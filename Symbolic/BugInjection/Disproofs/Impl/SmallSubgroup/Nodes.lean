/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge
public import GeneratedLean.BugInjectionMutant
-- `#guard` evaluates at compile time, so it needs the mutant's constants at the meta stage too.
public meta import GeneratedLean.BugInjectionMutant

/-!
Machine-free specification premise (`spec_half_pinned`) of the placed security disproof for the
`Cheval26SmallSubgroupHighBitCli` witness under `cheval26-small-subgroup`. The companion placed
implementation half is `NodesPlaced.impl_half_bytes_placed`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Nodes

open Symbolic.BugInjection (cliCompShape)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (cliCompFitsPinned)

#guard CryptoVerification.BugInjection.mutant == "cheval26-small-subgroup"

/-- `Cheval26SmallSubgroupHighBitCli.trace` admits no valid symbolic explanation under any
interpretation and record state permitted by `cliCompFitsPinned setup`. -/
theorem spec_half_pinned :
    cliCompShape.SpecHalf
      (cliCompFitsPinned Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.setup)
      Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.trace :=
  Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge.spec_half_pinned

end Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Nodes
