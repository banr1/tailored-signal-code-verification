/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Disproof.Basic
public import ProofLib.Disproof.StrictHook
public import ProofLib.Disproof.FaultWP
public import ProofLib.Disproof.ModelBuilder
import Arm64.Trusted.Spec.SepLogic

/-!
# Machine-Code Disproof Infrastructure

Re-exports the counterexample and refutation modules for `Arm64.Steps` and `subroutine_ok`:
- `ProofLib.Disproof.Basic`: terminal-state determinism and refutation lemmas via exceptions,
  falsified postconditions, or corrupted frame canaries.
- `ProofLib.Disproof.StrictHook`: defensive extern hook wrappers (`strictHook`, `oomAllocator`,
  `strictMemcpyRegionHook`) raising `.Exception` outside callee preconditions.
- `ProofLib.Disproof.FaultWP`: `ReachesException` reachability and single-step fault introduction.
- `ProofLib.Disproof.ModelBuilder`: decidable sparse memory and state builders (`DisproofRegion`,
  `buildDisproofMem`, `mkDisproofState`).
-/

@[expose] public section
