/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.ProofTerm.KernelProfile
public import ProofLib.ProofTerm.Lint
public import ProofLib.ProofTerm.KFold
public import ProofLib.ProofTerm.ClearDead
import Arm64.Trusted.Spec.SepLogic

/-!
# Proof-Term Profiling and Kernel-Cost Control

Umbrella module re-exporting `#kernel_profile`, `#kernel_hotspots`, `#kernel_lint`, `kfold`,
and `clear_dead` for measuring kernel type-checking cost, flagging unfolding of `@[kernel_heavy]`
definitions, binding repeated subterms, and clearing unused hypotheses.
-/
