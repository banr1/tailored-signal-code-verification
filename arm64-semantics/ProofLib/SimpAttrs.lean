/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
import Arm64.Trusted.Spec.SepLogic

/-!
# Normalization `simp` Attributes

Declares the `arm64_norm`, `wp_norm`, `callee_saved_split`, and `wp_unfold` `simp` attributes
used across `ProofLib` symbolic execution and calling-convention automation.
-/

@[expose] public section

/-- Simp attribute for ARM64 symbolic execution and state normalization rules. -/
register_simp_attr arm64_norm

/-- Simp attribute for `SepWP` state-spine canonicalization and instruction-stepping rules. -/
register_simp_attr wp_norm

/-- Simp attribute unpacking `CalleeSavedPreserved` and `CallingConventionPreserved` into
    per-register read equalities (`X19..X28`, `FP`, and `SP`). -/
register_simp_attr callee_saved_split

/-- Simp attribute marking rebased `Program` wrappers (`declare_rebased_program`) for automatic
    unfolding at subroutine proof entry (`wp_init` / `wp_start` / `wpp_init`). -/
register_simp_attr wp_unfold

end
