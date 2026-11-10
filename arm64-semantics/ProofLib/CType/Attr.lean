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
# `ctype_simp` Simp Attribute

Registers the `ctype_simp` simp attribute used by `ProofLib.CType` to unfold built-in
`Arm64.CType` semantic types (defined in a separate module so Lean can apply it downstream).
-/

@[expose] public section

/-- Simp set unfolding the built-in `Arm64.CType` semantic types. -/
register_simp_attr ctype_simp
