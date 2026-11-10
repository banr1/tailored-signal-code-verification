/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean

/-!
# `[addr_norm]` and `[wp_branch]` Simp Attributes

Registers the `addr_norm` simp set for canonicalizing chained `BitVec.ofNat` pointer offsets and
the `wp_branch` simp set for normalizing branch conditions and width-extension comparisons.
-/

/-- Simp set normalizing chained symbolic/literal `BitVec.ofNat` pointer offsets and width extensions. -/
register_simp_attr addr_norm

/-- Simp set normalizing branch conditions and zero/sign extension comparisons across case splits. -/
register_simp_attr wp_branch
