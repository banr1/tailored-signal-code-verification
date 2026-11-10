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
# Simp Set for Width Round-Trip Normalization

Registers the opt-in `width_norm` simp attribute for `setWidth`/`truncate`/`zeroExtend`
round-trip, shift-mask, and comparison lemmas in `ProofLib.BV.WidthNorm`. Kept separate from
`wp_norm` and `arm64_norm` so default normal forms stay unchanged; invoke via
`simp only [wp_norm, width_norm]`.
-/

@[expose] public section

/-- Opt-in width round-trip normalization; see `ProofLib.BV.WidthNorm`. -/
register_simp_attr width_norm
