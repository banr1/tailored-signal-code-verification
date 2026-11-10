/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Spec.Top
public import VerifiedLibraries.Mallocng.Spec.Cost

/-!
# Stock `musl` 1.2.5 `mallocng` Public Specification

Re-exports [`VerifiedLibraries.Mallocng.Spec.Top`](Spec/Top.lean) (public contracts for stock
`musl` 1.2.5 `mallocng` and the Rust `std` `__rdl_*` global-allocator shims) and
[`VerifiedLibraries.Mallocng.Spec.Cost`](Spec/Cost.lean) (cost-model-indexed C entry-point
contracts).
-/
