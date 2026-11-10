/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean

/-!
# Frame Transport Attribute

Declares the `@[frame_transport]` label attribute for state-indexed spatial atom transport lemmas
used by `wp_frame_transport`, `wp_call`, and `wpp_call`.
-/

@[expose] public section

/-- Label attribute for state-indexed spatial atom transport lemmas
    `forall ..., Rel s s' -> f ... s' = f ... s` consumed by `wp_frame_transport` (and by
    `wp_call` / `wpp_call` when `proofLib.wpCallFrameTransport` is enabled). -/
register_label_attr frame_transport

end
