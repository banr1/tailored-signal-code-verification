/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Surface.IncludeBytes

/-!
# Unit Tests for `include_bytes%`

Tests that `include_bytes% "IncludeBytes.fixture" off len` splices exact byte slices (including
empty slices) and rejects out-of-bounds slices.
-/

@[expose] public section

namespace Testing.IncludeBytes

example : include_bytes% "IncludeBytes.fixture" 0 3 = [0x30#8, 0x31#8, 0x32#8] := rfl
example : include_bytes% "IncludeBytes.fixture" 8 3 = [0x38#8, 0x39#8, 0x0a#8] := rfl
example : include_bytes% "IncludeBytes.fixture" 11 0 = [] := rfl

/-- error: include_bytes%: -/
#guard_msgs (substring := true) in
example : include_bytes% "IncludeBytes.fixture" 9 3 = [] := rfl

end Testing.IncludeBytes
