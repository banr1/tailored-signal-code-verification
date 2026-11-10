/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64

/-!
# Sharded Code Lookup Fixture: Shard 0

Defines `widgetCode` and its shard-0 offset theorem. Companion offset and stub theorems reside in
`Arm64.Testing.Regression.CodeLookupShard12` to test cross-shard discovery in `ProofLib.CodeLookup`.
-/

@[expose] public section

namespace Testing.CodeLookupSharded

open Arm64

def widgetCode : Program :=
  { base := 0
    code := []
    symbols := [("widget_entry", 0), ("widget_far", 32)]
    stubs := [("widget_stub", 64)] }

theorem widgetCode_fnOff_0x0 : widgetCode.fnOff "widget_entry" = 0 := rfl

end Testing.CodeLookupSharded
