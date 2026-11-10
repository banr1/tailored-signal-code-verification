/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public meta import Lean.Elab.Command

/-!
# Tests for `collectTableOffsets` Memoization

Verifies that `collectTableOffsets` caches closed symbol/stub tables built exclusively from
imported constants in `tableOffsetsMemoRef`, skips caching tables referencing local module
constants, and respects `proofLib.tableOffsetsMemo = false`.
-/

@[expose] public section

namespace ProofLib.Testing.TableOffsetsMemo

open Lean Elab Command Meta

/-- A symbol table defined in this (non-imported) module. -/
def widgetSyms : List (String × Nat) := [("alpha", 4), ("beta", 12)]

/-- `table_offsets t`: collect `t`'s offsets twice and report them and whether `t` was recorded. -/
elab "table_offsets " t:term : command => liftTermElabM do
  let tbl ← instantiateMVars (← Term.elabTerm t (some (toTypeExpr (List (String × Nat)))))
  let offs ← ProofLib.collectTableOffsets tbl
  let offs' ← ProofLib.collectTableOffsets tbl
  let recorded := (← ProofLib.tableOffsetsMemoRef.get).contains tbl
  logInfo m!"offsets {offs} (repeat equal: {offs == offs'}), recorded: {recorded}"

/-- info: offsets [32, 12, 4] (repeat equal: true), recorded: true -/
#guard_msgs in
table_offsets [("alpha", 4), ("beta", 12), ("gamma", 32)]

/-- info: offsets [12, 4] (repeat equal: true), recorded: false -/
#guard_msgs in
table_offsets widgetSyms

/-- info: offsets [16, 8] (repeat equal: true), recorded: false -/
#guard_msgs in
set_option proofLib.tableOffsetsMemo false in
table_offsets [("delta", 8), ("epsilon", 16)]

end ProofLib.Testing.TableOffsetsMemo
