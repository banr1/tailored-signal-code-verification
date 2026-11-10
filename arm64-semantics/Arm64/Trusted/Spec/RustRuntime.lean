/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.ISA.Semantics

/-!
# Rust Runtime Panic Hooks

Models Rust `panic = abort` entry points by wrapping a `Program` hook table (`Rust.withPanics`)
so calls to `core::panicking::*`, `unwrap`/`expect` failure paths, slice bounds checks, and
allocation error handlers transition `s.status` to `.Panicked`.
-/

@[expose] public section

namespace Arm64.Rust

/-- Demangled names of functions that start a panic. Everything in `core::panicking` panics;
    the others are the out-of-line panic paths of `unwrap`/`expect`, slice indexing, and
    allocation failure. -/
def isPanicSymbol (name : String) : Bool :=
  name.startsWith "core::panicking::" ||
  [ "core::result::unwrap_failed",
    "core::option::unwrap_failed",
    "core::option::expect_failed",
    "core::slice::index::slice_start_index_len_fail",
    "core::slice::index::slice_end_index_len_fail",
    "core::slice::index::slice_index_order_fail",
    "core::slice::index::slice_index_fail",
    "alloc::raw_vec::handle_error",
    "alloc::raw_vec::capacity_overflow",
    "alloc::alloc::handle_alloc_error" ].contains name

/-- The effect of entering a panic. -/
def panicked (s : State) : State :=
  { s with status := .Panicked }

/-- `hooks`, with every panic function (`isPanicSymbol`) mapped to `panicked`. -/
def withPanics (hooks : String → Option (State → State) := fun _ => none) :
    String → Option (State → State) :=
  fun name => if isPanicSymbol name then some panicked else hooks name

end Arm64.Rust
