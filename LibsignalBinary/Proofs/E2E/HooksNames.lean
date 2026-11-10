/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import ProofLib.BV.ArithCore

/-!
# E2E External Stub Symbol Names

External stub symbol-name abbreviations and `List.lookup` helper shared across E2E hook and binary
proof modules.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

/-! ## Stub names the session program does not handle -/

/-- `<SystemTime as Add<Duration>>::add` (stub `0x6ef34`). -/
abbrev timeAddName : String :=
  "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add"
/-- `SystemTime::duration_since` (stub `0x6ef2c`). -/
abbrev durationSinceName : String := "<std::time::SystemTime>::duration_since"
/-- `<String as Clone>::clone` (stub `0x6eed0`). -/
abbrev stringCloneName : String := "<alloc::string::String as core::clone::Clone>::clone"
/-- `bcmp(a = x0, b = x1, n = x2) -> int` (stub `0x6eec8`; hook `bcmpHook`). -/
abbrev bcmpName : String := "bcmp"
/-- `std::sys::random::linux::hashmap_random_keys() -> (u64, u64)` (stub `0x6eeb4`). -/
abbrev randomKeysName : String := "std::sys::random::linux::hashmap_random_keys"
/-- hashbrown's `Fallibility::capacity_overflow` of the copy the in-memory stores use (stub
`0x6ee8c`). Every reached caller passes `Infallible`, so it panics. -/
abbrev capOverflowName : String := "<hashbrown::raw::Fallibility>::capacity_overflow#1"
/-- hashbrown's `Fallibility::alloc_err`, same copy (stub `0x6ee94`); panics as above. -/
abbrev allocErrName : String := "<hashbrown::raw::Fallibility>::alloc_err#1"

/-! ## Allocator stub names (written as literals in `sessionExterns`) -/

/-- `__rust_alloc` (stub `0x6ee64`). -/
abbrev rustAllocName : String := "__rustc::__rust_alloc"
/-- `__rust_dealloc` (stub `0x6ee70`). -/
abbrev rustDeallocName : String := "__rustc::__rust_dealloc"
/-- `__rust_realloc` (stub `0x6eee0`). -/
abbrev rustReallocName : String := "__rustc::__rust_realloc"


theorem lookup_none {β : Type} (l : List (String × β)) (s : String)
    (h : s ∉ l.map Prod.fst) : l.lookup s = none := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hk : (s == k) = false := by simpa using h.1
    simp only [List.lookup, hk]
    exact ih h.2


end CryptoVerification.E2E
