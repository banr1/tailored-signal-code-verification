/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Exists

/-!
# `SupportedOn` and `HoldsBytes` Bridge Regression Tests

Positive and `#guard_msgs` negative regression tests for `SupportedOn.of_holdsBytes_rw`,
`SupportedOn.of_holdsBytes_ro`, and `Satisfies.pointsToBytes_of_holdsBytes_rw` in
`ProofLib.SepLogic.Exists`.
-/

@[expose] public section

namespace Examples.Testing.SepSupportedOnTest

open Arm64 ProofLib

/-! ## Positive -/

/-- A writable 16-byte window at `b + 0x10` and a read-only 8-byte window at `b + 0x20` combine
    into one satisfied separating conjunction. -/
example {m : Memory} {b : BitVec 64} {ws rs : List (BitVec 8)}
    (hws : ws.length = 16) (hrs : rs.length = 8)
    (hw : Obj.HoldsBytes m (b + BitVec.ofNat 64 0x10) ws (fun _ => .rw))
    (hr : Obj.HoldsBytes m (b + BitVec.ofNat 64 0x20) rs (fun _ => .ro)) :
    m ⊨ ((b + BitVec.ofNat 64 0x10) ↦ₛ ws) ∗ ((b + BitVec.ofNat 64 0x20) ↦ᵣ rs) :=
  ((SupportedOn.of_holdsBytes_rw (by omega) hw).sepConj
    (SupportedOn.of_holdsBytes_ro (by omega) hr) (fun _ h₁ h₂ => by omega)).satisfies

/-- The footprint of a read-only window is exactly its relative interval. -/
example {m : Memory} {b : BitVec 64} {rs : List (BitVec 8)} (hrs : rs.length = 8)
    (hr : Obj.HoldsBytes m (b + BitVec.ofNat 64 0x20) rs (fun _ => .ro)) :
    SupportedOn b (fun k => 0x20 ≤ k ∧ k < 0x28) m ((b + BitVec.ofNat 64 0x20) ↦ᵣ rs) := by
  have h := SupportedOn.of_holdsBytes_ro (by omega) hr
  rwa [hrs] at h

/-- A read-write range that ends exactly at the top of the address space is still satisfiable. -/
example {m : Memory} {bs : List (BitVec 8)} (hbs : bs.length = 2)
    (h : Obj.HoldsBytes m (BitVec.ofNat 64 (2 ^ 64 - 2)) bs (fun _ => .rw)) :
    m ⊨ (BitVec.ofNat 64 (2 ^ 64 - 2) ↦ₛ bs) :=
  Satisfies.pointsToBytes_of_holdsBytes_rw (by rw [hbs]; decide) h

/-! ## Negative -/

/-- error: unsolved goals
m : Memory
b : BitVec 64
rs : List (BitVec 8)
hr : Obj.HoldsBytes m (b + BitVec.ofNat 64 (2 ^ 64 - 1)) rs fun x => Perm.ro
⊢ 2 ^ 64 - 1 + rs.length < 2 ^ 64 -/
#guard_msgs in
example {m : Memory} {b : BitVec 64} {rs : List (BitVec 8)}
    (hr : Obj.HoldsBytes m (b + BitVec.ofNat 64 (2 ^ 64 - 1)) rs (fun _ => .ro)) :
    SupportedOn b (fun k => 2 ^ 64 - 1 ≤ k ∧ k < 2 ^ 64 - 1 + rs.length) m
      ((b + BitVec.ofNat 64 (2 ^ 64 - 1)) ↦ᵣ rs) :=
  SupportedOn.of_holdsBytes_ro (by skip) hr

/-- error: unsolved goals
m : Memory
addr : BitVec 64
bs : List (BitVec 8)
h : Obj.HoldsBytes m addr bs fun x => Perm.rw
⊢ addr.toNat + bs.length ≤ 2 ^ 64 -/
#guard_msgs in
example {m : Memory} {addr : BitVec 64} {bs : List (BitVec 8)}
    (h : Obj.HoldsBytes m addr bs (fun _ => .rw)) : m ⊨ (addr ↦ₛ bs) :=
  Satisfies.pointsToBytes_of_holdsBytes_rw (by skip) h

/-- The bound is not vacuous: a 2-byte range starting at `2 ^ 64 - 1` wraps around. -/
example : ¬ ((BitVec.ofNat 64 (2 ^ 64 - 1)).toNat + 2 ≤ 2 ^ 64) := by decide

/-- A read-only `HoldsBytes` does not provide the writable `addr ↦ₛ bs`. -/
example {m : Memory} {addr : BitVec 64} {bs : List (BitVec 8)}
    (_hbnd : addr.toNat + bs.length ≤ 2 ^ 64)
    (_h : Obj.HoldsBytes m addr bs (fun _ => .ro)) : True := by
  fail_if_success have := Satisfies.pointsToBytes_of_holdsBytes_rw _hbnd _h
  trivial

end Examples.Testing.SepSupportedOnTest
