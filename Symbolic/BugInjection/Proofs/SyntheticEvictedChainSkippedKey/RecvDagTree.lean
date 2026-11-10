/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

/-!
# Low-Bit-First Binary Tree

Defines `BinTree` and low-bit-first lookup `btGet` for bounded-depth `Nat`-keyed maps.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagTree

inductive BinTree (α : Type) where
  | empty : BinTree α
  | leaf : α → BinTree α
  | branch : BinTree α → BinTree α → BinTree α

/-- Looks up key `k` in `tr` with fuel `d`, branching on bits of `k` from least significant up. -/
def btGet {α : Type} (d : Nat) (tr : BinTree α) (k : Nat) : Option α :=
  match tr with
  | .empty => none
  | .leaf v => some v
  | .branch lo hi =>
    match d with
    | 0 => none
    | d' + 1 =>
      if Nat.beq (k % 2) 0 then btGet d' lo (k / 2) else btGet d' hi (k / 2)

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagTree
