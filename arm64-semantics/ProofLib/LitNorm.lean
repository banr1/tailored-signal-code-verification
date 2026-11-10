/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.VCGen
import Arm64.Trusted.Spec.SepLogic

/-!
# Ground-Literal Folding Simprocs for `wp_norm`

Definitional `dsimproc`s registered in `[wp_norm]` (and intentionally excluded from `arm64_norm`)
that fold `BitVec.ult`, `==`, `BitVec.toNat`, and `BitVec`/`Nat` `*` when every argument is a
ground literal recognized by `ProofLib.evalBitVecLit?` or `ProofLib.evalNatLit?` (including nested
ground arithmetic, `Program.fnAddr`, and `Nat` `abbrev` constants). Note that inside `simp`, a
`def` or `abbrev` constant of type `BitVec w` is not unfolded because reducible `whnf` stops at
`Fin.Internal.ofNat`.
-/

public meta section

namespace ProofLib

open Lean Meta

attribute [wp_norm] reduceHShiftLeft reduceHShiftRight

@[inline] private def isBitVecTy (ty : Expr) : Bool := ty.consumeMData.isAppOfArity ``BitVec 1

/-- Fold `BitVec.ult a b` when `a` and `b` are ground literals of the same width. -/
dsimproc [wp_norm] reduceBitVecUlt (BitVec.ult _ _) := fun e => do
  unless e.isAppOfArity ``BitVec.ult 3 do return .continue
  let some (w1, v1) ← evalBitVecLit? (e.getArg! 1) | return .continue
  let some (w2, v2) ← evalBitVecLit? (e.getArg! 2) | return .continue
  if w1 != w2 then return .continue
  return .done (toExpr (decide (v1 < v2)))

/-- Fold `a == b` on ground `BitVec w` literals of the same width. -/
dsimproc [wp_norm] reduceBitVecBeq (_ == _) := fun e => do
  unless e.isAppOfArity ``BEq.beq 4 && isBitVecTy (e.getArg! 0) do return .continue
  let some (w1, v1) ← evalBitVecLit? (e.getArg! 2) | return .continue
  let some (w2, v2) ← evalBitVecLit? (e.getArg! 3) | return .continue
  if w1 != w2 then return .continue
  return .done (toExpr (v1 == v2))

/-- Fold `BitVec.toNat a` to a `Nat` numeral when `a` is a ground literal. -/
dsimproc [wp_norm] reduceBitVecToNatLit (BitVec.toNat _) := fun e => do
  unless e.isAppOfArity ``BitVec.toNat 2 do return .continue
  let some (_, v) ← evalBitVecLit? (e.getArg! 1) | return .continue
  return .done (toExpr v)

/-- Fold `a * b` on ground `BitVec w` literals of the same width. -/
dsimproc [wp_norm] reduceBitVecMul (_ * _) := fun e => do
  unless e.isAppOfArity ``HMul.hMul 6 && isBitVecTy (e.getArg! 0) do return .continue
  let some (w1, v1) ← evalBitVecLit? (e.getArg! 4) | return .continue
  let some (w2, v2) ← evalBitVecLit? (e.getArg! 5) | return .continue
  if w1 != w2 then return .continue
  return .done (mkCanonBitVecLit w1 (v1 * v2))

/-- Fold `a * b` on ground `Nat` expressions (both factors must evaluate to literals). -/
dsimproc [wp_norm] reduceNatMulLit (_ * _) := fun e => do
  unless e.isAppOfArity ``HMul.hMul 6 && (e.getArg! 0).consumeMData.isConstOf ``Nat do return .continue
  let some v1 ← evalNatLit? (e.getArg! 4) | return .continue
  let some v2 ← evalNatLit? (e.getArg! 5) | return .continue
  return .done (toExpr (v1 * v2))

end ProofLib
