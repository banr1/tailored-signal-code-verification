/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Arm64.Trusted.ISA.Syntax
public import Arm64.Trusted.ISA.State
public meta import Lean
public meta import Arm64.Trusted.ISA.Syntax
public meta import Arm64.Trusted.ISA.State

/-!
# `Lean.ToExpr` Instances for AArch64 Syntax and Trace Types

Derives `Lean.ToExpr` instances for `Arm64.Trusted.ISA.Syntax` instruction types and
`Arm64.Trusted.ISA.State` trace types so tactics and commands can reflect decoded instructions.
-/

@[expose] public section

namespace Arm64

deriving instance Lean.ToExpr for RegWidth
deriving instance Lean.ToExpr for MemWidth
deriving instance Lean.ToExpr for CondCode
deriving instance Lean.ToExpr for ShiftType
deriving instance Lean.ToExpr for ExtendType
deriving instance Lean.ToExpr for Reg
deriving instance Lean.ToExpr for SimdMemSize
deriving instance Lean.ToExpr for AddrMode
deriving instance Lean.ToExpr for AddSubOp
deriving instance Lean.ToExpr for LogicalOp
deriving instance Lean.ToExpr for MoveWideOp
deriving instance Lean.ToExpr for BitfieldOp
deriving instance Lean.ToExpr for CondSelectOp
deriving instance Lean.ToExpr for DataProc1Op
deriving instance Lean.ToExpr for DataProc2Op
deriving instance Lean.ToExpr for DataProc3Op
deriving instance Lean.ToExpr for AtomicOp
deriving instance Lean.ToExpr for AesOp
deriving instance Lean.ToExpr for Instr
deriving instance Lean.ToExpr for OutputStream
deriving instance Lean.ToExpr for TraceEvent

end Arm64
