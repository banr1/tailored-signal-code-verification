/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

-- Layer 1 (`Arm64/Trusted/ISA/`): instruction-level AArch64 semantics
module

public import Arm64.Trusted.ISA.Syntax
public import Arm64.Trusted.ISA.Decode
public import Arm64.Trusted.ISA.Memory
public import Arm64.Trusted.ISA.State
public import Arm64.Trusted.ISA.Float
public import Arm64.Trusted.ISA.Eval
public import Arm64.Trusted.Syscalls
public import Arm64.Trusted.ISA.Semantics

-- Layer 2 (`Arm64/Trusted/Object/`): relocatable ELF object relocations, placement, and pre-link label provenance
public import Arm64.Trusted.Object.Reloc
public import Arm64.Trusted.Object.Placed
public import Arm64.Trusted.Object.Labels

-- Layer 3 (`Arm64/Trusted/Spec/`): `Init`-only machine-level specification foundation
public import Arm64.Trusted.Spec.AsciiNum
public import Arm64.Trusted.Spec.RustAbi
public import Arm64.Trusted.Spec.RustRuntime
public import Arm64.Trusted.Spec.SepLogic
public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.Placed

-- Layer 4 (`Arm64/Trusted/Surface/`): surface specification DSLs and literal macros
public import Arm64.Trusted.Surface.Abi
public import Arm64.Trusted.Surface.CType
public import Arm64.Trusted.Surface.HexCode
public import Arm64.Trusted.Surface.Ascii

/-!
# Trusted Computing Base

Umbrella module re-exporting the trusted AArch64 ISA semantics (`Arm64/Trusted/ISA/`), Linux
syscall interface (`Arm64/Trusted/Syscalls/`), ELF object relocation and placement model
(`Arm64/Trusted/Object/`), machine-level specification foundation (`Arm64/Trusted/Spec/`), and
surface specification macros (`Arm64/Trusted/Surface/`). Process-image byte loaders
(`IncludeBytes`, `FileBytes`) are imported via `Arm64.Trusted.Process`, and heap/allocator models
(`RustHeap`, `GlobalAlloc`) are imported directly by the specifications that use them.
-/

@[expose] public section
