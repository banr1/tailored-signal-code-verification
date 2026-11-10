/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted

/-!
# Arm64

Top-level umbrella module for the trusted specification vocabulary, re-exporting four layers
via `Arm64.Trusted`:

1. `Arm64/Trusted/ISA/` and `Arm64/Trusted/Syscalls/`: AArch64 instruction syntax (`Syntax`),
   binary decoder (`Decode`), byte-addressable virtual memory (`Memory`), machine state (`State`),
   IEEE-754 floats (`Float`), instruction evaluator (`Eval`), Linux AArch64 syscalls (`Syscalls`),
   and small-step operational semantics (`Semantics`: `Step` and `Steps`).
2. `Arm64/Trusted/Object/`: relocations (`Reloc`) and layout-generic placement (`Placed`).
3. `Arm64/Trusted/Spec/`: ASCII decimal integer formatting and parsing (`AsciiNum`), Rust ABI and
   panic runtime (`RustAbi`, `RustRuntime`), separation logic (`SepLogic`), framed Hoare triples
   and subroutine-to-hook primitives (`Hoare`), and placed contracts (`Placed`).
4. `Arm64/Trusted/Surface/`: surface specification DSLs and literal macros (`c_spec` and
   `rust_spec` in `Surface/Abi.lean`, `c_type_spec` in `Surface/CType.lean`, `hex_words%` and
   `Program.ofHex` in `Surface/HexCode.lean`, and `ascii!` / `asciic!` / `asciiCode!` in
   `Surface/Ascii.lean`). `Arm64.Trusted.Surface.IncludeBytes` and `Arm64.Trusted.Process` are
   imported separately by object and whole-binary specifications.
-/

@[expose] public section
