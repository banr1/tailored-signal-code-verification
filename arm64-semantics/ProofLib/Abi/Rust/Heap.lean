/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Abi.Rust.Heap.Alloc
public import ProofLib.Abi.Rust.Heap.Vec

/-!
# Rust Global Allocator and Heap Containers

Re-exports Rust global allocator contracts (`RustAlloc`, `ByteAlloc`, `LayoutOk`, and
`__rust_alloc` / `__rust_dealloc` / `__rust_realloc` specifications from
`ProofLib.Abi.Rust.Heap.Alloc`) together with separation-logic representations and structural
lemmas for `Vec<T>`, `Vec<u8>`, and `Box<[T]>` (`ProofLib.Abi.Rust.Heap.Vec`).
-/

@[expose] public section
