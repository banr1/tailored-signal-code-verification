/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.BV.Attr
public import ProofLib.BV.Linear
public import ProofLib.BV.Arith
public import ProofLib.BV.MaskLemmas
public import ProofLib.BV.BitsAttr
public import ProofLib.BV.Bits
public import ProofLib.BV.WidthNorm
public import ProofLib.BV.ReflectROBDD
public import ProofLib.BV.PolyMul
import Arm64.Trusted.Spec.SepLogic

/-!
# Bitvector and Arithmetic Decision Procedures

Re-exports the kernel-checked `BitVec` normalizers and decision procedures (`bv_lin`, `bv_arith`,
`bv_solve`, `bv_bits`, `bv_slice`, `bv_robdd`, and width-polymorphic mask and alignment lemmas)
without importing their regression test modules. See `ProofLib/BV/README.md` for solver selection.
-/

@[expose] public section
