/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.RustHeap.Vec
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.ToDual
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.SepLogic.WPp
import VCVio.Prelude.Core

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.DecryptPq

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem arrayAt_nil {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat) (p : BitVec 64) :
    arrayAt elem stride p [] = emp := rfl

theorem arrayAt_cons {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat) (p : BitVec 64)
    (x : α) (xs : List α) :
    arrayAt elem stride p (x :: xs) =
    (elem x p ∗ arrayAt elem stride (p + BitVec.ofNat 64 stride) xs) := rfl

theorem bv_ofNat_succ_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  bv_omega

theorem bv_ofNat_succ_succ_bne_one {n : Nat} (hlt : (n + 1 + 1) * 104 < 2 ^ 63) :
    (BitVec.ofNat 64 (n + 1 + 1) != 1#64) = true := by
  rw [bne_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change n + 1 + 1 = 1 at ht
  omega

theorem bv_ofNat_succ_beq_zero {n : Nat} (hlt : (n + 1) * 104 < 2 ^ 63) :
    (BitVec.ofNat 64 (n + 1) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change n + 1 = 0 at ht
  omega

theorem sp_sub_1504_add_0x38 (sp0 : BitVec 64) :
    sp0 - 1504#64 + 0x38#64 = sp0 - 1448#64 := by bv_omega

theorem sp_sub_1504_add_0xe8 (sp0 : BitVec 64) :
    sp0 - 1504#64 + 0xe8#64 = sp0 - 1272#64 := by bv_omega

theorem sp_sub_1504_add_0xf0 (sp0 : BitVec 64) :
    sp0 - 1504#64 + 0xf0#64 = sp0 - 1264#64 := by bv_omega

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
