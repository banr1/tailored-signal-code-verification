/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.HeapDefs
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Defs
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX -- shake: keep

/-!
# `<Vec<Vec<u8>> as Clone>::clone` Specification on 1 Element

Defines the stack bound `vecVecClone1StackX`, ghost input `VecVecClone1Ghost`, specification
`vecVecClone1SpecX`, and subroutine contract `VecVecClone1OkStmt` for `<Vec<Vec<u8>> as Clone>::clone`
(`<[Vec<u8>]>::to_vec`) when `x2 = 1`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record.Serialization
open Proofs.libsignal.Hooks2

/-- Stack budget of `Vec<Vec<u8>>::clone` on `len = 1`: `0x60` frame plus `extHookStack`. -/
abbrev vecVecClone1StackX : Nat := 0x60 + Proofs.libsignal.Stage1X.extHookStack

/-- Ghost parameters for `Vec<Vec<u8>>::clone` on `len = 1`: destination header `dst` (`x0`), source
slice `src` (`x1`), and element bytes `enc`. -/
structure VecVecClone1Ghost where
  dst : BitVec 64
  src : BitVec 64
  enc : List (BitVec 8)

/-- Specification of `<Vec<Vec<u8>> as Clone>::clone` on `len = 1` (`x2 = 1`): writes at `dst` a
fresh capacity-1 `Vec<Vec<u8>>` holding a copy of `enc` while preserving the source element. -/
def vecVecClone1SpecX (A : RustAlloc) : Spec VecVecClone1Ghost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧ s.readReg64 .x2 = 1#64⌝ ∗
      arrayAt (prevElem A) 24 x.src [x.enc] ∗ memRegion x.dst 24 ∗ A.pool ∗
      stackAt s.sp vecVecClone1StackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ arrayAt (prevElem A) 24 x.src [x.enc] ∗
      (∃∗ q' : BitVec 64, prevVecAt A x.dst 1#64 q' [x.enc]) ∗ A.pool ∗
      stackAt s0.sp vecVecClone1StackX
  onPanic := allocPanic

/-- Subroutine contract stating that `Vec<Vec<u8>>::clone` satisfies `vecVecClone1SpecX A` on
`SP2Ext img.base ext`. -/
def VecVecClone1OkStmt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr vecVecCloneName)
    ((vecVecClone1SpecX A).inImage img)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
