/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergePhase23W
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergePhase23Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Handshake `bytes::merge [local#5]` W-Mode Phases 2 and 3 Re-exports

Re-exports the unified `bytesMergeRawSpecXBoth` Phase 2 and Phase 3 lemmas on Block `514`
(`lsProg_514 H`), covering `x.bs.length < 2 ^ 62` without `BytesMergeCapOk`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

theorem mergePanicXBoth_eq_mergePanicXW (A : RustAlloc) (x : BytesMergeGhost)
    (s0 : State) (R : SepProp) :
    MergePanicXBoth A x s0 R = MergePanicXW A x s0 R := rfl

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
