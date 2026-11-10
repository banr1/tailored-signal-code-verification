/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmBytesTR
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmBytesPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Bytes Arms Under `LibsignalCodeRoLoaded`

Composes the placed bytes decode arms with `bytes_merge_6_placed_ok_w_cro` to prove
`OverDecArmCroPlacedAtTR ext OverDecBytesField` from `HookSat` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH
open CryptoVerification.E2E.Record (A0)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed

/-- `LibsignalCodeRoLoaded` bytes decode arms (`OverDecArmCroPlacedAtTR ext OverDecBytesField`)
discharged from `HookSat`. -/
theorem overDecArm_bytes_cro_placed_of_hooks [LibsignalPlacement]
    {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat ext lsRustAllocSym (rustAllocSpec A0))
    (hrealloc : HookSat ext lsRustReallocSym (rustReallocSpec A0))
    (hdealloc : HookSat ext lsRustDeallocSym (rustDeallocSpec A0))
    (hmc : HookSat ext lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : ext lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    OverDecArmCroPlacedAtTR ext OverDecBytesField :=
  fun s0 s g v fl rest hP hok _hfr hsuf hlen ⟨hcro, hregs⟩ hx0 _hx22 =>
    overDecArm_bytes_cro_placed_ext_of_bm6w ext
      (bytes_merge_6_placed_ok_w_cro hshim halloc hrealloc hdealloc hmc hpanic_alloc hpanic_raw)
      s0 s g v fl rest hP hok hsuf hlen hcro hregs hx0

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
