/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Coins.Defs
public import LibsignalBinary.Proofs.SignalSession.Coins.Fill.Helpers

/-!
# Fixed-Placement Proof of `signal_session_coins_fill`

Proves `coinsFill_ok` and `coinsFill_ok_at`: `signal_session_coins_fill` on
`tripleRatchetProgAtExt b ext` satisfies `coinsFillSpec b stk` for `0x50 ≤ stk`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Coins

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

/-- `signal_session_coins_fill` meets `coinsFillSpec b stk`. -/
theorem coinsFill_ok {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (stk : Nat) (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr coinsFillName) (coinsFillSpec b stk) :=
  Helpers.coinsFill_ok_proof hA hb stk hstk hstk'

/-- `coinsFill_ok` at a call site `fnAddr name + k` with `fnOff name + k = fnOff coinsFillName`. -/
theorem coinsFill_ok_at {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (stk : Nat) (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff coinsFillName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (coinsFillSpec b stk) :=
  sub_ok_at_of_fnAddr (coinsFill_ok hA hb stk hstk hstk') name k hk

end CryptoVerification.SignalSession.Coins
