/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDerive

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.TopLevel
open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.Initiator

structure SetUnackExactGhost where
  statePtr     : BitVec 64
  optOpkTag    : BitVec 32
  optOpkVal    : BitVec 32
  spkId        : BitVec 32
  baseKeyPtr   : BitVec 64
  baseKeyBytes : Initiator.Bytes


def durationSinceZeroTsSpec : Spec (BitVec 64 × BitVec 64) where
  pre := fun (p, ret) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret⌝ ∗
      memRegion p 16 ∗ memRegion ret 24 ∗ stackAt s.sp extHookStack
  post := fun (p, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion p 16 ∗
      ((∃∗ w2 : BitVec 64, ∃∗ w0 : BitVec 64,
        (ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗ ((ret + 16#64) ↦₆₄ w2))) ∗
      stackAt s0.sp extHookStack

theorem bv_add_neg_8 (x : BitVec 64) : x + 18446744073709551608#64 = x - 8#64 := by bv_lin
theorem bv_add_neg_16 (x : BitVec 64) : x + 18446744073709551600#64 = x - 16#64 := by bv_lin
theorem bv_add_neg_32 (x : BitVec 64) : x + 18446744073709551584#64 = x - 32#64 := by bv_lin
theorem bv_add_neg_36 (x : BitVec 64) : x + 18446744073709551580#64 = x - 36#64 := by bv_lin
theorem bv_add_neg_0x60 (x : BitVec 64) : x + 18446744073709551520#64 = x - 96#64 := by bv_lin
theorem bv_add_neg_728 (x : BitVec 64) : x + 18446744073709550888#64 = x - 728#64 := by bv_lin
theorem bv_add_neg_828 (x : BitVec 64) : x + 18446744073709550788#64 = x - 828#64 := by bv_lin
theorem bv_add_neg_864 (x : BitVec 64) : x + 18446744073709550752#64 = x - 864#64 := by bv_lin
theorem bv_add_neg_904 (x : BitVec 64) : x + 18446744073709550712#64 = x - 904#64 := by bv_lin
theorem bv_add_neg_944 (x : BitVec 64) : x + 18446744073709550672#64 = x - 944#64 := by bv_lin
theorem bv_add_neg_1000 (x : BitVec 64) : x + 18446744073709550616#64 = x - 1000#64 := by bv_lin
theorem bv_add_neg_1032 (x : BitVec 64) : x + 18446744073709550584#64 = x - 1032#64 := by bv_lin
theorem bv_add_neg_1048 (x : BitVec 64) : x + 18446744073709550568#64 = x - 1048#64 := by bv_lin
theorem bv_add_neg_1056 (x : BitVec 64) : x + 18446744073709550560#64 = x - 1056#64 := by bv_lin
theorem bv_add_neg_1068 (x : BitVec 64) : x + 18446744073709550548#64 = x - 1068#64 := by bv_lin
theorem bv_add_neg_1072 (x : BitVec 64) : x + 18446744073709550544#64 = x - 1072#64 := by bv_lin
theorem bv_add_neg_1116 (x : BitVec 64) : x + 18446744073709550500#64 = x - 1116#64 := by bv_lin
theorem bv_add_neg_1144 (x : BitVec 64) : x + 18446744073709550472#64 = x - 1144#64 := by bv_lin
theorem bv_add_neg_1444 (x : BitVec 64) : x + 18446744073709550172#64 = x - 1444#64 := by bv_lin
theorem bv_add_neg_2088 (x : BitVec 64) : x + 18446744073709549528#64 = x - 2088#64 := by bv_lin
theorem bv_add_neg_2108 (x : BitVec 64) : x + 18446744073709549508#64 = x - 2108#64 := by bv_lin
theorem bv_add_neg_2132 (x : BitVec 64) : x + 18446744073709549484#64 = x - 2132#64 := by bv_lin
theorem bv_add_neg_2400 (x : BitVec 64) : x + 18446744073709549216#64 = x - 2400#64 := by bv_lin
theorem bv_add_neg_2536 (x : BitVec 64) : x + 18446744073709549080#64 = x - 2536#64 := by bv_lin
theorem bv_add_neg_2684 (x : BitVec 64) : x + 18446744073709548932#64 = x - 2684#64 := by bv_lin
theorem bv_add_neg_0xb20 (x : BitVec 64) : x + 18446744073709548768#64 = x - 2848#64 := by bv_lin
theorem bv_add_neg_3032 (x : BitVec 64) : x + 18446744073709548584#64 = x - 3032#64 := by bv_lin
theorem bv_add_bl_0x123d0 (x : BitVec 64) :
    x + 2848#64 + 18446744073709135752#64 = x + 18446744073709138600#64 := by bv_lin
theorem bv_add_bl_0x17490 (x : BitVec 64) :
    x + 3128#64 + 18446744073709156144#64 = x + 18446744073709159272#64 := by bv_lin
theorem bv_add_bl_0x49e80 (x : BitVec 64) :
    x + 3288#64 + 18446744073709522876#64 = x + 18446744073709526164#64 := by bv_lin

end CryptoVerification.E2E.Pqxdh.TopLevel
