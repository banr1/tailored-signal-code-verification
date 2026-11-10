/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b

/-! # `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Wrapper for `Variant1b` -/

@[expose] public section
set_option autoImplicit false
namespace CryptoVerification.SpqrV1.States.FromPb
open Arm64 ProofLib CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc

theorem Ext4K.states_from_pb_keysUnsampled_156 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) (s0 s1 : State) (out pbA : BitVec 64)
    (s : V1State.Chunked.KeysUnsampled) (R : SepProp) (ha : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 156#64) (hr : s1.status = .Running)
    (hsp : s1.sp = s0.sp - 2400#64) (hx19 : s1.readReg64 .x19 = out) (hx23 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27 : s1.readReg64 .x27 = pbA) (htr : TraceCalleeSaved s1 s0) : StatesFromPbKeysUnsampled156Goal A F b ext s0 s1 out pbA s R :=
  states_from_pb_keysUnsampled_156_sfa (.of_4k hA) s0 s1 out pbA s R ha hpc hr hsp hx19 hx23 hx27 htr

end CryptoVerification.SpqrV1.States.FromPb
