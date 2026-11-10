/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
import ProofLib.CoreLemmas

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Bin
open Arm64 ProofLib

section PreSimp

theorem sp_setPC_pre_send (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl
theorem sp_setMem_setPC_pre_send (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl
theorem readReg64_setPC_pre_send (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r
theorem readReg64_setMem_setPC_pre_send (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
theorem readReg32_setPC_pre_send (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl
theorem readReg32_setMem_setPC_pre_send (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl
theorem readReg_setPC_pre_send (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
theorem readReg_setMem_setPC_pre_send (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
theorem bv_add_neg_0x50 (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 := by bv_lin
theorem bv_add_neg_0x4f0 (x : BitVec 64) : x + bv% (2 ^ 64 - 1264) = x - 1264#64 := by bv_lin

end PreSimp

end CryptoVerification.E2E.Bin
