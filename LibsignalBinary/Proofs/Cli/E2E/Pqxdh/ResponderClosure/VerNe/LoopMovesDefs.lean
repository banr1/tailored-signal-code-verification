/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopPeelDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K

/-!
# Previous-Session `memcpy` Chain Statements (`+0x2620 → +0x1fd4`)

Statement definitions `OverPrevMovesCliStmt4K` and `OverPrevMovesCliStmt` for the five 320-byte
`memcpy` transfers and `session_version` load (`w8 = 4#32` from `sp + 0xa78`) inside the CLI
responder closure.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib SepProp
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (AllocContractsMem4K)

/-- Five-step `memcpy` chain and version load (`+0x2620 → +0x1fd4`) under `AllocContractsMem4K`. -/
def OverPrevMovesCliStmt4K : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    AllocContractsMem4K img.base A ext →
    ∀ (s : State) (w0 w1 w2 u920 : BitVec 64) (r1 r2 : List (BitVec 8)),
      w0.toNat < 2 ^ 63 →
      r1.length = 304 →
      r2.length = 12 →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x2620#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x21 = s.sp + 0x930#64 →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1fd4#64) s
        (overPrevMovesSS (s.sp + 0x930#64) w0 w1 w2 r1 r2 ∗
         memRegion (s.sp + 0x560#64) 320 ∗
         memRegion (s.sp + 0x6a0#64) 320 ∗
         memRegion (s.sp + 0x7e0#64) 320 ∗
         ((s.sp + 0x920#64) ↦₆₄ u920) ∗
         stackAt s.sp allocHookStack)
        (fun sf P_f =>
          (P_f ⊢
            overPrevMovesSS (s.sp + 0x930#64) w0 w1 w2 r1 r2 ∗
            memRegion (s.sp + 0x560#64) 320 ∗
            memRegion (s.sp + 0x6a0#64) 320 ∗
            memRegion (s.sp + 0x7e0#64) 320 ∗
            ((s.sp + 0x920#64) ↦₆₄ s.readReg64 .x26) ∗
            stackAt s.sp allocHookStack) ∧
          sf.sp = s.sp ∧
          sf.trace = s.trace ∧
          sf.readReg64 .x8 = 4#64 ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x27 = s.readReg64 .x27 ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s)

/-- Copies the 320-byte tail of `overPrevMovesSS (s.sp + 0x930#64)` through scratch slots
`sp + 0x7e0`, `sp + 0x6a0`, `sp + 0x560`, `sp + 0x7e0`, and back to `sp + 0x948`, loads `w8 = 4`
from `sp + 0xa78`, and preserves `calleeSavedVRegs`. -/
def OverPrevMovesCliStmt : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    AllocContracts img.base A0 ext →
    ∀ (s : State) (w0 w1 w2 u920 : BitVec 64) (r1 r2 : List (BitVec 8)),
      w0.toNat < 2 ^ 63 →
      r1.length = 304 →
      r2.length = 12 →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x2620#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x21 = s.sp + 0x930#64 →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1fd4#64) s
        (overPrevMovesSS (s.sp + 0x930#64) w0 w1 w2 r1 r2 ∗
         memRegion (s.sp + 0x560#64) 320 ∗
         memRegion (s.sp + 0x6a0#64) 320 ∗
         memRegion (s.sp + 0x7e0#64) 320 ∗
         ((s.sp + 0x920#64) ↦₆₄ u920) ∗
         stackAt s.sp allocHookStack)
        (fun sf P_f =>
          (P_f ⊢
            overPrevMovesSS (s.sp + 0x930#64) w0 w1 w2 r1 r2 ∗
            memRegion (s.sp + 0x560#64) 320 ∗
            memRegion (s.sp + 0x6a0#64) 320 ∗
            memRegion (s.sp + 0x7e0#64) 320 ∗
            ((s.sp + 0x920#64) ↦₆₄ s.readReg64 .x26) ∗
            stackAt s.sp allocHookStack) ∧
          sf.sp = s.sp ∧
          sf.trace = s.trace ∧
          sf.readReg64 .x8 = 4#64 ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x27 = s.readReg64 .x27 ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
