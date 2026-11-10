/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopMovesDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.ConstsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopPeelDefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Previous-Session `memcpy` Chain Statement

Relocatable (`[LibsignalPlacement]`) statement `OverPrevMovesCliPlacedStmt`
(`(blkPl_518).base + 0x2620 → (blkPl_518).base + 0x1fd4`) on `lsProg_518`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib SepProp
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CliHandshake.RespClosurePlaced

/-- Relocatable `[LibsignalPlacement]` `memcpy` chain & version load
(`(blkPl_518).base + 0x2620 → (blkPl_518).base + 0x1fd4`) on `lsProg_518 ext`. -/
def OverPrevMovesCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ (ext : String → Option (State → State)),
    subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (sessionMemcpySpec allocHookStack) →
    ∀ (s : State) (w0 w1 w2 u920 : BitVec 64) (r1 r2 : List (BitVec 8)),
      w0.toNat < 2 ^ 63 →
      r1.length = 304 →
      r2.length = 12 →
      s.pc = (blkPl_518).base + 0x2620#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x21 = s.sp + 0x930#64 →
      SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1fd4#64) s
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
