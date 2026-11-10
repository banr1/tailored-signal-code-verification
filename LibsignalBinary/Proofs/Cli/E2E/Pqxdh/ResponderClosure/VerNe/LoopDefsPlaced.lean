/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DecDefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable One-Element `previous_sessions` Loop Statement

Relocatable (`[LibsignalPlacement]`) statement `OverPrevLoopCliPlacedStmtGen`
(`(blkPl_518).base + 0x1e78 → (blkPl_518).base + 0x2cfc`) on `lsProg_518`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.CliHandshake.RespClosurePlaced

/-- Relocatable `[LibsignalPlacement]` 1-element `previous_sessions` loop
(`(blkPl_518).base + 0x1e78 → (blkPl_518).base + 0x2cfc`) on `lsProg_518 ext`. -/
def OverPrevLoopCliPlacedStmtGen [LibsignalPlacement] (trackVRegs : Bool) : Prop :=
  ∀ (ext : String → Option (State → State)),
    ∀ (s0 s : State) (coroPtr prevCap prevPtr errsPtr wd0 u3e0 : BitVec 64)
      (msgVer : BitVec 32) (enc : List (BitVec 8)),
      prevCap ≠ 0#64 →
      msgVer ≠ 4#32 →
      OverPrevEncOK enc →
      (lsProg_518 ext).CodeLoaded s.mem →
      s.pc = (blkPl_518).base + 0x1e78#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      overDecStackX ≤ s.sp.toNat →
      s.trace = s0.trace →
      s.readReg64 .x19 = coroPtr →
      s.readReg64 .x29 = s.sp + 0xc70#64 →
      SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2cfc#64) s
        (prevVecAt A0 (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
         ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
         ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗
         ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
         ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
         ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
         ((s.sp + 0x3e0#64) ↦₆₄ u3e0) ∗
         memRegion (errsPtr + 48#64) 144 ∗
         memRegion (s.sp + 0x538#64) 1016 ∗
         memRegion (s.sp + 0x930#64) 48 ∗
         memRegion (s.sp + 0x960#64) 48 ∗
         memRegion (s.sp + 0x990#64) 256 ∗
         memRegion (s.sp + 0xa90#64) 344 ∗
         memRegion (s.sp + 0xbe8#64) 136 ∗
         pqLogLevelCellPlaced ∗
         A0.pool ∗
         stackAt s.sp overDecStackX)
        (fun sf P_f =>
          (P_f ⊢
            prevVecAt A0 (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
            ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
            ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
            ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
            ((errsPtr + 56#64) ↦₃₂ msgVer) ∗
            memRegion (errsPtr + 60#64) 36 ∗
            memRegion (errsPtr + 96#64) 96 ∗
            memRegion (s.sp + 0x538#64) 1016 ∗
            memRegion (s.sp + 0x930#64) 48 ∗
            memRegion (s.sp + 0x960#64) 48 ∗
            memRegion (s.sp + 0x990#64) 256 ∗
            memRegion (s.sp + 0xa90#64) 344 ∗
            memRegion (s.sp + 0xbe8#64) 136 ∗
            pqLogLevelCellPlaced ∗
            A0.pool ∗
            stackAt s.sp overDecStackX ∗
            anyHeap) ∧
          sf.sp = s.sp ∧
          sf.trace = s0.trace ∧
          sf.readReg64 .x19 = coroPtr ∧
          sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
          optVRegsEq trackVRegs sf s ∧
          (lsProg_518 ext).CodeLoaded sf.mem)
        (PanicOomProp s0)

abbrev OverPrevLoopCliPlacedStmt [LibsignalPlacement] : Prop :=
  OverPrevLoopCliPlacedStmtGen true

abbrev OverPrevLoopCliGPRPlacedStmt [LibsignalPlacement] : Prop :=
  OverPrevLoopCliPlacedStmtGen false

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
