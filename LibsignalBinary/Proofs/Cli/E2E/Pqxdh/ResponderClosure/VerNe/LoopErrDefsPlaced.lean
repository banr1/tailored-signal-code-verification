/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.ConstsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Previous-Session Version-Skip Tail Statement

Relocatable (`[LibsignalPlacement]`) statement `OverPrevErrCliPlacedStmt`
(`(blkPl_518).base + 0x1fd4 → (blkPl_518).base + 0x2cfc`) on `lsProg_518`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.CliHandshake.RespClosurePlaced

/-- Relocatable `[LibsignalPlacement]` previous-session version-skip tail
(`(blkPl_518).base + 0x1fd4 → (blkPl_518).base + 0x2cfc`) on `lsProg_518 ext`. -/
def OverPrevErrCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {A : RustAlloc} (ext : String → Option (State → State)),
    ∀ (s0 s : State) (prevPtr errsPtr : BitVec 64) (msgVer : BitVec 32)
      (G : SessionGhost) (st : SessionState (List (BitVec 8))),
      msgVer ≠ 4#32 →
      (lsProg_518 ext).CodeLoaded s.mem →
      s.pc = (blkPl_518).base + 0x1fd4#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.trace = s0.trace →
      s.readReg64 .x8 = 4#64 →
      s.readReg64 .x27 = prevPtr →
      SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2cfc#64) s
        (((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
         ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
         ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
         ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
         ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
         memRegion (errsPtr + 48#64) 144 ∗
         memRegion (s.sp + 0xa90#64) 344 ∗
         sessionStateAt A (s.sp + 0x930#64) G st ∗
         pqLogLevelCellPlaced ∗
         A.pool ∗
         stackAt s.sp growOneSpeStack)
        (fun sf P_f =>
          (P_f ⊢
            ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
            ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
            ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
            ((errsPtr + 56#64) ↦₃₂ msgVer) ∗
            memRegion (errsPtr + 60#64) 36 ∗
            memRegion (errsPtr + 96#64) 96 ∗
            memRegion (s.sp + 0xa90#64) 344 ∗
            memRegion (s.sp + 0x930#64) 344 ∗
            pqLogLevelCellPlaced ∗
            A.pool ∗
            stackAt s.sp growOneSpeStack) ∧
          sf.sp = s.sp ∧
          sf.trace = s0.trace ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (lsProg_518 ext).CodeLoaded sf.mem)
        (PanicOomProp s0)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
