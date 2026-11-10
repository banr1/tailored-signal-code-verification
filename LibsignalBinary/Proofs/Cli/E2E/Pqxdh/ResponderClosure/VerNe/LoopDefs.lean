/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DecDefs

/-!
# One-Element `previous_sessions` Loop Statements

Statement definitions `OverPrevLoopCliStmtGenExt` and `OverPrevLoopCliStmtGen` (`+0x1e78 → +0x2cfc`
on `tripleRatchetProgAtExt`): enters the `previous_sessions` loop with `len = 1`, decodes `enc`,
runs the `memcpy` chain, checks `4 ≠ msgVer`, appends a second `UnrecognizedMessageVersion` error
(`errs.len = 2`), drops the decoded `SessionStructure`, and exits to `+0x2cfc`.
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
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (AllocContractsMem4K)

/-- One-element `previous_sessions` loop statement (`+0x1e78 → +0x2cfc`) under `AllocContractsMem4K`. -/
def OverPrevLoopCliStmtGenExt (A : RustAlloc) (trackVRegs : Bool) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    AllocContractsMem4K img.base A ext →
    ∀ (s0 s : State) (coroPtr prevCap prevPtr errsPtr wd0 u3e0 : BitVec 64)
      (msgVer : BitVec 32) (enc : List (BitVec 8)),
      prevCap ≠ 0#64 →
      msgVer ≠ 4#32 →
      OverPrevEncOK enc →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1e78#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      overDecStackX ≤ s.sp.toNat →
      s.trace = s0.trace →
      s.readReg64 .x19 = coroPtr →
      s.readReg64 .x29 = s.sp + 0xc70#64 →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x2cfc#64) s
        (prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
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
         logOff img ∗
         A.pool ∗
         stackAt s.sp overDecStackX)
        (fun sf P_f =>
          (P_f ⊢
            prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
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
            logOff img ∗
            A.pool ∗
            stackAt s.sp overDecStackX ∗
            anyHeap) ∧
          sf.sp = s.sp ∧
          sf.trace = s0.trace ∧
          sf.readReg64 .x19 = coroPtr ∧
          sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
          optVRegsEq trackVRegs sf s ∧
          img.FrozenLoaded sf ∧
          sf.symtab = img.symtab)
        (PanicOomProp s0)

abbrev OverPrevLoopCliStmtExt (A : RustAlloc) : Prop := OverPrevLoopCliStmtGenExt A true
abbrev OverPrevLoopCliGPRStmtExt (A : RustAlloc) : Prop := OverPrevLoopCliStmtGenExt A false

/-- Specialization of `OverPrevLoopCliStmtGenExt` to `A = Record.A0` under `AllocContracts`. -/
def OverPrevLoopCliStmtGen (trackVRegs : Bool) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    AllocContracts img.base A0 ext →
    ∀ (s0 s : State) (coroPtr prevCap prevPtr errsPtr wd0 u3e0 : BitVec 64)
      (msgVer : BitVec 32) (enc : List (BitVec 8)),
      prevCap ≠ 0#64 →
      msgVer ≠ 4#32 →
      OverPrevEncOK enc →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1e78#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      overDecStackX ≤ s.sp.toNat →
      s.trace = s0.trace →
      s.readReg64 .x19 = coroPtr →
      s.readReg64 .x29 = s.sp + 0xc70#64 →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x2cfc#64) s
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
         logOff img ∗
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
            logOff img ∗
            A0.pool ∗
            stackAt s.sp overDecStackX ∗
            anyHeap) ∧
          sf.sp = s.sp ∧
          sf.trace = s0.trace ∧
          sf.readReg64 .x19 = coroPtr ∧
          sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
          optVRegsEq trackVRegs sf s ∧
          img.FrozenLoaded sf ∧
          sf.symtab = img.symtab)
        (PanicOomProp s0)

abbrev OverPrevLoopCliStmt : Prop := OverPrevLoopCliStmtGen true
abbrev OverPrevLoopCliGPRStmt : Prop := OverPrevLoopCliStmtGen false

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
