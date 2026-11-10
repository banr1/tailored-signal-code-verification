/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.PrevBridge
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrB
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Version-Mismatch Closure Heap and Statement Definitions

Stack scratch layout (`overScratch`), optional vector-register preservation (`optVRegsEq`), and
`+0x1e04 → ret` specification statements (`OverVerNe1e04CliStmtGenExt`, `OverVerNe1e04CliA0StmtGen`)
for the CLI PQXDH responder closure version-mismatch (`msgVer ≠ 4`) path with one archived
`previous_sessions` entry.
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
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (growOneSpeStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (stageP3ErrPostPrevEmpty)

/-- Optional `calleeSavedVRegs` preservation (`true` = full ARM64 PCS `d8..d15`, `false` = GPR-only). -/
def optVRegsEq (trackVRegs : Bool) (sf s : State) : Prop :=
  if trackVRegs then calleeSavedVRegs sf = calleeSavedVRegs s else True

theorem optVRegsEq_refl (trackVRegs : Bool) (s : State) : optVRegsEq trackVRegs s s := by
  cases trackVRegs <;> simp [optVRegsEq]

theorem optVRegsEq_trans {trackVRegs : Bool} {s1 s2 s3 : State}
    (h12 : optVRegsEq trackVRegs s2 s1) (h23 : optVRegsEq trackVRegs s3 s2) :
    optVRegsEq trackVRegs s3 s1 := by
  cases trackVRegs
  · trivial
  · simp only [optVRegsEq, ↓reduceIte] at h12 h23 ⊢
    exact h23.trans h12

theorem optVRegsEq_of_vregs_eq (trackVRegs : Bool) {sf s : State}
    (h : calleeSavedVRegs sf = calleeSavedVRegs s) :
    optVRegsEq trackVRegs sf s := by
  cases trackVRegs <;> simp [optVRegsEq, h]

@[simp]
theorem optVRegsEq_true (sf s : State) :
    optVRegsEq true sf s ↔ calleeSavedVRegs sf = calleeSavedVRegs s :=
  Iff.rfl

@[simp]
theorem optVRegsEq_false (sf s : State) :
    optVRegsEq false sf s ↔ True :=
  Iff.rfl

/-- Closure stack scratch slots untouched outside the 1-element `previous_sessions` loop
(`sp + 0x538..0x930` = 1016 B, `sp + 0x990..0xa90` = 256 B, `sp + 0xbe8..0xc70` = 136 B). -/
def overScratch (q : BitVec 64) : SepProp :=
  memRegion (q + 0x538#64) 1016 ∗
  memRegion (q + 0x990#64) 256 ∗
  memRegion (q + 0xbe8#64) 136

/-- Version-mismatch closure segment specification (`+0x1e04 → s0.readReg64 .x30`) for arbitrary
`A : RustAlloc` under `AllocContractsMem4K` over a 1-element `previous_sessions` vector. -/
def OverVerNe1e04CliStmtGenExt (A : RustAlloc) (trackVRegs : Bool) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    AllocContractsMem4K img.base A ext →
    ∀ (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0 : BitVec 64),
      initErrsPtr ≠ 0#64 →
      prevCap ≠ 0#64 →
      ∀ (msgVer : BitVec 32), msgVer ≠ 4#32 →
      ∀ (b_2c0 : BitVec 8) (enc : List (BitVec 8)), OverPrevEncOK enc →
      ∀ (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8))),
        st.version = 4#32 →
        rootStack ≤ s.sp.toNat →
        img.FrozenLoaded s1 →
        s1.symtab = img.symtab →
        s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1e04#64 →
        s1.status = .Running →
        s1.sp = s.sp →
        (s.sp &&& 15#64 == 0#64) = true →
        s1.trace = s0.trace →
        s1.readReg64 .x9 = msgVer.setWidth 64 →
        s1.readReg64 .x19 = coroPtr →
        s1.readReg64 .x24 = s.sp + 0x370#64 →
        s1.readReg64 .x27 = ctxPtr →
        s1.readReg64 .x29 = s.sp + 0xc70#64 →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
          (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
           ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
           ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
           ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
           ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
           ((s.sp + 0xd0#64) ↦₆₄ ud0) ∗
           ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
           ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
           ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
           ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
           memRegion (s.sp + 0x3e0#64) 344 ∗
           memRegion (s.sp + 0x930#64) 48 ∗
           memRegion (s.sp + 0x960#64) 48 ∗
           overScratch s.sp ∗
           sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
           sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
           prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
           ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
           logOff img ∗
           memRegion outPtr 48 ∗
           memRegion (s.sp + 0x250#64) 20 ∗
           memRegion (s.sp + 0x270#64) 48 ∗
           memRegion (s.sp + 0x370#64) 36 ∗
           decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
           A.pool ∗
           stackAt s.sp rootStack)
          (fun sf P_f =>
            (∃ wd0 : BitVec 64,
              P_f ⊢
                ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
                ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
                ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
                ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗
                memRegion (s.sp + 0x3e0#64) 344 ∗
                memRegion (s.sp + 0x960#64) 48 ∗
                overScratch s.sp ∗
                memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
                stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr
                  (.invalidMessage .preKey .decryptionFailed) ∗
                anyHeap) ∧
            sf.sp = s.sp + 0xcd0#64 ∧
            sf.trace = s0.trace ∧
            ClosureCalleeSaved s0 sf ∧
            img.FrozenLoaded sf ∧
            sf.symtab = img.symtab ∧
            optVRegsEq trackVRegs sf s1)
          (P3P4.PanicOomProp s0)

abbrev OverVerNe1e04CliStmtExt (A : RustAlloc) : Prop := OverVerNe1e04CliStmtGenExt A true
abbrev OverVerNe1e04CliGPRStmtExt (A : RustAlloc) : Prop := OverVerNe1e04CliStmtGenExt A false

/-- Specialization of `OverVerNe1e04CliStmtGenExt` to `A = Record.A0` under `AllocContracts`. -/
def OverVerNe1e04CliA0StmtGen (trackVRegs : Bool) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    AllocContracts img.base A0 ext →
    ∀ (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0 : BitVec 64),
      initErrsPtr ≠ 0#64 →
      prevCap ≠ 0#64 →
      ∀ (msgVer : BitVec 32), msgVer ≠ 4#32 →
      ∀ (b_2c0 : BitVec 8) (enc : List (BitVec 8)), OverPrevEncOK enc →
      ∀ (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8))),
        st.version = 4#32 →
        rootStack ≤ s.sp.toNat →
        img.FrozenLoaded s1 →
        s1.symtab = img.symtab →
        s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1e04#64 →
        s1.status = .Running →
        s1.sp = s.sp →
        (s.sp &&& 15#64 == 0#64) = true →
        s1.trace = s0.trace →
        s1.readReg64 .x9 = msgVer.setWidth 64 →
        s1.readReg64 .x19 = coroPtr →
        s1.readReg64 .x24 = s.sp + 0x370#64 →
        s1.readReg64 .x27 = ctxPtr →
        s1.readReg64 .x29 = s.sp + 0xc70#64 →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
          (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
           ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
           ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
           ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
           ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
           ((s.sp + 0xd0#64) ↦₆₄ ud0) ∗
           ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
           ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
           ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
           ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
           memRegion (s.sp + 0x3e0#64) 344 ∗
           memRegion (s.sp + 0x930#64) 48 ∗
           memRegion (s.sp + 0x960#64) 48 ∗
           overScratch s.sp ∗
           sessionStateAt A0 (s.sp + 0xa90#64) G₁ st ∗
           sessionStateAt A0 (coroPtr + 0xf8#64) recG st ∗
           prevVecAt A0 (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
           ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
           logOff img ∗
           memRegion outPtr 48 ∗
           memRegion (s.sp + 0x250#64) 20 ∗
           memRegion (s.sp + 0x270#64) 48 ∗
           memRegion (s.sp + 0x370#64) 36 ∗
           decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
           A0.pool ∗
           stackAt s.sp rootStack)
          (fun sf P_f =>
            (∃ wd0 : BitVec 64,
              P_f ⊢
                ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
                ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
                ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
                ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗
                memRegion (s.sp + 0x3e0#64) 344 ∗
                memRegion (s.sp + 0x960#64) 48 ∗
                overScratch s.sp ∗
                memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
                stageP3ErrPostPrevEmpty A0 img.base s0 s coroPtr outPtr
                  (.invalidMessage .preKey .decryptionFailed) ∗
                anyHeap) ∧
            sf.sp = s.sp + 0xcd0#64 ∧
            sf.trace = s0.trace ∧
            ClosureCalleeSaved s0 sf ∧
            img.FrozenLoaded sf ∧
            sf.symtab = img.symtab ∧
            optVRegsEq trackVRegs sf s1)
          (P3P4.PanicOomProp s0)

abbrev OverVerNe1e04CliA0Stmt : Prop := OverVerNe1e04CliA0StmtGen true
abbrev OverVerNe1e04CliA0GPRStmt : Prop := OverVerNe1e04CliA0StmtGen false

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
