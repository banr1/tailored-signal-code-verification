/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DefsPlaced

/-!
# Budget-Threaded Relocatable Version-Mismatch Closure Definitions

Allocator-budget (`RustCliAllocBudget M`) relocatable error-exit postcondition
(`stageP3ErrPostPrevEmptyPlaced`) and envelope-parameterized `+0x1e04 → s0.readReg64 .x30`
statements (`OverVerNe1e04CliPlacedStmtGen`) on Block `518` (`lsProg_518`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DefsPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (SessionState SignalProtocolError)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet (recordResultAt rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (growOneSpeStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  ClosureCalleeSaved decryptPrekeySavedRegsAt
)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe (
  OverPrevEncOK optVRegsEq overScratch pqLogLevelCellPlaced prevVecAt
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget
)

/-- Budget-threaded relocatable error-exit postcondition at `s0.readReg64 .x30`, pairing
`recordResultAt A.repAlloc` and `pqLogLevelCellPlaced` with `A.pool lim st sf`. -/
def stageP3ErrPostPrevEmptyPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 s sf : State) (coroPtr outPtr : BitVec 64)
    (e : SignalProtocolError) : SepProp :=
  (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
    ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
    ((s.sp + 0x3d8#64) ↦₆₄ errsLen)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (s.sp + 0xa90#64) 344 ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  pqLogLevelCellPlaced ∗
  recordResultAt A.repAlloc outPtr (.error (SessionState.recordError .preKey e)) ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st sf ∗ stackAt s.sp growOneSpeStack

theorem stageP3ErrPostPrevEmptyPlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 s sf : State) (coroPtr outPtr : BitVec 64)
    (e : SignalProtocolError) :
    stageP3ErrPostPrevEmptyPlaced A lim st s0 s sf coroPtr outPtr e =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.stageP3ErrPostPrevEmptyPlaced
        (A.atState lim st sf) s0 s coroPtr outPtr e :=
  rfl

/-- Envelope-parameterized budget-threaded `+0x1e04 → s0.readReg64 .x30` CLI version-mismatch
statement over a 1-element `previous_sessions` on `lsProg_518 ext`. -/
def OverVerNe1e04CliPlacedStmtGen [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : List (BitVec 8) → List AllocEvent → Prop)
    (Qp : M.σ → State → State → SepProp → Prop)
    (trackVRegs : Bool) : Prop :=
  ∀ (ext : String → Option (State → State)),
    ∀ (st_init : M.σ) (s0 s s1 : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0 : BitVec 64),
      initErrsPtr ≠ 0#64 →
      prevCap ≠ 0#64 →
      ∀ (msgVer : BitVec 32), msgVer ≠ 4#32 →
      ∀ (b_2c0 : BitVec 8) (enc : List (BitVec 8)), OverPrevEncOK enc →
      FitsEnv M lim st_init (Env enc) →
      ∀ (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8))),
        st.version = 4#32 →
        rootStack ≤ s.sp.toNat →
        (lsProg_518 ext).CodeLoaded s1.mem →
        s1.pc = lsmpl.base 518 + 0x1e04#64 →
        s1.status = .Running →
        s1.sp = s.sp →
        (s.sp &&& 15#64 == 0#64) = true →
        s1.trace = s0.trace →
        s1.readReg64 .x9 = msgVer.setWidth 64 →
        s1.readReg64 .x19 = coroPtr →
        s1.readReg64 .x24 = s.sp + 0x370#64 →
        s1.readReg64 .x27 = ctxPtr →
        s1.readReg64 .x29 = s.sp + 0xc70#64 →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
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
           sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
           sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
           prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
           ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
           pqLogLevelCellPlaced ∗
           memRegion outPtr 48 ∗
           memRegion (s.sp + 0x250#64) 20 ∗
           memRegion (s.sp + 0x270#64) 48 ∗
           memRegion (s.sp + 0x370#64) 36 ∗
           decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
           A.pool lim st_init s1 ∗
           stackAt s.sp rootStack)
          (fun sf P_f =>
            (∃ (wd0 : BitVec 64) (evs : List AllocEvent),
              Env enc evs ∧
              (P_f ⊢
                ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
                ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
                ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
                ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗
                memRegion (s.sp + 0x3e0#64) 344 ∗
                memRegion (s.sp + 0x960#64) 48 ∗
                overScratch s.sp ∗
                memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
                stageP3ErrPostPrevEmptyPlaced A lim (M.stepEvents evs st_init) s0 s sf coroPtr outPtr
                  (.invalidMessage .preKey .decryptionFailed))) ∧
            sf.sp = s.sp + 0xcd0#64 ∧
            sf.trace = s0.trace ∧
            ClosureCalleeSaved s0 sf ∧
            (lsProg_518 ext).CodeLoaded sf.mem ∧
            optVRegsEq trackVRegs sf s1)
          (Qp st_init s0)

abbrev OverVerNe1e04CliPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : List (BitVec 8) → List AllocEvent → Prop)
    (Qp : M.σ → State → State → SepProp → Prop) : Prop :=
  OverVerNe1e04CliPlacedStmtGen A lim Env Qp true

abbrev OverVerNe1e04CliGPRPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : List (BitVec 8) → List AllocEvent → Prop)
    (Qp : M.σ → State → State → SepProp → Prop) : Prop :=
  OverVerNe1e04CliPlacedStmtGen A lim Env Qp false

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DefsPlacedBudget
