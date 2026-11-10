/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.PoolNeedLocks
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainOkComposePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

/-!
# Placed Budgeted `main` Hop Composition with Read-Only `argv` and `NeedLocks`

Composes the Block-`617` `main` hop continuations (`step1`..`step6`) into
`b2MainSpecTightNeedLocksFineAt` over read-only `argvAtRO` / `argvAtROP` and `ExitKPoolPlaced`,
retaining `((libcAddr + 3#64) ↦₈ 0#8)` (`__libc.need_locks = 0`) at `main` return.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement LibsignalRoLoaded libsignalMutatedBlocks
   libsignalSessionExterns lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (allocFailedIn)
open CryptoVerification.SignalSession (CliHooks Inputs libsignalSessionLib stdinCapBytes)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk CoinsReadable IsSendOverCap IsStdinOverCap MainCaseB2 MainGhost MainPost MainResult
   RunAnswer StoresGhost cliInputs cliStaticsPlaced utf8)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AtCallPlaced AtEntryPlaced AtM1EndPlaced AtM4EndPlaced AtM4EndTightPlaced AtM4Placed
   AtM6Placed CallV CallW HistOkTight IoModel LsCodeInv MainIoFacts argsBuf callCellsPlaced
   callHeap coinsOf commitFiles inputOf locals m4CellsPlaced m5CellsPlaced m6CellsPlaced mProgPlaced
   mainFrameSize mainLitsBlk617 mainLitsPlaced_of_roLoaded mainOom mainSaved namedWrites ownedBytes
   parseArgs parseArgs_none_of_shape_proof)
open CryptoVerification.SignalSession.Cli.MainHops.MainOkPlacedHelpers
  (panic_of_mem sepWPp_mono_post traceStreamBytes_nil)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine
  (FineBudget fineCostModel fineHookRustCliAllocBudget hookPool_entails_needLocks_anyHeap)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
  (B2MainEntryFacts argvAtRO b2MainFrameFine b2MainSpecTightNeedLocksFineAt cStrAtRO
   cliStaticsPlacedAt cliStaticsPlacedAt_eq_cliStaticsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
  (ExitKPoolPlaced main_ret_placed_needLocks_proof)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-! ## Read-only pointer-indexed `argv` predicates -/

/-- Read-only pointer-indexed C `argv` table at `a`. -/
def argvAtROP : BitVec 64 → List (BitVec 64 × List (BitVec 8)) → SepProp
  | a, [] => a ↦₆₄ᵣ 0#64
  | a, (p, s) :: rest => (a ↦₆₄ᵣ p) ∗ cStrAtRO p s ∗ argvAtROP (a + 8#64) rest

/-- Prefix of `argvAtROP` without the trailing NUL pointer slot. -/
def argvAtROPPrefix : BitVec 64 → List (BitVec 64 × List (BitVec 8)) → SepProp
  | _, [] => emp
  | a, (p, s) :: ps => (a ↦₆₄ᵣ p) ∗ cStrAtRO p s ∗ argvAtROPPrefix (a + 8#64) ps

theorem argvAtRO_entails_argvAtROP (a : BitVec 64) (ss : List (List (BitVec 8))) :
    argvAtRO a ss ⊢
      ∃∗ ps : List (BitVec 64 × List (BitVec 8)), ⌜ps.map (·.2) = ss⌝ ∗ argvAtROP a ps := by
  induction ss generalizing a with
  | nil =>
    exact Entails.sepExists_right [] (Entails.pure_right rfl (Entails.refl _))
  | cons s ss ih =>
    simp only [argvAtRO]
    apply Entails.sepExists_elim
    intro p
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (ih (a + 8#64)))) ?_
    simp only [sepExists_sepConj_right]
    apply Entails.sepExists_elim
    intro ps
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl)) ?_
    apply Entails.pure_left
    rintro rfl
    exact Entails.sepExists_right ((p, s) :: ps)
      (Entails.pure_right rfl (Entails.of_eq (by simp only [argvAtROP]; sep_ac_rfl)))

theorem argvAtROP_append (a : BitVec 64) (xs ys : List (BitVec 64 × List (BitVec 8))) :
    argvAtROP a (xs ++ ys) =
      argvAtROPPrefix a xs ∗ argvAtROP (a + BitVec.ofNat 64 (8 * xs.length)) ys := by
  induction xs generalizing a with
  | nil =>
    simp only [List.nil_append, argvAtROPPrefix, List.length_nil, Nat.mul_zero,
      BitVec.add_zero, emp_sepConj]
  | cons x xs ih =>
    rcases x with ⟨p, s⟩
    simp only [List.cons_append, argvAtROP, argvAtROPPrefix, List.length_cons, ih (a + 8#64)]
    have haddr : a + 8#64 + BitVec.ofNat 64 (8 * xs.length) =
        a + BitVec.ofNat 64 (8 * (xs.length + 1)) := by
      have : 8 * (xs.length + 1) = 8 + 8 * xs.length := by omega
      rw [this, BitVec.ofNat_add]
      bv_omega
    rw [haddr]
    sep_ac_rfl

/-! ## Read-only literal framing and `NeedLocks` exit continuation -/

/-- A budgeted `main` hop proved with `mainLitsBlk617` among the statics (`Statics ∗ mainLitsBlk617`)
over `b2MainFrameFine` holds without them wherever `LibsignalRoLoaded lsmpl s.mem` holds. -/
theorem sepWPp_b2MainFrameFine_mainLitsPlaced [LibsignalPlacement] {prog : Program}
    {ret : BitVec 64} {s : State} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {stk : Nat} {Statics : SepProp} {i : Inputs}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hwp : SepWPp prog ret s
      (b2MainFrameFine A lim st stk (Statics ∗ mainLitsBlk617) i s) Q Qp oom) :
    SepWPp prog ret s (b2MainFrameFine A lim st stk Statics i s) Q Qp oom := by
  intro R hm
  apply hwp R
  have h := mainLitsPlaced_of_roLoaded hro hm
  refine Satisfies.of_eq h ?_
  simp only [b2MainFrameFine]
  sep_ac_rfl

theorem post_of_mem_needLocks_tight {libcAddr : BitVec 64} {r : MainResult} {s0 sf : State}
    {stk : Nat} {Pf R : SepProp}
    (hpost : MainPost r s0 sf)
    (hPf : Pf ⊢ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ anyHeap)
    (hmf : sf.mem ⊨ Pf ∗ R) :
    sf.mem ⊨
      (⌜MainPost r s0 sf⌝ ∗ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ anyHeap) ∗ R := by
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hpost, ?_⟩
  have hmf' := Satisfies.mono (sepConj_mono_left hPf) hmf
  simpa only [sepConj_assoc] using hmf'

/-- Build `ExitKPoolPlaced` for `b2MainSpecTightNeedLocksFineAt` from any pool-to-`NeedLocks`
projection `hneed` and `RetPlacedBudget.main_ret_placed_needLocks_proof`. -/
theorem exitKPool_b2NeedLocks_tight_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {libcAddr : BitVec 64} {lim : BudgetLimits} {r : MainResult} {s0 : State} {stk : Nat}
    {R : SepProp} {G : Nat → State → Prop}
    (hneed : ∀ (st' : M.σ) (sf : State),
      A.pool lim st' sf ⊢ ((libcAddr + 3#64) ↦₈ 0#8) ∗ anyHeap)
    (hstk : mainFrameSize ≤ stk)
    (hG : ∀ code s, G code s → ∀ sf, sf.trace = s.trace → sf.fs = s.fs →
      (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code →
      MainPost r s0 sf) :
    ExitKPoolPlaced CodeOk H A lim s0 stk G
      (fun sf Pf =>
        ((sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜MainPost r s0 sf⌝ ∗
            ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ anyHeap) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ R)) := by
  intro s st code hs hg
  exact sepWPp_mono_post
    (fun sf Pf ⟨hsp, hcs, hx0, htr, hfs, _, hPf⟩ =>
      ⟨post_of_mem_needLocks_tight (hG code s hg sf htr hfs hx0) hPf, hsp, hcs⟩)
    (main_ret_placed_needLocks_proof (st := st) hneed hstk hs)

/-! ## Invariant-threaded `b2MainSpecTightNeedLocksFineAt` hop composer -/

/-- Compose budgeted hop continuations `step1`..`step6` into `b2MainSpecTightNeedLocksFineAt` on
Block `617` while threading cost-state invariants `St0`..`St5`. -/
theorem b2_main_ok_tight_needLocks_with_inv_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {libcAddr : BitVec 64} {lim : BudgetLimits} {st0 : M.σ}
    {St0 : Inputs → M.σ → Prop}
    {St1 : Inputs → M.σ → Prop}
    {St2 : Inputs → CallV → M.σ → Prop}
    {St3 : Inputs → CallV → M.σ → Prop}
    {St4 : Inputs → CallV → StoresGhost → M.σ → Prop}
    {St5 : Inputs → CallV → StoresGhost → Bool → M.σ → Prop}
    {io : IoModel} {Run : Inputs → RunAnswer → Prop} {inputsOf : Inputs → ProcessInputs}
    {stk : Nat}
    (hfacts : MainIoFacts io)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hneed : ∀ (st' : M.σ) (sf : State),
      A.pool lim st' sf ⊢ ((libcAddr + 3#64) ↦₈ 0#8) ∗ anyHeap)
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hstk_frame : mainFrameSize ≤ stk)
    (hSt0 : ∀ i : Inputs, CliInputsOk i → St0 i st0)
    (step1 : ∀ {i : Inputs} {s0 : State} {Statics : SepProp} {Q Qp : State → SepProp → Prop}
      {oom : State → SepProp},
      St0 i st0 →
      AtEntryPlaced CodeOk i s0 →
      CliInputsOk i →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPoolPlaced CodeOk H A lim s0 stk
        (fun code s => code = 2 ∧ i.argv = [] ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp →
      (∀ (s : State) (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) (p0 : BitVec 64)
          (st1 : M.σ),
        St1 i st1 →
        i.argv ≠ [] → ps.map (·.2) = i.argv.map bytesOfString →
        AtM1EndPlaced CodeOk s0 s i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
          (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st1 s ∗ Statics)
          Q Qp oom) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0
        (b2MainFrameFine A lim st0 stk Statics i s0) Q Qp oom)
    (step2 : ∀ {i : Inputs} {s0 s : State} {buf p0 : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {st1 : M.σ} {Statics : SepProp}
      {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
      St1 i st1 →
      CliInputsOk i → i.argv ≠ [] →
      ps.map (·.2) = i.argv.map bytesOfString →
      AtM1EndPlaced CodeOk s0 s i.argv.length buf →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPoolPlaced CodeOk H A lim s0 stk
        (fun code s' => code = 2 ∧ parseArgs uuidTryParse (i.argv.map bytesOfString) = none ∧
          s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp →
      (∀ (s' : State) (w : CallW) (c : CallV) (st2 : M.σ),
        St2 i c st2 →
        parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
        AtCallPlaced CodeOk s0 s' w i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st2 s' ∗ Statics)
          Q Qp oom) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st1 s ∗ Statics)
        Q Qp oom)
    (step3 : ∀ {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
      {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))} {st2 : M.σ}
      {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
      St2 i c st2 →
      s0.fs = initFsState (cliInputs i) → s0.trace = [] →
      io.stdin (initFsState (cliInputs i)) = some i.stdin →
      io.pathOk (utf8 "coins") →
      (∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
        r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i)) →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s w i.argv.length buf →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPoolPlaced CodeOk H A lim s0 stk
        (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
          (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
        Q Qp →
      (∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64) (st3 : M.σ),
        St3 i c st3 →
        (inputOf i c).length ≤ stdinCapBytes →
        AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
            ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st3 s' ∗ cliStaticsPlaced ∗ mainLitsBlk617)
          Q Qp oom) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st2 s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom)
    (step4_overCap : ∀ {i : Inputs} {peer : AddrV} {w : CallW} {s0 s : State}
      {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {st3 : M.σ} {Q Qp : State → SepProp → Prop},
      St3 i (.send peer) st3 →
      stk ≤ s0.sp.toNat →
      s0.trace = [] →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer) →
      1_000_000 < i.stdin.length →
      AtM4Placed CodeOk i s0 s w (.send peer) i.argv.length buf coinsCap coinsPtr inCap →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPoolPlaced CodeOk H A lim s0 stk
        (fun code s' => code = 1 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
          s'.trace = s.trace) Q Qp →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i (.send peer)).length)
            (inputOf i (.send peer)) ∗
          callHeap A.repAlloc w (.send peer) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st3 s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp (mainOom s0))
    (step4_call : ∀ {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
      {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {st3 : M.σ} {Q Qp : State → SepProp → Prop},
      St3 i c st3 →
      stk ≤ s0.sp.toNat →
      s0.trace = [] →
      Run i a → ¬ IsSendOverCap i →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap →
      (∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf) →
      ExitKPoolPlaced CodeOk H A lim s0 stk
        (fun code s' => code = 1 ∧ a = some none ∧ HistOkTight i s' ∧
          s.trace <+: s'.trace) Q Qp →
      (∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)) (st4 : M.σ),
        St4 i c g st4 →
        a = some (some (namedWrites g.writes, out)) →
        (∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) → s.trace <+: s'.trace →
        AtM4EndTightPlaced CodeOk i s0 s' c i.argv.length buf inCap →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st4 s' ∗ anyHeap)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st3 s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp (mainOom s0))
    (step5 : ∀ {i : Inputs} {c : CallV} {g : StoresGhost} {out : List (BitVec 8)}
      {s0 s : State} {buf inCap inPtr : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
      {st4 : M.σ} {Q Qp : State → SepProp → Prop},
      St4 i c g st4 →
      s0.trace = [] →
      (∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) →
      AtM4EndPlaced CodeOk i s0 s c i.argv.length buf inCap →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      (∀ (s' : State) (ok : Bool) (outCap outPtr : BitVec 64) (st5 : M.σ),
        St5 i c g ok st5 →
        (match commitFiles io.wr s.fs.files g.writes with
         | some F => ok = true ∧ s'.fs.files = F
         | none => ok = false) →
        s.trace <+: s'.trace →
        ProcessOutcome.traceStreamBytes .stdout s'.trace =
          ProcessOutcome.traceStreamBytes .stdout s.trace →
        AtM6Placed CodeOk s0 s' ok i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
                (BitVec.ofNat 64 out.length) inCap inPtr) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st5 s' ∗ anyHeap)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st4 s ∗ anyHeap)
        Q Qp (mainOom s0))
    (step6 : ∀ {i : Inputs} {c : CallV} {g : StoresGhost} {s0 s : State} {ok : Bool}
      {buf outCap outPtr inCap inPtr : BitVec 64}
      {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))} {st5 : M.σ}
      {Q Qp : State → SepProp → Prop},
      St5 i c g ok st5 →
      AtM6Placed CodeOk s0 s ok i.argv.length buf →
      ExitKPoolPlaced CodeOk H A lim s0 stk
        (fun code s' => s'.fs.files = s.fs.files ∧
          (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
              ProcessOutcome.traceStreamBytes .stdout s'.trace =
              ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
           else code = 2 ∧ s'.trace = s.trace)) Q Qp →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
              (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st5 s ∗ anyHeap)
        Q Qp (mainOom s0)) :
    subroutine_ok (mProgPlaced H) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk A lim st0 stk cliStaticsPlaced Run inputsOf) := by
  apply subroutine_ok_of_sepWPp_init
  intro ⟨i, r⟩ R s0 hpc hrun0 hpre hal
  simp only [b2MainSpecTightNeedLocksFineAt, B2MainEntryFacts, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hCO, hcase, hok, ⟨hargc, hfs0_in, htr0⟩, hsp⟩, hm⟩ := hpre
  have hfs0 : s0.fs = initFsState (cliInputs i) := hfs0_in.trans (hfs_eq i)
  have hst0 : St0 i st0 := hSt0 i hok
  refine ⟨b2MainFrameFine A lim st0 stk cliStaticsPlaced i s0, ?_, ?_⟩
  · simpa only [b2MainFrameFine, sepConj_assoc] using hm
  · apply sepWPp_b2MainFrameFine_mainLitsPlaced (hCI.toRoCl hCO).2
    change SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0
      (b2MainFrameFine A lim st0 stk (cliStaticsPlaced ∗ mainLitsBlk617) i s0)
      (fun sf Pf =>
        ((sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜MainPost r s0 sf⌝ ∗
            ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ anyHeap) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ R))
      (mainOom s0)
    have hs0 : AtEntryPlaced CodeOk i s0 :=
      { pc := by rw [hpc]; exact (BitVec.add_zero (lsmpl.base 617)).symm
        run := hrun0
        inv := hCO
        argc := hargc
        spAligned := hal }
    have hpanicA : ∀ (sf : State) (Pf : SepProp), allocFailedIn s0 sf →
        ((sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ R)) :=
      fun _ _ ha => panic_of_mem (Or.inr ha)
    cases hcase with
    | usage hascii hshape =>
      have hfail : parseArgs uuidTryParse (i.argv.map bytesOfString) = none :=
        parseArgs_none_of_shape_proof uuidTryParse hascii hshape
      have hexit2 : ExitKPoolPlaced CodeOk H A lim s0 stk
          (fun code s => code = 2 ∧ s.trace = s0.trace ∧ s.fs = s0.fs)
          (fun sf Pf =>
            ((sf.mem ⊨ Pf ∗ R) →
              (sf.mem ⊨ (⌜MainPost (.ret 2 [] []) s0 sf⌝ ∗
                ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ anyHeap) ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf Pf =>
            (sf.mem ⊨ Pf ∗ R) →
              (sf.mem ⊨ (⌜(.ret 2 [] [] : MainResult) = .abort ∨ allocFailedIn s0 sf⌝ ∗
                anyHeap) ∗ R)) :=
        exitKPool_b2NeedLocks_tight_placed hneed hstk_frame
          fun code s ⟨hcode, htr_s, hfs_s⟩ sf htr_f hfs_f hx0 =>
            ⟨2, [], [], rfl,
              hx0.trans (congrArg (BitVec.ofNat 32) hcode),
              congrArg FsState.files (hfs_f.trans hfs_s),
              by rw [htr_f, htr_s, htr0]; exact traceStreamBytes_nil⟩
      refine step1 hst0 hs0 hok hpanicA
        (fun s st code hs ⟨hcode, _, htr_s, hfs_s⟩ => hexit2 s st code hs ⟨hcode, htr_s, hfs_s⟩) ?_
      intro s1 buf ps p0 st1 hst1 hne hps hs1
      refine step2 (p0 := p0) hst1 hok hne hps hs1 hpanicA
        (fun s' st code hs' ⟨hcode, _, htr_s, hfs_s⟩ =>
          hexit2 s' st code hs' ⟨hcode, htr_s, hfs_s⟩) ?_
      intro _ _ _ _ _ hpc_parse _
      exact (nomatch hfail.symm.trans hpc_parse)
    | stdinOverCap hover =>
      obtain ⟨⟨c0, hparse_c0, htag_c0⟩, hgt_stdin⟩ := hover
      refine step1 hst0 hs0 hok hpanicA ?_ ?_
      · intro s st code _ ⟨_, hnil, _, _⟩
        rw [hnil] at hparse_c0
        cases hparse_c0
      · intro s1 buf ps p0 st1 hst1 hne hps hs1
        refine step2 (p0 := p0) hst1 hok hne hps hs1 hpanicA ?_ ?_
        · intro s' st code _ ⟨_, hnone, _, _⟩
          rw [hnone] at hparse_c0
          cases hparse_c0
        · intro s2 w c st2 hst2 hpc_parse hs2
          have hc_eq : c = c0 := Option.some.inj (hpc_parse.symm.trans hparse_c0)
          subst hc_eq
          refine step3 hst2 hfs0 htr0 (hfacts.stdin i hok) hfacts.coinsPath
            (hfacts.coins i hok) hparse_c0 hs2 hpanicA ?_ ?_
          · refine exitKPool_b2NeedLocks_tight_placed hneed hstk_frame
              fun code s' ⟨hcode, hfiles', _, htr'⟩ sf htr_f hfs_f hx0 => ?_
            refine ⟨2, [], [], rfl,
              hx0.trans (congrArg (BitVec.ofNat 32) hcode), ?_, ?_⟩
            · rw [hfs_f, hfiles', hfs0]; rfl
            · rw [htr_f, htr', hs2.trace, htr0]
              exact traceStreamBytes_nil
          · intro _ _ _ _ _ _ _ hin_le _
            simp only [inputOf, htag_c0, ↓reduceIte] at hin_le
            omega
    | sendOverCap hover hnstin hcr =>
      obtain ⟨⟨peer, hparse_send⟩, hlen_gt⟩ := hover
      refine step1 hst0 hs0 hok hpanicA ?_ ?_
      · intro s st code _ ⟨_, hnil, _, _⟩
        rw [hnil] at hparse_send
        cases hparse_send
      · intro s1 buf ps p0 st1 hst1 hne hps hs1
        refine step2 (p0 := p0) hst1 hok hne hps hs1 hpanicA ?_ ?_
        · intro s' st code _ ⟨_, hnone, _, _⟩
          rw [hnone] at hparse_send
          cases hparse_send
        · intro s2 w c st2 hst2 hpc_parse hs2
          have hc_eq : c = .send peer := Option.some.inj (hpc_parse.symm.trans hparse_send)
          subst hc_eq
          refine step3 hst2 hfs0 htr0 (hfacts.stdin i hok) hfacts.coinsPath
            (hfacts.coins i hok) hparse_send hs2 hpanicA ?_ ?_
          · intro s' st code _ ⟨_, _, hex_or, _⟩
            rcases hex_or with hncr | ⟨htag, hgt⟩
            · exact absurd hcr hncr
            · exact absurd ⟨⟨.send peer, hparse_send, htag⟩, hgt⟩ hnstin
          · intro s3 coinsCap coinsPtr inCap inPtr st3 hst3 _ hs3
            refine step4_overCap hst3 hsp htr0 hparse_send hlen_gt hs3 hpanicA ?_
            refine exitKPool_b2NeedLocks_tight_placed hneed hstk_frame
              fun code s' ⟨hcode, hfiles', htr'⟩ sf htr_f hfs_f hx0 => ?_
            refine ⟨1, [], [], rfl,
              hx0.trans (congrArg (BitVec.ofNat 32) hcode), ?_, ?_⟩
            · rw [hfs_f, hfiles', hfs0]
              rfl
            · rw [htr_f, htr', hs3.trace, htr0]
              exact traceStreamBytes_nil
    | @call a hRun hnover hnstin hcr hco =>
      have hsome : (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome :=
        hparse i a hRun
      refine step1 hst0 hs0 hok hpanicA ?_ ?_
      · intro s st code _ ⟨_, hnil, _, _⟩
        rw [hnil] at hsome
        cases hsome
      · intro s1 buf ps p0 st1 hst1 hne hps hs1
        refine step2 (p0 := p0) hst1 hok hne hps hs1 hpanicA ?_ ?_
        · intro s' st code _ ⟨_, hnone, _, _⟩
          rw [hnone] at hsome
          cases hsome
        · intro s2 w c st2 hst2 hpc_parse hs2
          refine step3 hst2 hfs0 htr0 (hfacts.stdin i hok) hfacts.coinsPath
            (hfacts.coins i hok) hpc_parse hs2 hpanicA ?_ ?_
          · intro s' st code _ ⟨_, _, hex_or, _⟩
            rcases hex_or with hncr | ⟨htag, hgt⟩
            · exact absurd hcr hncr
            · exact absurd ⟨⟨c, hpc_parse, htag⟩, hgt⟩ hnstin
          · intro s3 coinsCap coinsPtr inCap inPtr st3 hst3 _ hs3
            refine step4_call hst3 hsp htr0 hRun hnover hpc_parse hs3 ?_ ?_ ?_
            · intro sf Pf hpan
              rcases hpan with rfl | ha
              · exact panic_of_mem (Or.inl rfl)
              · exact panic_of_mem (Or.inr ha)
            · refine exitKPool_b2NeedLocks_tight_placed hneed hstk_frame
                fun code s' ⟨hcode, ha_eq, ⟨hfiles', hstdout'⟩, _⟩ sf htr_f hfs_f hx0 => ?_
              subst ha_eq
              refine ⟨1, [], [], rfl,
                hx0.trans (congrArg (BitVec.ofNat 32) hcode), ?_, ?_⟩
              · rw [hfs_f, hfiles', hfs0]
                rfl
              · rw [htr_f, hstdout']
            · intro s4 g out st4 hst4 hans hwr _ hs4
              subst hans
              refine step5 hst4 htr0 hwr hs4.toAtM4EndPlaced hpanicA ?_
              · intro s5 ok outCap outPtr st5 hst5 hcommit htr45 hstdout5 hs5
                refine step6 hst5 hs5 ?_
                · refine exitKPool_b2NeedLocks_tight_placed hneed hstk_frame
                    fun code s6 ⟨hfiles6, hbr6⟩ sf htr_f hfs_f hx0 => ?_
                  rcases hs4.hist with ⟨hfiles4, hstdout4⟩
                  have hcf :
                      commitFiles io.wr (initFsState (cliInputs i)).files g.writes =
                        some (MainPost.writeAll (initFsState (cliInputs i))
                          (namedWrites g.writes)).files :=
                    hfacts.commit i hok g.writes (fun pw hpw => (hwr pw hpw).1) hco
                  rw [hfiles4, hcf] at hcommit
                  obtain ⟨hok_eq, hfiles5⟩ := hcommit
                  subst hok_eq
                  obtain ⟨hcode, _, hstdout6⟩ := hbr6
                  refine ⟨0, namedWrites g.writes, out, rfl,
                    hx0.trans (congrArg (BitVec.ofNat 32) hcode), ?_, ?_⟩
                  · rw [hfs_f, hfiles6, hfiles5, hfs0]
                  · rw [htr_f, hstdout6, hstdout5, hstdout4, List.nil_append]

theorem b2_main_ok_tight_needLocks_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {libcAddr : BitVec 64} {lim : BudgetLimits} {st0 : M.σ}
    {io : IoModel} {Run : Inputs → RunAnswer → Prop} {inputsOf : Inputs → ProcessInputs}
    {stk : Nat}
    (hfacts : MainIoFacts io)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hneed : ∀ (st' : M.σ) (sf : State),
      A.pool lim st' sf ⊢ ((libcAddr + 3#64) ↦₈ 0#8) ∗ anyHeap)
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hstk_frame : mainFrameSize ≤ stk)
    (step1 : ∀ {i : Inputs} {s0 : State} {Statics : SepProp} {Q Qp : State → SepProp → Prop}
      {oom : State → SepProp},
      AtEntryPlaced CodeOk i s0 →
      CliInputsOk i →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPoolPlaced CodeOk H A lim s0 stk
        (fun code s => code = 2 ∧ i.argv = [] ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp →
      (∀ (s : State) (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) (p0 : BitVec 64)
          (st1 : M.σ),
        i.argv ≠ [] → ps.map (·.2) = i.argv.map bytesOfString →
        AtM1EndPlaced CodeOk s0 s i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
          (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st1 s ∗ Statics)
          Q Qp oom) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0
        (b2MainFrameFine A lim st0 stk Statics i s0) Q Qp oom)
    (step2 : ∀ {i : Inputs} {s0 s : State} {buf p0 : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {st1 : M.σ} {Statics : SepProp}
      {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
      CliInputsOk i → i.argv ≠ [] →
      ps.map (·.2) = i.argv.map bytesOfString →
      AtM1EndPlaced CodeOk s0 s i.argv.length buf →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPoolPlaced CodeOk H A lim s0 stk
        (fun code s' => code = 2 ∧ parseArgs uuidTryParse (i.argv.map bytesOfString) = none ∧
          s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp →
      (∀ (s' : State) (w : CallW) (c : CallV) (st2 : M.σ),
        parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
        AtCallPlaced CodeOk s0 s' w i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st2 s' ∗ Statics)
          Q Qp oom) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st1 s ∗ Statics)
        Q Qp oom)
    (step3 : ∀ {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
      {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))} {st2 : M.σ}
      {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
      s0.fs = initFsState (cliInputs i) → s0.trace = [] →
      io.stdin (initFsState (cliInputs i)) = some i.stdin →
      io.pathOk (utf8 "coins") →
      (∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
        r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i)) →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s w i.argv.length buf →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPoolPlaced CodeOk H A lim s0 stk
        (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
          (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
        Q Qp →
      (∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64) (st3 : M.σ),
        (inputOf i c).length ≤ stdinCapBytes →
        AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
            ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st3 s' ∗ cliStaticsPlaced ∗ mainLitsBlk617)
          Q Qp oom) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st2 s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom)
    (step4_overCap : ∀ {i : Inputs} {peer : AddrV} {w : CallW} {s0 s : State}
      {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {st3 : M.σ} {Q Qp : State → SepProp → Prop},
      stk ≤ s0.sp.toNat →
      s0.trace = [] →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer) →
      1_000_000 < i.stdin.length →
      AtM4Placed CodeOk i s0 s w (.send peer) i.argv.length buf coinsCap coinsPtr inCap →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPoolPlaced CodeOk H A lim s0 stk
        (fun code s' => code = 1 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
          s'.trace = s.trace) Q Qp →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i (.send peer)).length)
            (inputOf i (.send peer)) ∗
          callHeap A.repAlloc w (.send peer) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st3 s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp (mainOom s0))
    (step4_call : ∀ {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
      {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {st3 : M.σ} {Q Qp : State → SepProp → Prop},
      stk ≤ s0.sp.toNat →
      s0.trace = [] →
      Run i a → ¬ IsSendOverCap i →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap →
      (∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf) →
      ExitKPoolPlaced CodeOk H A lim s0 stk
        (fun code s' => code = 1 ∧ a = some none ∧ HistOkTight i s' ∧
          s.trace <+: s'.trace) Q Qp →
      (∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)) (st4 : M.σ),
        a = some (some (namedWrites g.writes, out)) →
        (∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) → s.trace <+: s'.trace →
        AtM4EndTightPlaced CodeOk i s0 s' c i.argv.length buf inCap →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st4 s' ∗ anyHeap)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st3 s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp (mainOom s0))
    (step5 : ∀ {i : Inputs} {c : CallV} {g : StoresGhost} {out : List (BitVec 8)}
      {s0 s : State} {buf inCap inPtr : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
      {st4 : M.σ} {Q Qp : State → SepProp → Prop},
      s0.trace = [] →
      (∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) →
      AtM4EndPlaced CodeOk i s0 s c i.argv.length buf inCap →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      (∀ (s' : State) (ok : Bool) (outCap outPtr : BitVec 64) (st5 : M.σ),
        (match commitFiles io.wr s.fs.files g.writes with
         | some F => ok = true ∧ s'.fs.files = F
         | none => ok = false) →
        s.trace <+: s'.trace →
        ProcessOutcome.traceStreamBytes .stdout s'.trace =
          ProcessOutcome.traceStreamBytes .stdout s.trace →
        AtM6Placed CodeOk s0 s' ok i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
                (BitVec.ofNat 64 out.length) inCap inPtr) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st5 s' ∗ anyHeap)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st4 s ∗ anyHeap)
        Q Qp (mainOom s0))
    (step6 : ∀ {s0 s : State} {ok : Bool} {n : Nat}
      {buf outCap outPtr inCap inPtr : BitVec 64}
      {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))} {st5 : M.σ}
      {Q Qp : State → SepProp → Prop},
      AtM6Placed CodeOk s0 s ok n buf →
      ExitKPoolPlaced CodeOk H A lim s0 stk
        (fun code s' => s'.fs.files = s.fs.files ∧
          (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
              ProcessOutcome.traceStreamBytes .stdout s'.trace =
              ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
           else code = 2 ∧ s'.trace = s.trace)) Q Qp →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
              (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st5 s ∗ anyHeap)
        Q Qp (mainOom s0)) :
    subroutine_ok (mProgPlaced H) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk A lim st0 stk cliStaticsPlaced Run inputsOf) :=
  b2_main_ok_tight_needLocks_with_inv_placed
    (St0 := fun _ _ => True)
    (St1 := fun _ _ => True)
    (St2 := fun _ _ _ => True)
    (St3 := fun _ _ _ => True)
    (St4 := fun _ _ _ _ => True)
    (St5 := fun _ _ _ _ _ => True)
    hfacts hfs_eq hneed hparse hstk_frame (fun _ _ => trivial)
    (fun _ hs0 hok hp hex hn =>
      step1 hs0 hok hp hex fun s buf ps p0 st1 => hn s buf ps p0 st1 trivial)
    (fun _ hok hne hps hs1 hp hex hn =>
      step2 hok hne hps hs1 hp hex fun s' w c st2 => hn s' w c st2 trivial)
    (fun _ hfs0 htr0 hsin hcok hcs hpc hs2 hp hex hn =>
      step3 hfs0 htr0 hsin hcok hcs hpc hs2 hp hex
        fun s' coinsCap coinsPtr inCap inPtr st3 =>
          hn s' coinsCap coinsPtr inCap inPtr st3 trivial)
    (fun _ hsp htr0 hpc hlen hs3 hp hex =>
      step4_overCap hsp htr0 hpc hlen hs3 hp hex)
    (fun _ hsp htr0 hR hnover hpc hs3 hp hex hn =>
      step4_call hsp htr0 hR hnover hpc hs3 hp hex
        fun s' g out st4 => hn s' g out st4 trivial)
    (fun _ htr0 hwr hs4 hp hn =>
      step5 htr0 hwr hs4 hp
        fun s' ok outCap outPtr st5 => hn s' ok outCap outPtr st5 trivial)
    (fun _ hs5 hex => step6 hs5 hex)

/-! ## `fineHookRustCliAllocBudget` and `cliProgExtPlacedAt` instantiations -/

/-- Construct a `LibsignalPlacement` instance with `lsmpl = mpl` from block placeability and
distinct externs. -/
@[instance_reducible]
def libsignalPlacementOf (mpl : Obj.MultiPlacement)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext : (libsignalSessionExterns.map mpl.ρ).Nodup) : LibsignalPlacement where
  mpl := mpl
  block_placeable := hblk
  externsDistinct := hext

theorem mProgPlaced_eq_cliProgExtPlacedAt [LibsignalPlacement]
    (ext : CliHooks → String → Option (State → State)) (W : CliHooks) :
    mProgPlaced (ext W) = cliProgExtPlacedAt lsmpl ext 617 W :=
  IsLsBlockProg.eq_blockProgram (prog := lsProg_617 (ext W)) (i := 617) (H := ext W)

theorem fineHook_b2_main_ok_tight_needLocks_with_inv_placed_lsmpl [LibsignalPlacement]
    {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64}
    {St0 : Inputs → FineBudget → Prop}
    {St1 : Inputs → FineBudget → Prop}
    {St2 : Inputs → CallV → FineBudget → Prop}
    {St3 : Inputs → CallV → FineBudget → Prop}
    {St4 : Inputs → CallV → StoresGhost → FineBudget → Prop}
    {St5 : Inputs → CallV → StoresGhost → Bool → FineBudget → Prop}
    {io : IoModel} {Run : Inputs → RunAnswer → Prop} {inputsOf : Inputs → ProcessInputs}
    {stk : Nat}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfacts : MainIoFacts io)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hstk_frame : mainFrameSize ≤ stk)
    (hSt0 : ∀ i : Inputs, CliInputsOk i → St0 i fineCostModel.init)
    (step1 : ∀ {i : Inputs} {s0 : State} {Statics : SepProp} {Q Qp : State → SepProp → Prop}
      {oom : State → SepProp},
      let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
      St0 i fineCostModel.init →
      AtEntryPlaced CodeOk i s0 →
      CliInputsOk i →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPoolPlaced CodeOk (ext W) A lim s0 stk
        (fun code s => code = 2 ∧ i.argv = [] ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp →
      (∀ (s : State) (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) (p0 : BitVec 64)
          (st1 : FineBudget),
        St1 i st1 →
        i.argv ≠ [] → ps.map (·.2) = i.argv.map bytesOfString →
        AtM1EndPlaced CodeOk s0 s i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s
          (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st1 s ∗ Statics)
          Q Qp oom) →
      ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s0
        (b2MainFrameFine A lim fineCostModel.init stk Statics i s0) Q Qp oom)
    (step2 : ∀ {i : Inputs} {s0 s : State} {buf p0 : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {st1 : FineBudget} {Statics : SepProp}
      {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
      let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
      St1 i st1 →
      CliInputsOk i → i.argv ≠ [] →
      ps.map (·.2) = i.argv.map bytesOfString →
      AtM1EndPlaced CodeOk s0 s i.argv.length buf →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPoolPlaced CodeOk (ext W) A lim s0 stk
        (fun code s' => code = 2 ∧ parseArgs uuidTryParse (i.argv.map bytesOfString) = none ∧
          s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp →
      (∀ (s' : State) (w : CallW) (c : CallV) (st2 : FineBudget),
        St2 i c st2 →
        parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
        AtCallPlaced CodeOk s0 s' w i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s'
          (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st2 s' ∗ Statics)
          Q Qp oom) →
      ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s
        (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st1 s ∗ Statics)
        Q Qp oom)
    (step3 : ∀ {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
      {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))} {st2 : FineBudget}
      {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
      let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
      St2 i c st2 →
      s0.fs = initFsState (cliInputs i) → s0.trace = [] →
      io.stdin (initFsState (cliInputs i)) = some i.stdin →
      io.pathOk (utf8 "coins") →
      (∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
        r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i)) →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s w i.argv.length buf →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPoolPlaced CodeOk (ext W) A lim s0 stk
        (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
          (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
        Q Qp →
      (∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64) (st3 : FineBudget),
        St3 i c st3 →
        (inputOf i c).length ≤ stdinCapBytes →
        AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
        ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s'
          (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
            ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st3 s' ∗ cliStaticsPlaced ∗ mainLitsBlk617)
          Q Qp oom) →
      ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st2 s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom)
    (step4_overCap : ∀ {i : Inputs} {peer : AddrV} {w : CallW} {s0 s : State}
      {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {st3 : FineBudget}
      {Q Qp : State → SepProp → Prop},
      let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
      St3 i (.send peer) st3 →
      stk ≤ s0.sp.toNat →
      s0.trace = [] →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer) →
      1_000_000 < i.stdin.length →
      AtM4Placed CodeOk i s0 s w (.send peer) i.argv.length buf coinsCap coinsPtr inCap →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPoolPlaced CodeOk (ext W) A lim s0 stk
        (fun code s' => code = 1 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
          s'.trace = s.trace) Q Qp →
      ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i (.send peer)).length)
            (inputOf i (.send peer)) ∗
          callHeap A.repAlloc w (.send peer) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st3 s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp (mainOom s0))
    (step4_call : ∀ {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
      {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {st3 : FineBudget}
      {Q Qp : State → SepProp → Prop},
      let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
      St3 i c st3 →
      stk ≤ s0.sp.toNat →
      s0.trace = [] →
      Run i a → ¬ IsSendOverCap i →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap →
      (∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf) →
      ExitKPoolPlaced CodeOk (ext W) A lim s0 stk
        (fun code s' => code = 1 ∧ a = some none ∧ HistOkTight i s' ∧
          s.trace <+: s'.trace) Q Qp →
      (∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)) (st4 : FineBudget),
        St4 i c g st4 →
        a = some (some (namedWrites g.writes, out)) →
        (∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) → s.trace <+: s'.trace →
        AtM4EndTightPlaced CodeOk i s0 s' c i.argv.length buf inCap →
        ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s'
          (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st4 s' ∗ anyHeap)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st3 s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp (mainOom s0))
    (step5 : ∀ {i : Inputs} {c : CallV} {g : StoresGhost} {out : List (BitVec 8)}
      {s0 s : State} {buf inCap inPtr : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
      {st4 : FineBudget} {Q Qp : State → SepProp → Prop},
      let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
      St4 i c g st4 →
      s0.trace = [] →
      (∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) →
      AtM4EndPlaced CodeOk i s0 s c i.argv.length buf inCap →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      (∀ (s' : State) (ok : Bool) (outCap outPtr : BitVec 64) (st5 : FineBudget),
        St5 i c g ok st5 →
        (match commitFiles io.wr s.fs.files g.writes with
         | some F => ok = true ∧ s'.fs.files = F
         | none => ok = false) →
        s.trace <+: s'.trace →
        ProcessOutcome.traceStreamBytes .stdout s'.trace =
          ProcessOutcome.traceStreamBytes .stdout s.trace →
        AtM6Placed CodeOk s0 s' ok i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s'
          (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
                (BitVec.ofNat 64 out.length) inCap inPtr) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st5 s' ∗ anyHeap)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s
        (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st4 s ∗ anyHeap)
        Q Qp (mainOom s0))
    (step6 : ∀ {i : Inputs} {c : CallV} {g : StoresGhost} {s0 s : State} {ok : Bool}
      {buf outCap outPtr inCap inPtr : BitVec 64}
      {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))} {st5 : FineBudget}
      {Q Qp : State → SepProp → Prop},
      let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
      St5 i c g ok st5 →
      AtM6Placed CodeOk s0 s ok i.argv.length buf →
      ExitKPoolPlaced CodeOk (ext W) A lim s0 stk
        (fun code s' => s'.fs.files = s.fs.files ∧
          (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
              ProcessOutcome.traceStreamBytes .stdout s'.trace =
              ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
           else code = 2 ∧ s'.trace = s.trace)) Q Qp →
      ProofLib.SepWPp (mProgPlaced (ext W)) (s0.readReg64 .lr) s
        (ownedBytes A.repAlloc outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
              (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st5 s ∗ anyHeap)
        Q Qp (mainOom s0)) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init stk (cliStaticsPlacedAt lsmpl) Run inputsOf) := by
  rw [← mProgPlaced_eq_cliProgExtPlacedAt ext W, cliStaticsPlacedAt_eq_cliStaticsPlaced]
  have hneed : ∀ (st' : FineBudget) (sf : State),
      (fineHookRustCliAllocBudget γ mmpl tp brkStart).pool lim st' sf ⊢
        ((libcAddr + 3#64) ↦₈ 0#8) ∗ anyHeap := by
    intro st' sf
    rw [hlibc]
    exact hookPool_entails_needLocks_anyHeap γ mmpl tp brkStart lim st' sf
  exact b2_main_ok_tight_needLocks_with_inv_placed hfacts hfs_eq hneed hparse hstk_frame hSt0
    step1 step2 step3 step4_overCap step4_call step5 step6

end LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
