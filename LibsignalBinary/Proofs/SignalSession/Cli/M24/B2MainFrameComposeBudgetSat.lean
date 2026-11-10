/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.PoolNeedLocks
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1PlacedRoBudgetSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

/-!
# SWAR-Padded Route-B2 `b2MainSpecTightNeedLocksFineAtPad` Hop & Process Composition

- **Role**: `Role::Proof` (outside the TCB).
- **Overview**:
  Additive SWAR-padded sibling of `B2MainFrameComposeBudget` and the `579 → 617` lifts in
  `MainOkCliExtB2NeedLocksInst`:
  - `sepWPp_argvAtROPPad_to_unpadded_needLocks`: peels the SWAR read-ahead pad at the `M1 → M2`
    boundary and absorbs it into `anyHeap` on return and panic so `M2..M6` (`B2MainRemainingHops`)
    run unchanged;
  - `b2_main_ok_tight_needLocks_with_inv_placed_pad`: composes `M1` over `b2MainFrameFinePad` /
    `argvAtROPPad` with `M2..M6` into `b2MainSpecTightNeedLocksFineAtPad`;
  - `b2MainSpecTightNeedLocksFineAtPad_of_*_sat`: `579 → 617` lifts consuming only
    `HookSat (ext W) "strlen" (strlenSpecROSat hookStack)` on `step1` (zero `strlenHook`).
-/

public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudgetSat

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement LibsignalRoLoaded libsignalMutatedBlocks
   libsignalSessionExterns lsmpl)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (allocFailedIn)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs libsignalSessionLib stdinCapBytes)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk CoinsReadable IsSendOverCap IsStdinOverCap MainCaseB2 MainGhost MainPost MainResult
   RunAnswer StoresGhost cliInputs cliStaticsPlaced utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AtCallPlaced AtEntryPlaced AtM1EndPlaced AtM4EndPlaced AtM4EndTightPlaced AtM4Placed
   AtM6Placed CallV CallW HistOkTight IoModel LsCodeInv MainIoFacts RunCall argsBuf
   callCellsPlaced callHeap cliIo cliIo_coins cliIo_coinsPath cliIo_commit cliIo_stdin cliMainStk
   cliResStack cliWrOk cli_hstk64 coinsOf commitFiles hparse_of_domains inputOf locals
   m4CellsPlaced m5CellsPlaced m6CellsPlaced mProgPlaced mainFrameSize mainLitsBlk617
   mainLitsPlaced_of_roLoaded mainOom mainSaved namedWrites ownedBytes parseArgs
   parseArgs_none_of_shape_proof)
open CryptoVerification.SignalSession.Cli.MainHops.MainOkPlacedHelpers
  (panic_of_mem traceStreamBytes_nil)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runRel)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget rustAllocEvents)
open LibsignalBinary.Heap.Fine
  (FineBudget fineCostModel fineHookRustCliAllocBudget hookPool_entails_needLocks_anyHeap)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad
  (argvAtROPPad argvAtROPPad_entails_argvAtROP_frame b2MainFrameFinePad
   b2MainSpecTightNeedLocksFineAtPad sepWPp_forget_frame strlenSpecROSat)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
  (argvAtROP exitKPool_b2NeedLocks_tight_placed libsignalPlacementOf
   mProgPlaced_eq_cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
  (B2MainEntryFacts cliStaticsPlacedAt cliStaticsPlacedAt_eq_cliStaticsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
  (domScopedRun domScopedRun_dom)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
  (B2MainRemainingHops mainFrameSize_le_cliMainStk pqScopedRun
   subroutine_ok_runSpecTightPlaced_mono_run)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1PlacedRoBudgetSat
  (main_m1_ro_pool_placed_step1_of_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget (ExitKPoolPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-! ## 1. `b2MainFrameFinePad` RoLiterals Lift & `M1 → M2` Pad-Peeling Continuation Bridge -/

theorem sepWPp_b2MainFrameFinePad_mainLitsPlaced [LibsignalPlacement] {prog : Program}
    {ret : BitVec 64} {s : State} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {stk : Nat} {Statics : SepProp} {i : Inputs}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hwp : SepWPp prog ret s
      (b2MainFrameFinePad A lim st stk (Statics ∗ mainLitsBlk617) i s) Q Qp oom) :
    SepWPp prog ret s (b2MainFrameFinePad A lim st stk Statics i s) Q Qp oom := by
  intro R hm
  apply hwp R
  have h := mainLitsPlaced_of_roLoaded hro hm
  refine Satisfies.of_eq h ?_
  simp only [b2MainFrameFinePad]
  sep_ac_rfl

private theorem sepWPp_mono_q_qp {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q₁ Q₂ Qp₁ Qp₂ : State → SepProp → Prop} {oom : State → SepProp}
    (hQ : ∀ sf Pf, Q₁ sf Pf → Q₂ sf Pf)
    (hQp : ∀ sf Pf, Qp₁ sf Pf → Qp₂ sf Pf)
    (hwp : SepWPp prog ret s P Q₁ Qp₁ oom) :
    SepWPp prog ret s P Q₂ Qp₂ oom := by
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, Pf, hmf, hq⟩ | ⟨hpan, Pf, hmf, hqp⟩ | hoom
  · exact Or.inl ⟨hpc, hrun, Pf, hmf, hQ sf Pf hq⟩
  · exact Or.inr (Or.inl ⟨hpan, Pf, hmf, hQp sf Pf hqp⟩)
  · exact Or.inr (Or.inr hoom)

private theorem sepWPp_of_entails_exists {prog : Program} {ret : BitVec 64} {s : State}
    {P₁ : SepProp} {P₂ : SepProp → SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hent : P₁ ⊢ ∃∗ Rpad : SepProp, P₂ Rpad)
    (hk : ∀ Rpad : SepProp, SepWPp prog ret s (P₂ Rpad) Q Qp oom) :
    SepWPp prog ret s P₁ Q Qp oom := by
  intro R hm hL
  have hm' := Satisfies.mono (sepConj_mono_left hent) hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm'
  rcases hm' with ⟨Rpad, hmR⟩
  exact hk Rpad R hmR hL

/-- Peel the SWAR read-ahead pad out of `argvAtROPPad` at the `M1 → M2` continuation boundary and
absorb it into `anyHeap` in the `NeedLocks` normal-return and panic postconditions, so `M2..M6` run
unchanged over `argvAtROP`. -/
theorem sepWPp_argvAtROPPad_to_unpadded_needLocks {prog : Program}
    {libcAddr : BitVec 64} {r : MainResult} {s0 s1 : State} {stk : Nat}
    {x1 : BitVec 64} {ps_all : List (BitVec 64 × List (BitVec 8))}
    {PreA Rest R : SepProp}
    (hk : ∀ R' : SepProp,
      SepWPp prog (s0.readReg64 .lr) s1
        (PreA ∗ argvAtROP x1 ps_all ∗ Rest)
        (fun sf Pf =>
          ((sf.mem ⊨ Pf ∗ R') →
            (sf.mem ⊨ (⌜MainPost r s0 sf⌝ ∗
              ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ anyHeap) ∗ R')) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf Pf =>
          (sf.mem ⊨ Pf ∗ R') →
            (sf.mem ⊨ (⌜r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ R'))
        (mainOom s0)) :
    SepWPp prog (s0.readReg64 .lr) s1
      (PreA ∗ argvAtROPPad x1 ps_all ∗ Rest)
      (fun sf Pf =>
        ((sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜MainPost r s0 sf⌝ ∗
            ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ anyHeap) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ R))
      (mainOom s0) := by
  have hent :
      PreA ∗ argvAtROPPad x1 ps_all ∗ Rest ⊢
        ∃∗ Rpad : SepProp, (PreA ∗ argvAtROP x1 ps_all ∗ Rest) ∗ Rpad := by
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left (argvAtROPPad_entails_argvAtROP_frame x1 ps_all))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim
    intro Rpad
    exact Entails.sepExists_right Rpad (Entails.of_eq (by sep_ac_rfl))
  refine sepWPp_of_entails_exists hent fun Rpad => ?_
  refine sepWPp_forget_frame
    (fun _ => by dsimp only [mainOom]; exact Entails.pure_left False.elim) ?_
  refine sepWPp_mono_q_qp ?_ ?_ (hk (Rpad ∗ R))
  · intro sf Pf ⟨hpost, hsp, hcs⟩
    refine ⟨fun hm => ?_, hsp, hcs⟩
    rw [sepConj_assoc] at hm
    have hm' := hpost hm
    have eq1 :
        ((⌜MainPost r s0 sf⌝ ∗ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ anyHeap) ∗
          (Rpad ∗ R)) =
        (⌜MainPost r s0 sf⌝ ∗ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗
          (anyHeap ∗ Rpad)) ∗ R := by
      sep_ac_rfl
    rw [eq1] at hm'
    exact Satisfies.mono
      (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (entails_anyHeap _)))))
      hm'
  · intro sf Pf hpan hm
    rw [sepConj_assoc] at hm
    have hm' := hpan hm
    have eq1 :
        ((⌜r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ (Rpad ∗ R)) =
        (⌜r = .abort ∨ allocFailedIn s0 sf⌝ ∗ (anyHeap ∗ Rpad)) ∗ R := by
      sep_ac_rfl
    rw [eq1] at hm'
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))) hm'

/-! ## 2. Invariant-Threaded `b2MainSpecTightNeedLocksFineAtPad` Hop Composer (`Block 617`) -/

/-- SWAR-padded sibling of `B2MainFrameComposeBudget.b2_main_ok_tight_needLocks_with_inv_placed`:
`step1` runs over `b2MainFrameFinePad` / `argvAtROPPad`, `sepWPp_argvAtROPPad_to_unpadded_needLocks`
peels the SWAR pad at `M1 → M2`, and `step2..step6` run over unchanged `argvAtROP`. -/
theorem b2_main_ok_tight_needLocks_with_inv_placed_pad [LibsignalPlacement] {CodeOk : Memory → Prop}
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
            argvAtROPPad (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st1 s ∗ Statics)
          Q Qp oom) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0
        (b2MainFrameFinePad A lim st0 stk Statics i s0) Q Qp oom)
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
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk A lim st0 stk cliStaticsPlaced Run
        inputsOf) := by
  apply subroutine_ok_of_sepWPp_init
  intro ⟨i, r⟩ R s0 hpc hrun0 hpre hal
  simp only [b2MainSpecTightNeedLocksFineAtPad, B2MainEntryFacts, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hCO, hcase, hok, ⟨hargc, hfs0_in, htr0⟩, hsp⟩, hm⟩ := hpre
  have hfs0 : s0.fs = initFsState (cliInputs i) := hfs0_in.trans (hfs_eq i)
  have hst0 : St0 i st0 := hSt0 i hok
  refine ⟨b2MainFrameFinePad A lim st0 stk cliStaticsPlaced i s0, ?_, ?_⟩
  · simpa only [b2MainFrameFinePad, sepConj_assoc] using hm
  · apply sepWPp_b2MainFrameFinePad_mainLitsPlaced (hCI.toRoCl hCO).2
    change SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0
      (b2MainFrameFinePad A lim st0 stk (cliStaticsPlaced ∗ mainLitsBlk617) i s0)
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
    have hpanicA : ∀ (R' : SepProp) (sf : State) (Pf : SepProp), allocFailedIn s0 sf →
        ((sf.mem ⊨ Pf ∗ R') →
          (sf.mem ⊨ (⌜r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ R')) :=
      fun _ _ _ ha => panic_of_mem (Or.inr ha)
    cases hcase with
    | usage hascii hshape =>
      have hfail : parseArgs uuidTryParse (i.argv.map bytesOfString) = none :=
        parseArgs_none_of_shape_proof uuidTryParse hascii hshape
      have hexit2 : ∀ (R' : SepProp), ExitKPoolPlaced CodeOk H A lim s0 stk
          (fun code s => code = 2 ∧ s.trace = s0.trace ∧ s.fs = s0.fs)
          (fun sf Pf =>
            ((sf.mem ⊨ Pf ∗ R') →
              (sf.mem ⊨ (⌜MainPost (.ret 2 [] []) s0 sf⌝ ∗
                ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ anyHeap) ∗ R')) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf Pf =>
            (sf.mem ⊨ Pf ∗ R') →
              (sf.mem ⊨ (⌜(.ret 2 [] [] : MainResult) = .abort ∨ allocFailedIn s0 sf⌝ ∗
                anyHeap) ∗ R')) :=
        fun _ => exitKPool_b2NeedLocks_tight_placed hneed hstk_frame
          fun code s ⟨hcode, htr_s, hfs_s⟩ sf htr_f hfs_f hx0 =>
            ⟨2, [], [], rfl,
              hx0.trans (congrArg (BitVec.ofNat 32) hcode),
              congrArg FsState.files (hfs_f.trans hfs_s),
              by rw [htr_f, htr_s, htr0]; exact traceStreamBytes_nil⟩
      refine step1 hst0 hs0 hok (hpanicA R)
        (fun s st code hs ⟨hcode, _, htr_s, hfs_s⟩ => hexit2 R s st code hs ⟨hcode, htr_s, hfs_s⟩)
        ?_
      intro s1 buf ps p0 st1 hst1 hne hps hs1
      refine sepWPp_argvAtROPPad_to_unpadded_needLocks fun R' => ?_
      refine step2 (p0 := p0) hst1 hok hne hps hs1 (hpanicA R')
        (fun s' st code hs' ⟨hcode, _, htr_s, hfs_s⟩ =>
          hexit2 R' s' st code hs' ⟨hcode, htr_s, hfs_s⟩) ?_
      intro _ _ _ _ _ hpc_parse _
      exact (nomatch hfail.symm.trans hpc_parse)
    | stdinOverCap hover =>
      obtain ⟨⟨c0, hparse_c0, htag_c0⟩, hgt_stdin⟩ := hover
      refine step1 hst0 hs0 hok (hpanicA R) ?_ ?_
      · intro s st code _ ⟨_, hnil, _, _⟩
        rw [hnil] at hparse_c0
        cases hparse_c0
      · intro s1 buf ps p0 st1 hst1 hne hps hs1
        refine sepWPp_argvAtROPPad_to_unpadded_needLocks fun R' => ?_
        refine step2 (p0 := p0) hst1 hok hne hps hs1 (hpanicA R') ?_ ?_
        · intro s' st code _ ⟨_, hnone, _, _⟩
          rw [hnone] at hparse_c0
          cases hparse_c0
        · intro s2 w c st2 hst2 hpc_parse hs2
          have hc_eq : c = c0 := Option.some.inj (hpc_parse.symm.trans hparse_c0)
          subst hc_eq
          refine step3 hst2 hfs0 htr0 (hfacts.stdin i hok) hfacts.coinsPath
            (hfacts.coins i hok) hparse_c0 hs2 (hpanicA R') ?_ ?_
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
      refine step1 hst0 hs0 hok (hpanicA R) ?_ ?_
      · intro s st code _ ⟨_, hnil, _, _⟩
        rw [hnil] at hparse_send
        cases hparse_send
      · intro s1 buf ps p0 st1 hst1 hne hps hs1
        refine sepWPp_argvAtROPPad_to_unpadded_needLocks fun R' => ?_
        refine step2 (p0 := p0) hst1 hok hne hps hs1 (hpanicA R') ?_ ?_
        · intro s' st code _ ⟨_, hnone, _, _⟩
          rw [hnone] at hparse_send
          cases hparse_send
        · intro s2 w c st2 hst2 hpc_parse hs2
          have hc_eq : c = .send peer := Option.some.inj (hpc_parse.symm.trans hparse_send)
          subst hc_eq
          refine step3 hst2 hfs0 htr0 (hfacts.stdin i hok) hfacts.coinsPath
            (hfacts.coins i hok) hparse_send hs2 (hpanicA R') ?_ ?_
          · intro s' st code _ ⟨_, _, hex_or, _⟩
            rcases hex_or with hncr | ⟨htag, hgt⟩
            · exact absurd hcr hncr
            · exact absurd ⟨⟨.send peer, hparse_send, htag⟩, hgt⟩ hnstin
          · intro s3 coinsCap coinsPtr inCap inPtr st3 hst3 _ hs3
            refine step4_overCap hst3 hsp htr0 hparse_send hlen_gt hs3 (hpanicA R') ?_
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
      refine step1 hst0 hs0 hok (hpanicA R) ?_ ?_
      · intro s st code _ ⟨_, hnil, _, _⟩
        rw [hnil] at hsome
        cases hsome
      · intro s1 buf ps p0 st1 hst1 hne hps hs1
        refine sepWPp_argvAtROPPad_to_unpadded_needLocks fun R' => ?_
        refine step2 (p0 := p0) hst1 hok hne hps hs1 (hpanicA R') ?_ ?_
        · intro s' st code _ ⟨_, hnone, _, _⟩
          rw [hnone] at hsome
          cases hsome
        · intro s2 w c st2 hst2 hpc_parse hs2
          refine step3 hst2 hfs0 htr0 (hfacts.stdin i hok) hfacts.coinsPath
            (hfacts.coins i hok) hpc_parse hs2 (hpanicA R') ?_ ?_
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
              refine step5 hst4 htr0 hwr hs4.toAtM4EndPlaced (hpanicA R') ?_
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

/-! ## 3. `579 → 617` `HookSat` Lifts (`b2MainSpecTightNeedLocksFineAtPad_of_*_sat`, Zero `strlenHook`) -/

/-- `HookSat (ext W) "strlen" (strlenSpecROSat hookStack)` sibling of
`MainOkCliExtB2NeedLocksInst.b2MainSpecTightNeedLocksFineAt_of_runTight_lsmpl`:
consumes zero `strlenHook` premises when supplied a `B2MainRemainingHops` bundle. -/
theorem b2MainSpecTightNeedLocksFineAtPad_of_runTight_lsmpl_sat [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {St0 : Inputs → FineBudget → Prop}
    {St1 : Inputs → FineBudget → Prop}
    {St2 : Inputs → CallV → FineBudget → Prop}
    {St3 : Inputs → CallV → FineBudget → Prop}
    {St4 : Inputs → CallV → StoresGhost → FineBudget → Prop}
    {St5 : Inputs → CallV → StoresGhost → Bool → FineBudget → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop} {inputsOf : Inputs → ProcessInputs}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hstrlenRO : HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hc_alloc : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hSt0 : ∀ i : Inputs, CliInputsOk i → St0 i fineCostModel.init)
    (hSt01 : ∀ {i : Inputs}, CliInputsOk i → St0 i fineCostModel.init → i.argv ≠ [] →
      FitsEvents fineCostModel lim fineCostModel.init (rustAllocEvents (16 * i.argv.length) 8) ∧
        St1 i (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init))
    (hrun : subroutine_ok (mProgPlaced (ext W)) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse Run cliWrOk cliResStack))
    (hhops : B2MainRemainingHops CodeOk mmpl ext W brkStart lim γ tp
      St1 St2 St3 St4 St5 RunEnv Run) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl) Run inputsOf) := by
  subst hlibc
  rw [← mProgPlaced_eq_cliProgExtPlacedAt ext W, cliStaticsPlacedAt_eq_cliStaticsPlaced]
  exact b2_main_ok_tight_needLocks_with_inv_placed_pad
    ⟨cliIo_stdin, cliIo_coinsPath, cliIo_coins, cliIo_commit⟩ hfs_eq
    (fun st' sf => hookPool_entails_needLocks_anyHeap γ mmpl tp brkStart lim st' sf)
    hparse mainFrameSize_le_cliMainStk hSt0
    (fun hst0 hs0 hok hpanic hexit hnext =>
      main_m1_ro_pool_placed_step1_of_sat hc_alloc hstrlenRO hstk cli_hstk64 hSt01
        hst0 hs0 hok hpanic hexit hnext)
    hhops.step2 hhops.step3 hhops.step4_overCap (hhops.step4_call hrun) hhops.step5 hhops.step6

/-- `runRel S` specialization of `b2MainSpecTightNeedLocksFineAtPad_of_runTight_lsmpl_sat`. -/
theorem b2MainSpecTightNeedLocksFineAtPad_of_runSem_lsmpl_sat [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {St0 : Inputs → FineBudget → Prop}
    {St1 : Inputs → FineBudget → Prop}
    {St2 : Inputs → CallV → FineBudget → Prop}
    {St3 : Inputs → CallV → FineBudget → Prop}
    {St4 : Inputs → CallV → StoresGhost → FineBudget → Prop}
    {St5 : Inputs → CallV → StoresGhost → Bool → FineBudget → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hstrlenRO : HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hc_alloc : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hSt0 : ∀ i : Inputs, CliInputsOk i → St0 i fineCostModel.init)
    (hSt01 : ∀ {i : Inputs}, CliInputsOk i → St0 i fineCostModel.init → i.argv ≠ [] →
      FitsEvents fineCostModel lim fineCostModel.init (rustAllocEvents (16 * i.argv.length) 8) ∧
        St1 i (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init))
    (hrun : subroutine_ok (mProgPlaced (ext W)) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse (runRel S) cliWrOk cliResStack))
    (hhops : B2MainRemainingHops CodeOk mmpl ext W brkStart lim γ tp
      St1 St2 St3 St4 St5 RunEnv (runRel S)) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl) (runRel S) inputsOf) :=
  b2MainSpecTightNeedLocksFineAtPad_of_runTight_lsmpl_sat hlibc hfs_eq
    (hparse_of_domains fun _ _ hr => domScopedRun_dom (Dom := fun _ => True) ⟨trivial, hr⟩)
    hstrlenRO hc_alloc hstk hSt0 hSt01 hrun hhops

/-- Explicit-`mpl` specialization of `b2MainSpecTightNeedLocksFineAtPad_of_runSem_lsmpl_sat`. -/
theorem b2MainSpecTightNeedLocksFineAtPad_of_runSem_placed_sat
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {St0 : Inputs → FineBudget → Prop}
    {St1 : Inputs → FineBudget → Prop}
    {St2 : Inputs → CallV → FineBudget → Prop}
    {St3 : Inputs → CallV → FineBudget → Prop}
    {St4 : Inputs → CallV → StoresGhost → FineBudget → Prop}
    {St5 : Inputs → CallV → StoresGhost → Bool → FineBudget → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hstrlenRO : HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hc_alloc : @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hSt0 : ∀ i : Inputs, CliInputsOk i → St0 i fineCostModel.init)
    (hSt01 : ∀ {i : Inputs}, CliInputsOk i → St0 i fineCostModel.init → i.argv ≠ [] →
      FitsEvents fineCostModel lim fineCostModel.init (rustAllocEvents (16 * i.argv.length) 8) ∧
        St1 i (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init))
    (hrun : @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
      (mpl.base 579)
      (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse (runRel S)
        cliWrOk cliResStack))
    (hhops : @B2MainRemainingHops (libsignalPlacementOf mpl hblk hext_nodup)
      CodeOk mmpl ext W brkStart lim γ tp St1 St2 St3 St4 St5 RunEnv (runRel S)) :
    subroutine_ok (cliProgExtPlacedAt mpl ext 617 W) (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl) (runRel S) inputsOf) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  exact b2MainSpecTightNeedLocksFineAtPad_of_runSem_lsmpl_sat S hlibc hfs_eq hstrlenRO
    hc_alloc hstk hSt0 hSt01 hrun hhops

/-- `domScopedRun Dom (runRel S)` specialization of
`b2MainSpecTightNeedLocksFineAtPad_of_runTight_lsmpl_sat`. -/
theorem b2MainSpecTightNeedLocksFineAtPad_of_domScopedRunSem_lsmpl_sat [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {St0 : Inputs → FineBudget → Prop}
    {St1 : Inputs → FineBudget → Prop}
    {St2 : Inputs → CallV → FineBudget → Prop}
    {St3 : Inputs → CallV → FineBudget → Prop}
    {St4 : Inputs → CallV → StoresGhost → FineBudget → Prop}
    {St5 : Inputs → CallV → StoresGhost → Bool → FineBudget → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (Dom : Inputs → Prop) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hstrlenRO : HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hc_alloc : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hSt0 : ∀ i : Inputs, CliInputsOk i → St0 i fineCostModel.init)
    (hSt01 : ∀ {i : Inputs}, CliInputsOk i → St0 i fineCostModel.init → i.argv ≠ [] →
      FitsEvents fineCostModel lim fineCostModel.init (rustAllocEvents (16 * i.argv.length) 8) ∧
        St1 i (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init))
    (hrun : subroutine_ok (mProgPlaced (ext W)) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse (runRel S) cliWrOk cliResStack))
    (hhops : B2MainRemainingHops CodeOk mmpl ext W brkStart lim γ tp
      St1 St2 St3 St4 St5 RunEnv (domScopedRun Dom (runRel S))) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl)
        (domScopedRun Dom (runRel S)) inputsOf) :=
  b2MainSpecTightNeedLocksFineAtPad_of_runTight_lsmpl_sat hlibc hfs_eq
    (hparse_of_domains fun _ _ hr => domScopedRun_dom hr) hstrlenRO hc_alloc hstk hSt0 hSt01
    (subroutine_ok_runSpecTightPlaced_mono_run (fun _ _ h => h.2) hrun) hhops

/-- Explicit-`mpl` specialization of
`b2MainSpecTightNeedLocksFineAtPad_of_domScopedRunSem_lsmpl_sat`. -/
theorem b2MainSpecTightNeedLocksFineAtPad_of_domScopedRunSem_placed_sat
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {St0 : Inputs → FineBudget → Prop}
    {St1 : Inputs → FineBudget → Prop}
    {St2 : Inputs → CallV → FineBudget → Prop}
    {St3 : Inputs → CallV → FineBudget → Prop}
    {St4 : Inputs → CallV → StoresGhost → FineBudget → Prop}
    {St5 : Inputs → CallV → StoresGhost → Bool → FineBudget → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (Dom : Inputs → Prop) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hstrlenRO : HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hc_alloc : @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hSt0 : ∀ i : Inputs, CliInputsOk i → St0 i fineCostModel.init)
    (hSt01 : ∀ {i : Inputs}, CliInputsOk i → St0 i fineCostModel.init → i.argv ≠ [] →
      FitsEvents fineCostModel lim fineCostModel.init (rustAllocEvents (16 * i.argv.length) 8) ∧
        St1 i (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init))
    (hrun : @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
      (mpl.base 579)
      (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse (runRel S)
        cliWrOk cliResStack))
    (hhops : @B2MainRemainingHops (libsignalPlacementOf mpl hblk hext_nodup)
      CodeOk mmpl ext W brkStart lim γ tp St1 St2 St3 St4 St5 RunEnv
      (domScopedRun Dom (runRel S))) :
    subroutine_ok (cliProgExtPlacedAt mpl ext 617 W) (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
        (domScopedRun Dom (runRel S)) inputsOf) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  exact b2MainSpecTightNeedLocksFineAtPad_of_domScopedRunSem_lsmpl_sat Dom S hlibc hfs_eq
    hstrlenRO hc_alloc hstk hSt0 hSt01 hrun hhops

/-- `pqScopedRun WP (runRel S)` specialization of
`b2MainSpecTightNeedLocksFineAtPad_of_runTight_lsmpl_sat`. -/
theorem b2MainSpecTightNeedLocksFineAtPad_of_pqScopedRunSem_lsmpl_sat [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {St0 : Inputs → FineBudget → Prop}
    {St1 : Inputs → FineBudget → Prop}
    {St2 : Inputs → CallV → FineBudget → Prop}
    {St3 : Inputs → CallV → FineBudget → Prop}
    {St4 : Inputs → CallV → StoresGhost → FineBudget → Prop}
    {St5 : Inputs → CallV → StoresGhost → Bool → FineBudget → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (WP : PEParams) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hstrlenRO : HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hc_alloc : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hSt0 : ∀ i : Inputs, CliInputsOk i → St0 i fineCostModel.init)
    (hSt01 : ∀ {i : Inputs}, CliInputsOk i → St0 i fineCostModel.init → i.argv ≠ [] →
      FitsEvents fineCostModel lim fineCostModel.init (rustAllocEvents (16 * i.argv.length) 8) ∧
        St1 i (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init))
    (hrun : subroutine_ok (mProgPlaced (ext W)) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse (runRel S) cliWrOk cliResStack))
    (hhops : B2MainRemainingHops CodeOk mmpl ext W brkStart lim γ tp
      St1 St2 St3 St4 St5 RunEnv (pqScopedRun WP (runRel S))) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl)
        (pqScopedRun WP (runRel S)) inputsOf) :=
  b2MainSpecTightNeedLocksFineAtPad_of_domScopedRunSem_lsmpl_sat (CliPqxdhInputs WP) S hlibc hfs_eq
    hstrlenRO hc_alloc hstk hSt0 hSt01 hrun hhops

/-- Explicit-`mpl` specialization of
`b2MainSpecTightNeedLocksFineAtPad_of_pqScopedRunSem_lsmpl_sat`. -/
theorem b2MainSpecTightNeedLocksFineAtPad_of_pqScopedRunSem_placed_sat
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {St0 : Inputs → FineBudget → Prop}
    {St1 : Inputs → FineBudget → Prop}
    {St2 : Inputs → CallV → FineBudget → Prop}
    {St3 : Inputs → CallV → FineBudget → Prop}
    {St4 : Inputs → CallV → StoresGhost → FineBudget → Prop}
    {St5 : Inputs → CallV → StoresGhost → Bool → FineBudget → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (WP : PEParams) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hstrlenRO : HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hc_alloc : @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hSt0 : ∀ i : Inputs, CliInputsOk i → St0 i fineCostModel.init)
    (hSt01 : ∀ {i : Inputs}, CliInputsOk i → St0 i fineCostModel.init → i.argv ≠ [] →
      FitsEvents fineCostModel lim fineCostModel.init (rustAllocEvents (16 * i.argv.length) 8) ∧
        St1 i (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init))
    (hrun : @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
      (mpl.base 579)
      (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse (runRel S)
        cliWrOk cliResStack))
    (hhops : @B2MainRemainingHops (libsignalPlacementOf mpl hblk hext_nodup)
      CodeOk mmpl ext W brkStart lim γ tp St1 St2 St3 St4 St5 RunEnv
      (pqScopedRun WP (runRel S))) :
    subroutine_ok (cliProgExtPlacedAt mpl ext 617 W) (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
        (pqScopedRun WP (runRel S)) inputsOf) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  exact b2MainSpecTightNeedLocksFineAtPad_of_pqScopedRunSem_lsmpl_sat WP S hlibc hfs_eq
    hstrlenRO hc_alloc hstk hSt0 hSt01 hrun hhops

end LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudgetSat
