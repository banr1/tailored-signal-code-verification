/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4PlacedBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Structural
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `main` Hop M4 (`M+0x5dc → M+0x7b0 / M+0xb24 / M+0x650`)

Verifies `main`'s fourth hop on Block `617` under `[LibsignalPlacement]` and `RustCliAllocBudget M`,
covering the 1 MiB `send` payload cap (`ExitKPoolPlaced`), `RunEnv`-exact execution of
`signal_session::run`, and envelope-erased `runSpecAny*Placed` corollaries.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.RustHeap (allocFailedIn)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli
  (IsSendOverCap RunAnswer StoresGhost cliInputs cliStaticsPlaced)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AtM4EndPlaced AtM4EndTightPlaced AtM4Placed CallV CallW HistOk HistOkTight InMainPlaced
   LsCodeInv RunCall argsBuf callHeap coinsOf inputOf locals m4CellsPlaced m5CellsPlaced
   mProgPlaced mainFrameSize mainLitsBlk617 mainOom mainOomLegacy mainSaved main_call_plain
   namedWrites ownedBytes parseArgs runResAt sepWPp_of_mainOom stackAt_split_ge)
open CryptoVerification.SignalSession.Cli.MainHops.M4Placed
  (m4RestFramePlaced ownedBytesRest ownedBytes_merge)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4PlacedBudget

open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (runSpecAnyPlaced runSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
  (ExitKPlaced MainCalleesBlk617 runSpecAnyTightPlaced runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4PlacedBudgetAux
  (m4_allocFailedIn_of_start_trace_eq_p m4_err_tail_pool_placed m4_histOkTight_of_eq_p
   m4_ok_tail_placed m4_sendOverCap_pool_placed_proof m4_sepWPp_exists_left_p m4_to_run_call_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
  (ExitKPoolPlaced exitKPoolPlaced_of_exitKPlaced)

private theorem sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

/-! ## 1. `IsSendOverCap` Clean Exit (`M+0x5dc → M+0x650`) -/

/-- On `c = .send peer` with `1_000_000 < i.stdin.length`, `M+0x5dc .. M+0x61c` installs `coins`,
detects `x27 > 0xf4240`, sets `w26 = 1`, and jumps to `M+0x650` to drop `input`, `Call`, and `args`
before exiting with code `1`, retaining `A.pool` via `ExitKPoolPlaced`. -/
theorem main_m4_sendOverCap_pool_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {peer : AddrV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hsp : stk ≤ s0.sp.toNat)
    (hs0tr : s0.trace = [])
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some (.send peer))
    (hover : 1_000_000 < i.stdin.length)
    (hs : AtM4Placed CodeOk i s0 s w (.send peer) i.argv.length buf coinsCap coinsPtr inCap)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 1 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        s'.trace = s.trace) Q Qp) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i (.send peer)).length)
          (inputOf i (.send peer)) ∗
        callHeap A.repAlloc w (.send peer) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp (mainOom s0) :=
  m4_sendOverCap_pool_placed_proof hc hstk hstk64 hsp hs0tr hparse hover hs hpanic hexit

theorem main_m4_sendOverCap_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {peer : AddrV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hsp : stk ≤ s0.sp.toNat)
    (hs0tr : s0.trace = [])
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some (.send peer))
    (hover : 1_000_000 < i.stdin.length)
    (hs : AtM4Placed CodeOk i s0 s w (.send peer) i.argv.length buf coinsCap coinsPtr inCap)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 1 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        s'.trace = s.trace) Q Qp) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i (.send peer)).length)
          (inputOf i (.send peer)) ∗
        callHeap A.repAlloc w (.send peer) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp (mainOom s0) :=
  main_m4_sendOverCap_pool_placed_proof hc hstk hstk64 hsp hs0tr hparse hover hs hpanic
    (exitKPoolPlaced_of_exitKPlaced (lim := lim) hexit)

/-! ## 2. Top-Level Budget-Threaded `main_m4` Proofs (`RunEnv` & Envelope-Erased `Any`) -/

set_option maxHeartbeats 1200000 in
/-- Proves `AtM4EndTightPlaced` and threads `A.pool lim (M.stepEvents evs st) s'` over
`runSpecTightPlaced` when `∀ peer, c = .send peer → i.stdin.length ≤ 1_000_000`. -/
theorem main_m4_pool_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {RunEnv : RunCall → List AllocEvent → Prop} {uuidParse : UuidParser}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop}
    {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hrun : subroutine_ok (mProgPlaced H) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk A lim RunEnv uuidParse Run wrOk resStack))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hsp : stk ≤ s0.sp.toNat)
    (hs0tr : s0.trace = [])
    (hRun : Run i a)
    (hnot_over : ∀ peer, c = .send peer → i.stdin.length ≤ 1_000_000)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim st (RunEnv
      { i := i, c := c, a := a,
        res := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64,
        call := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64,
        stores := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64,
        inp := inPtr, coins := coinsPtr }))
    (hs : AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap)
    (hpanic : ∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 1 ∧ a = some none ∧ HistOkTight i s' ∧
        s.trace <+: s'.trace) Q Qp)
    (hnext : ∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)) (evs : List AllocEvent),
      RunEnv
        { i := i, c := c, a := a,
          res := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64,
          call := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64,
          stores := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64,
          inp := inPtr, coins := coinsPtr } evs →
      a = some (some (namedWrites g.writes, out)) →
      (∀ pw ∈ g.writes, wrOk pw.1) → s.trace <+: s'.trace →
      AtM4EndTightPlaced CodeOk i s0 s' c i.argv.length buf inCap →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st) s' ∗ anyHeap)
        Q Qp (mainOom s0)) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hres_le : resStack ≤ stk - mainFrameSize := by omega
  have hstk_split := stackAt_split_ge fsp hres_le (by omega)
  refine m4_to_run_call_placed hstk hsp hs0tr hRun hnot_over hparse hs
    fun s3 hs3 hsp3 htr3_s htr3_0 hfs3_s => ?_
  let g_run : RunCall :=
    { i := i, c := c, a := a, res := fsp + 0x1b8#64, call := fsp + 0x78#64,
      stores := fsp + 0x310#64, inp := inPtr, coins := coinsPtr }
  let frameRun : SepProp :=
    m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
      ownedBytesRest A.repAlloc inCap inPtr (inputOf i c) ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - resStack) ∗
      anyHeap
  have hpre_env :
      (runSpecAnyPlaced CodeOk A lim uuidParse Run (fun _ => True) resStack).pre (g_run, st) s3 ∗
        frameRun ⊢
      (runSpecTightPlaced CodeOk A lim RunEnv uuidParse Run wrOk resStack).pre (g_run, st) s3 ∗
        frameRun := by
    dsimp only [runSpecTightPlaced, runSpecPlaced, runSpecAnyPlaced]
    refine sepConj_mono ?_ (Entails.refl _)
    exact Entails.pure_left fun hp => Entails.pure_right ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1,
      hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1,
      hp.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1, hfit,
      hp.2.2.2.2.2.2.2.2.2.2.2⟩ (Entails.refl _)
  refine main_call_plain (CodeOk := CodeOk) (g_run, st) hrun hs3.inv hs3.pc hs3.run hs3.spAligned
    hs3.lr hpre_env
    (hpanic := fun sf R' _ hp => ?_)
    (hoom := fun sf R' _ ho => ?_)
    (hnext := fun sf hinv_f hpcm hrunm hspm hcsm => ?_)
  · dsimp only [runSpecTightPlaced, runSpecPlaced, g_run] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    exact hpanic sf _ (hp.1.imp_right (m4_allocFailedIn_of_start_trace_eq_p htr3_0))
  · dsimp only [runSpecTightPlaced, runSpecPlaced] at ho
    exact (not_satisfies_false_sepConj ho).elim
  · have hsp_f : sf.sp = fsp := hspm.trans hsp3
    have hs_7a4 : InMainPlaced CodeOk s0 sf 0x7a4 :=
      { pc := hpcm, run := hrunm, sp := hsp_f,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hs3.fp, inv := hinv_f,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hs3.vregs, spAligned := hs.base.spAligned }
    have hx19_f : sf.readReg64 (.gpr 19#5) = buf := hcsm.1.trans hs3.x19
    have hx21_f : sf.readReg64 (.gpr 21#5) = fsp + 0x310#64 := by rw [hcsm.2.2.1, hs3.x21, hsp3]
    have hx22_f : sf.readReg64 (.gpr 22#5) = fsp + 0x78#64 := by rw [hcsm.2.2.2.1, hs3.x22, hsp3]
    have hx23_f : sf.readReg64 (.gpr 23#5) = inCap := hcsm.2.2.2.2.1.trans hs3.x23
    have hx24_f : sf.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length :=
      hcsm.2.2.2.2.2.1.trans hs3.x24
    have hx27_f : sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (inputOf i c).length :=
      hcsm.2.2.2.2.2.2.2.2.1.trans hs3.x27
    dsimp only [runSpecTightPlaced, runSpecPlaced, g_run, frameRun]
    rw [sepExists_sepConj_left]
    apply m4_sepWPp_exists_left_p; intro evs
    have hpost_tidy :
        (⌜RunEnv g_run evs ∧ s3.trace <+: sf.trace ∧
            sf.fs.files = s3.fs.files ∧
            ProcessOutcome.traceStreamBytes .stdout sf.trace =
              ProcessOutcome.traceStreamBytes .stdout s3.trace⌝ ∗
          memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
          (inPtr ↦ₛ inputOf i c) ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s3.sp resStack ∗
          (∃∗ a' : RunAnswer, ⌜a' ≠ none ∧ a' = a⌝ ∗
            runResAt A.repAlloc wrOk (fsp + 0x1b8#64) a') ∗ anyHeap) ∗
        (m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          ownedBytesRest A.repAlloc inCap inPtr (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - resStack) ∗ anyHeap) ⊢
        ⌜RunEnv g_run evs ∧ s3.trace <+: sf.trace ∧
          sf.fs.files = s3.fs.files ∧
          ProcessOutcome.traceStreamBytes .stdout sf.trace =
            ProcessOutcome.traceStreamBytes .stdout s3.trace⌝ ∗
        (∃∗ a' : RunAnswer, ⌜a' ≠ none ∧ a' = a⌝ ∗
          runResAt A.repAlloc wrOk (fsp + 0x1b8#64) a') ∗
        m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ anyHeap := by
      rw [hsp3]
      have hrearr_post :
          (⌜RunEnv g_run evs ∧ s3.trace <+: sf.trace ∧
              sf.fs.files = s3.fs.files ∧
              ProcessOutcome.traceStreamBytes .stdout sf.trace =
                ProcessOutcome.traceStreamBytes .stdout s3.trace⌝ ∗
            memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
            (inPtr ↦ₛ inputOf i c) ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt fsp resStack ∗
            (∃∗ a' : RunAnswer, ⌜a' ≠ none ∧ a' = a⌝ ∗
              runResAt A.repAlloc wrOk (fsp + 0x1b8#64) a') ∗ anyHeap) ∗
          (m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
            ownedBytesRest A.repAlloc inCap inPtr (inputOf i c) ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
            memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - resStack) ∗ anyHeap) =
          ⌜RunEnv g_run evs ∧ s3.trace <+: sf.trace ∧
            sf.fs.files = s3.fs.files ∧
            ProcessOutcome.traceStreamBytes .stdout sf.trace =
              ProcessOutcome.traceStreamBytes .stdout s3.trace⌝ ∗
          (∃∗ a' : RunAnswer, ⌜a' ≠ none ∧ a' = a⌝ ∗
            runResAt A.repAlloc wrOk (fsp + 0x1b8#64) a') ∗
          m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
          ((inPtr ↦ₛ inputOf i c) ∗ ownedBytesRest A.repAlloc inCap inPtr (inputOf i c)) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
          (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - resStack) ∗ stackAt fsp resStack) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ (anyHeap ∗ anyHeap) := by
        sep_ac_rfl
      rw [hrearr_post]
      exact sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono_right
              (sepConj_mono_right
                (sepConj_mono_right
                  (sepConj_mono (ownedBytes_merge A.repAlloc inCap inPtr (inputOf i c))
                    (sepConj_mono_right
                      (sepConj_mono_right
                        (sepConj_mono (Entails.of_eq hstk_split.symm)
                          (sepConj_mono_right
                            (ProofLib.entails_anyHeap (anyHeap ∗ anyHeap))))))))))))
    refine sepWPp_weaken_pre hpost_tidy ?_
    clear hpost_tidy
    apply SepWPp.pure_left
    rintro ⟨hevs, htr_pref3, hfiles, hout⟩
    have htr_pref_s : s.trace <+: sf.trace := by rwa [htr3_s] at htr_pref3
    have hhist_sf : HistOkTight i sf :=
      ⟨by rw [hfiles, hfs3_s]; exact hs.fs, by rw [hout, htr3_0, hs0tr]; rfl⟩
    rw [sepExists_sepConj_left]
    apply m4_sepWPp_exists_left_p; intro a'
    rw [sepConj_assoc]
    apply SepWPp.pure_left
    rintro ⟨ha'_ne, ha'_eq⟩
    cases a' with
    | none => exact (ha'_ne rfl).elim
    | some res =>
      cases res with
      | none =>
        exact m4_err_tail_pool_placed hc hstk hstk64 hs_7a4 hsp_f hx19_f hx23_f hx24_f
          (fun s_exit htr_tot hfs_tot =>
            ⟨rfl, ha'_eq.symm,
              m4_histOkTight_of_eq_p htr_tot hfs_tot hhist_sf,
              by rwa [htr_tot]⟩)
          hexit
      | some p =>
        rcases p with ⟨ws, out⟩
        dsimp only [runResAt]
        rw [sepExists_sepConj_left]
        apply m4_sepWPp_exists_left_p; intro g
        rw [sepConj_assoc]
        apply SepWPp.pure_left
        rintro ⟨hws, hwr⟩
        subst hws
        exact m4_ok_tail_placed hs_7a4 hsp_f hx19_f hx21_f hx22_f hx23_f hx24_f hx27_f
          fun s' hs_7b0 hx19' hx21' hx22' hx23' hx24' hx27' htr_ok hfs_ok =>
            hnext s' g out evs hevs ha'_eq.symm hwr (by rwa [htr_ok])
              { base := hs_7b0, x19 := hx19', x21 := hx21', x22 := hx22', x23 := hx23',
                x24 := hx24', x27 := hx27',
                hist := m4_histOkTight_of_eq_p htr_ok hfs_ok hhist_sf }

/-- Direct `uuidTryParse` + `¬ IsSendOverCap i` specialization of `main_m4_pool_placed_proof`,
matching `B2MainFrameComposeBudget.step4_call`. -/
theorem main_m4_call_pool_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop}
    {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidTryParse hookStack resStack)
    (hrun : subroutine_ok (mProgPlaced H) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk A lim RunEnv uuidTryParse Run wrOk resStack))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hsp : stk ≤ s0.sp.toNat)
    (hs0tr : s0.trace = [])
    (hRun : Run i a) (hnover : ¬ IsSendOverCap i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim st (RunEnv
      { i := i, c := c, a := a,
        res := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64,
        call := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64,
        stores := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64,
        inp := inPtr, coins := coinsPtr }))
    (hs : AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap)
    (hpanic : ∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 1 ∧ a = some none ∧ HistOkTight i s' ∧
        s.trace <+: s'.trace) Q Qp)
    (hnext : ∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)) (evs : List AllocEvent),
      RunEnv
        { i := i, c := c, a := a,
          res := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64,
          call := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64,
          stores := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64,
          inp := inPtr, coins := coinsPtr } evs →
      a = some (some (namedWrites g.writes, out)) →
      (∀ pw ∈ g.writes, wrOk pw.1) → s.trace <+: s'.trace →
      AtM4EndTightPlaced CodeOk i s0 s' c i.argv.length buf inCap →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st) s' ∗ anyHeap)
        Q Qp (mainOom s0)) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp (mainOom s0) :=
  main_m4_pool_placed_proof hc hrun hstk hstk64 hsp hs0tr hRun
    (fun peer hc_eq => Nat.le_of_not_lt fun hgt => hnover ⟨⟨peer, hc_eq ▸ hparse⟩, hgt⟩)
    hparse hfit hs hpanic hexit hnext

theorem main_m4_tight_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {RunEnv : RunCall → List AllocEvent → Prop} {uuidParse : UuidParser}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop}
    {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hrun : subroutine_ok (mProgPlaced H) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk A lim RunEnv uuidParse Run wrOk resStack))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hsp : stk ≤ s0.sp.toNat)
    (hs0tr : s0.trace = [])
    (hRun : Run i a)
    (hnot_over : ∀ peer, c = .send peer → i.stdin.length ≤ 1_000_000)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim st (RunEnv
      { i := i, c := c, a := a,
        res := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64,
        call := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64,
        stores := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64,
        inp := inPtr, coins := coinsPtr }))
    (hs : AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap)
    (hpanic : ∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 1 ∧ a = some none ∧ HistOkTight i s' ∧
        s.trace <+: s'.trace) Q Qp)
    (hnext : ∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)) (evs : List AllocEvent),
      RunEnv
        { i := i, c := c, a := a,
          res := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64,
          call := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64,
          stores := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64,
          inp := inPtr, coins := coinsPtr } evs →
      a = some (some (namedWrites g.writes, out)) →
      (∀ pw ∈ g.writes, wrOk pw.1) → s.trace <+: s'.trace →
      AtM4EndTightPlaced CodeOk i s0 s' c i.argv.length buf inCap →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st) s' ∗ anyHeap)
        Q Qp (mainOom s0)) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp (mainOom s0) :=
  main_m4_pool_placed_proof hc hrun hstk hstk64 hsp hs0tr hRun hnot_over hparse hfit hs hpanic
    (exitKPoolPlaced_of_exitKPlaced (lim := lim) hexit) hnext

theorem main_m4_call_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop}
    {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidTryParse hookStack resStack)
    (hrun : subroutine_ok (mProgPlaced H) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk A lim RunEnv uuidTryParse Run wrOk resStack))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hsp : stk ≤ s0.sp.toNat)
    (hs0tr : s0.trace = [])
    (hRun : Run i a) (hnover : ¬ IsSendOverCap i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim st (RunEnv
      { i := i, c := c, a := a,
        res := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64,
        call := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64,
        stores := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64,
        inp := inPtr, coins := coinsPtr }))
    (hs : AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap)
    (hpanic : ∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 1 ∧ a = some none ∧ HistOkTight i s' ∧
        s.trace <+: s'.trace) Q Qp)
    (hnext : ∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)) (evs : List AllocEvent),
      RunEnv
        { i := i, c := c, a := a,
          res := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64,
          call := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64,
          stores := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64,
          inp := inPtr, coins := coinsPtr } evs →
      a = some (some (namedWrites g.writes, out)) →
      (∀ pw ∈ g.writes, wrOk pw.1) → s.trace <+: s'.trace →
      AtM4EndTightPlaced CodeOk i s0 s' c i.argv.length buf inCap →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st) s' ∗ anyHeap)
        Q Qp (mainOom s0)) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp (mainOom s0) :=
  main_m4_call_pool_placed_proof hc hrun hstk hstk64 hsp hs0tr hRun hnover hparse hfit hs hpanic
    (exitKPoolPlaced_of_exitKPlaced (lim := lim) hexit) hnext

/-- Legacy-shape `RunEnv`-exact `main_m4` wrapper over `runSpecPlaced`. -/
theorem main_m4_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {RunEnv : RunCall → List AllocEvent → Prop} {uuidParse : UuidParser}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop}
    {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hrun : subroutine_ok (mProgPlaced H) (lsmpl.base 579)
      (runSpecPlaced CodeOk A lim RunEnv uuidParse Run wrOk resStack))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hsp : stk ≤ s0.sp.toNat)
    (hs0tr : s0.trace = [])
    (hRun : Run i a)
    (hnot_over : ∀ peer, c = .send peer → i.stdin.length ≤ 1_000_000)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hfit : FitsEnv M lim st (RunEnv
      { i := i, c := c, a := a,
        res := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64,
        call := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64,
        stores := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64,
        inp := inPtr, coins := coinsPtr }))
    (hs : AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap)
    (hpanic : ∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 1 ∧ (a = some none ∨ allocFailedIn s0 s') ∧ HistOk i s0 s' ∧
        s.trace <+: s'.trace) Q Qp)
    (hnext : ∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)) (evs : List AllocEvent),
      RunEnv
        { i := i, c := c, a := a,
          res := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64,
          call := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64,
          stores := s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64,
          inp := inPtr, coins := coinsPtr } evs →
      (a = some (some (namedWrites g.writes, out)) ∨ allocFailedIn s0 s') →
      (∀ pw ∈ g.writes, wrOk pw.1) → s.trace <+: s'.trace →
      AtM4EndPlaced CodeOk i s0 s' c i.argv.length buf inCap →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st) s' ∗ anyHeap)
        Q Qp (mainOom s0)) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp (mainOomLegacy s0) := by
  apply sepWPp_of_mainOom
  exact main_m4_tight_placed_proof hc hrun hstk hstk64 hsp hs0tr hRun hnot_over hparse hfit hs hpanic
    (fun s' code hs' ⟨hc1, ha, hhist, htr⟩ =>
      hexit s' code hs' ⟨hc1, Or.inl ha, Or.inl hhist, htr⟩)
    (fun s' g out evs hevs ha hwr htr hAt =>
      hnext s' g out evs hevs (Or.inl ha) hwr htr hAt.toAtM4EndPlaced)

set_option maxHeartbeats 1200000 in
/-- Envelope-erased `ExitKPoolPlaced` `main_m4` proof over `runSpecAnyTightPlaced` with existential
post-`run` cost state `st' : M.σ`. -/
theorem main_m4_any_pool_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop}
    {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hrun : subroutine_ok (mProgPlaced H) (lsmpl.base 579)
      (runSpecAnyTightPlaced CodeOk A lim uuidParse Run wrOk resStack))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hsp : stk ≤ s0.sp.toNat)
    (hs0tr : s0.trace = [])
    (hRun : Run i a)
    (hnot_over : ∀ peer, c = .send peer → i.stdin.length ≤ 1_000_000)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hs : AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap)
    (hpanic : ∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 1 ∧ a = some none ∧ HistOkTight i s' ∧
        s.trace <+: s'.trace) Q Qp)
    (hnext : ∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)) (st' : M.σ),
      a = some (some (namedWrites g.writes, out)) →
      (∀ pw ∈ g.writes, wrOk pw.1) → s.trace <+: s'.trace →
      AtM4EndTightPlaced CodeOk i s0 s' c i.argv.length buf inCap →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st' s' ∗ anyHeap)
        Q Qp (mainOom s0)) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hres_le : resStack ≤ stk - mainFrameSize := by omega
  have hstk_split := stackAt_split_ge fsp hres_le (by omega)
  refine m4_to_run_call_placed hstk hsp hs0tr hRun hnot_over hparse hs
    fun s3 hs3 hsp3 htr3_s htr3_0 hfs3_s => ?_
  let g_run : RunCall :=
    { i := i, c := c, a := a, res := fsp + 0x1b8#64, call := fsp + 0x78#64,
      stores := fsp + 0x310#64, inp := inPtr, coins := coinsPtr }
  let frameRun : SepProp :=
    m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
      ownedBytesRest A.repAlloc inCap inPtr (inputOf i c) ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - resStack) ∗
      anyHeap
  have hpre_any :
      (runSpecAnyPlaced CodeOk A lim uuidParse Run (fun _ => True) resStack).pre (g_run, st) s3 ∗
        frameRun ⊢
      (runSpecAnyTightPlaced CodeOk A lim uuidParse Run wrOk resStack).pre (g_run, st) s3 ∗
        frameRun :=
    Entails.refl _
  refine main_call_plain (CodeOk := CodeOk) (g_run, st) hrun hs3.inv hs3.pc hs3.run hs3.spAligned
    hs3.lr hpre_any
    (hpanic := fun sf R' _ hp => ?_)
    (hoom := fun sf R' _ ho => ?_)
    (hnext := fun sf hinv_f hpcm hrunm hspm hcsm => ?_)
  · dsimp only [runSpecAnyTightPlaced, runSpecAnyPlaced, g_run] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    exact hpanic sf _ (hp.1.imp_right (m4_allocFailedIn_of_start_trace_eq_p htr3_0))
  · dsimp only [runSpecAnyTightPlaced, runSpecAnyPlaced] at ho
    exact (not_satisfies_false_sepConj ho).elim
  · have hsp_f : sf.sp = fsp := hspm.trans hsp3
    have hs_7a4 : InMainPlaced CodeOk s0 sf 0x7a4 :=
      { pc := hpcm, run := hrunm, sp := hsp_f,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hs3.fp, inv := hinv_f,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hs3.vregs, spAligned := hs.base.spAligned }
    have hx19_f : sf.readReg64 (.gpr 19#5) = buf := hcsm.1.trans hs3.x19
    have hx21_f : sf.readReg64 (.gpr 21#5) = fsp + 0x310#64 := by rw [hcsm.2.2.1, hs3.x21, hsp3]
    have hx22_f : sf.readReg64 (.gpr 22#5) = fsp + 0x78#64 := by rw [hcsm.2.2.2.1, hs3.x22, hsp3]
    have hx23_f : sf.readReg64 (.gpr 23#5) = inCap := hcsm.2.2.2.2.1.trans hs3.x23
    have hx24_f : sf.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length :=
      hcsm.2.2.2.2.2.1.trans hs3.x24
    have hx27_f : sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (inputOf i c).length :=
      hcsm.2.2.2.2.2.2.2.2.1.trans hs3.x27
    dsimp only [runSpecAnyTightPlaced, runSpecAnyPlaced, g_run, frameRun]
    rw [sepExists_sepConj_left]
    apply m4_sepWPp_exists_left_p; intro st'
    have hpost_tidy :
        (⌜s3.trace <+: sf.trace ∧
            sf.fs.files = s3.fs.files ∧
            ProcessOutcome.traceStreamBytes .stdout sf.trace =
              ProcessOutcome.traceStreamBytes .stdout s3.trace⌝ ∗
          memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
          (inPtr ↦ₛ inputOf i c) ∗ A.pool lim st' sf ∗ stackAt s3.sp resStack ∗
          (∃∗ a' : RunAnswer, ⌜a' ≠ none ∧ a' = a⌝ ∗
            runResAt A.repAlloc wrOk (fsp + 0x1b8#64) a') ∗ anyHeap) ∗
        (m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          ownedBytesRest A.repAlloc inCap inPtr (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - resStack) ∗ anyHeap) ⊢
        ⌜s3.trace <+: sf.trace ∧
          sf.fs.files = s3.fs.files ∧
          ProcessOutcome.traceStreamBytes .stdout sf.trace =
            ProcessOutcome.traceStreamBytes .stdout s3.trace⌝ ∗
        (∃∗ a' : RunAnswer, ⌜a' ≠ none ∧ a' = a⌝ ∗
          runResAt A.repAlloc wrOk (fsp + 0x1b8#64) a') ∗
        m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗
        A.pool lim st' sf ∗ anyHeap := by
      rw [hsp3]
      have hrearr_post :
          (⌜s3.trace <+: sf.trace ∧
              sf.fs.files = s3.fs.files ∧
              ProcessOutcome.traceStreamBytes .stdout sf.trace =
                ProcessOutcome.traceStreamBytes .stdout s3.trace⌝ ∗
            memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
            (inPtr ↦ₛ inputOf i c) ∗ A.pool lim st' sf ∗ stackAt fsp resStack ∗
            (∃∗ a' : RunAnswer, ⌜a' ≠ none ∧ a' = a⌝ ∗
              runResAt A.repAlloc wrOk (fsp + 0x1b8#64) a') ∗ anyHeap) ∗
          (m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
            ownedBytesRest A.repAlloc inCap inPtr (inputOf i c) ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
            memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - resStack) ∗ anyHeap) =
          ⌜s3.trace <+: sf.trace ∧
            sf.fs.files = s3.fs.files ∧
            ProcessOutcome.traceStreamBytes .stdout sf.trace =
              ProcessOutcome.traceStreamBytes .stdout s3.trace⌝ ∗
          (∃∗ a' : RunAnswer, ⌜a' ≠ none ∧ a' = a⌝ ∗
            runResAt A.repAlloc wrOk (fsp + 0x1b8#64) a') ∗
          m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
          ((inPtr ↦ₛ inputOf i c) ∗ ownedBytesRest A.repAlloc inCap inPtr (inputOf i c)) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
          (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - resStack) ∗ stackAt fsp resStack) ∗
          A.pool lim st' sf ∗ (anyHeap ∗ anyHeap) := by
        sep_ac_rfl
      rw [hrearr_post]
      exact sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono_right
              (sepConj_mono_right
                (sepConj_mono_right
                  (sepConj_mono (ownedBytes_merge A.repAlloc inCap inPtr (inputOf i c))
                    (sepConj_mono_right
                      (sepConj_mono_right
                        (sepConj_mono (Entails.of_eq hstk_split.symm)
                          (sepConj_mono_right
                            (ProofLib.entails_anyHeap (anyHeap ∗ anyHeap))))))))))))
    refine sepWPp_weaken_pre hpost_tidy ?_
    clear hpost_tidy
    apply SepWPp.pure_left
    rintro ⟨htr_pref3, hfiles, hout⟩
    have htr_pref_s : s.trace <+: sf.trace := by rwa [htr3_s] at htr_pref3
    have hhist_sf : HistOkTight i sf :=
      ⟨by rw [hfiles, hfs3_s]; exact hs.fs, by rw [hout, htr3_0, hs0tr]; rfl⟩
    rw [sepExists_sepConj_left]
    apply m4_sepWPp_exists_left_p; intro a'
    rw [sepConj_assoc]
    apply SepWPp.pure_left
    rintro ⟨ha'_ne, ha'_eq⟩
    cases a' with
    | none => exact (ha'_ne rfl).elim
    | some res =>
      cases res with
      | none =>
        exact m4_err_tail_pool_placed hc hstk hstk64 hs_7a4 hsp_f hx19_f hx23_f hx24_f
          (fun s_exit htr_tot hfs_tot =>
            ⟨rfl, ha'_eq.symm,
              m4_histOkTight_of_eq_p htr_tot hfs_tot hhist_sf,
              by rwa [htr_tot]⟩)
          hexit
      | some p =>
        rcases p with ⟨ws, out⟩
        dsimp only [runResAt]
        rw [sepExists_sepConj_left]
        apply m4_sepWPp_exists_left_p; intro g
        rw [sepConj_assoc]
        apply SepWPp.pure_left
        rintro ⟨hws, hwr⟩
        subst hws
        exact m4_ok_tail_placed hs_7a4 hsp_f hx19_f hx21_f hx22_f hx23_f hx24_f hx27_f
          fun s' hs_7b0 hx19' hx21' hx22' hx23' hx24' hx27' htr_ok hfs_ok =>
            hnext s' g out st' ha'_eq.symm hwr (by rwa [htr_ok])
              { base := hs_7b0, x19 := hx19', x21 := hx21', x22 := hx22', x23 := hx23',
                x24 := hx24', x27 := hx27',
                hist := m4_histOkTight_of_eq_p htr_ok hfs_ok hhist_sf }

theorem main_m4_any_tight_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop}
    {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hrun : subroutine_ok (mProgPlaced H) (lsmpl.base 579)
      (runSpecAnyTightPlaced CodeOk A lim uuidParse Run wrOk resStack))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hsp : stk ≤ s0.sp.toNat)
    (hs0tr : s0.trace = [])
    (hRun : Run i a)
    (hnot_over : ∀ peer, c = .send peer → i.stdin.length ≤ 1_000_000)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hs : AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap)
    (hpanic : ∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 1 ∧ a = some none ∧ HistOkTight i s' ∧
        s.trace <+: s'.trace) Q Qp)
    (hnext : ∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)) (st' : M.σ),
      a = some (some (namedWrites g.writes, out)) →
      (∀ pw ∈ g.writes, wrOk pw.1) → s.trace <+: s'.trace →
      AtM4EndTightPlaced CodeOk i s0 s' c i.argv.length buf inCap →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st' s' ∗ anyHeap)
        Q Qp (mainOom s0)) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp (mainOom s0) :=
  main_m4_any_pool_placed_proof hc hrun hstk hstk64 hsp hs0tr hRun hnot_over hparse hs hpanic
    (exitKPoolPlaced_of_exitKPlaced (lim := lim) hexit) hnext

/-- Envelope-erased legacy-shape `main_m4` wrapper over `runSpecAnyPlaced`. -/
theorem main_m4_any_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop}
    {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hrun : subroutine_ok (mProgPlaced H) (lsmpl.base 579)
      (runSpecAnyPlaced CodeOk A lim uuidParse Run wrOk resStack))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hsp : stk ≤ s0.sp.toNat)
    (hs0tr : s0.trace = [])
    (hRun : Run i a)
    (hnot_over : ∀ peer, c = .send peer → i.stdin.length ≤ 1_000_000)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hs : AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap)
    (hpanic : ∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 1 ∧ (a = some none ∨ allocFailedIn s0 s') ∧ HistOk i s0 s' ∧
        s.trace <+: s'.trace) Q Qp)
    (hnext : ∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)) (st' : M.σ),
      (a = some (some (namedWrites g.writes, out)) ∨ allocFailedIn s0 s') →
      (∀ pw ∈ g.writes, wrOk pw.1) → s.trace <+: s'.trace →
      AtM4EndPlaced CodeOk i s0 s' c i.argv.length buf inCap →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st' s' ∗ anyHeap)
        Q Qp (mainOom s0)) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp (mainOomLegacy s0) := by
  apply sepWPp_of_mainOom
  exact main_m4_any_tight_placed_proof hc hrun hstk hstk64 hsp hs0tr hRun hnot_over hparse hs
    hpanic
    (fun s' code hs' ⟨hc1, ha, hhist, htr⟩ =>
      hexit s' code hs' ⟨hc1, Or.inl ha, Or.inl hhist, htr⟩)
    (fun s' g out st' ha hwr htr hAt =>
      hnext s' g out st' (Or.inl ha) hwr htr hAt.toAtM4EndPlaced)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4PlacedBudget
