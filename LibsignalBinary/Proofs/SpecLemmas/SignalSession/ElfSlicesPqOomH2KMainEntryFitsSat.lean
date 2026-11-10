/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.PoolNeedLocks
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlacedPadSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInstSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1PlacedRoBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2PlacedBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMainEntryFits -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# `HookSat` Sibling of `ElfSlicesPqOomH2KMainEntryFits` (`ElfSlicesPqOomH2KMainEntryFitsSat`)

**Checked by Lean.** Untrusted (`CliElfLib`, `Role::Proof`; `0` `sorry`, `std3` axioms).

Replaces both exact-hook hypotheses
- `hutf8 : ext W lsFromUtf8Sym = some (fromUtf8Hook err)` / `∀ W, ext W lsFromUtf8Sym = some (fromUtf8Hook (errOf W))`
  (dropping unused `err` / `errOf`), and
- `hmemrchr : ext W lsMemrchrSym = some memrchrHook` / `∀ W, ext W lsMemrchrSym = some memrchrHook`
with `HookSat` RW (`withVmPreserved (fromUtf8AsciiSpec hookStack)`, `withVmPreserved (memrchrSpec extHookStack)`)
and RO (`withVmPreserved (fromUtf8AsciiSpecRO hookStack)`, `withVmPreserved (memrchrSpecRO extHookStack)`)
contracts across all 6 general-`ext` theorems of `ElfSlicesPqOomH2KMainEntryFits`, plus `toSat` bridges
recovering the two `cliGhostExterns` instantiations.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMainEntryFitsSat

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.RustHeap (allocFailedIn)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs cliExternsPlaced cliProcessInputs
   libsignalSessionLib lsFromUtf8Sym lsMemrchrSym stdinCapBytes strlenHook)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk CoinsReadable IsSendOverCap MainPost MainResult RunAnswer StoresGhost
   cliInputs cliStaticsPlaced utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AtCallPlaced AtEntryPlaced AtM1EndPlaced AtM4EndPlaced AtM4EndTightPlaced AtM4Placed
   AtM6Placed CallV CallW HistOkTight IoModel LsCodeInv MainIoFacts RunCall argsBuf
   callCellsPlaced callHeap cliIo cliIo_coins cliIo_coinsPath cliIo_commit cliIo_stdin cliMainStk
   cliResStack cliWrOk cli_hstk64 cli_resStack_callees coinsOf commitFiles fromUtf8AsciiSpec
   hparse_of_domains inputOf locals lsHandleErrorSymMain m4CellsPlaced m5CellsPlaced m6CellsPlaced
   mProgPlaced mainFrameSize mainLitsBlk617 mainOom mainSaved memrchrSpec namedWrites ownedBytes
   parseArgs parseArgs_none_of_shape_proof)
open CryptoVerification.SignalSession.Cli.MainHops.MainOkPlacedHelpers
  (panic_of_mem traceStreamBytes_nil)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_fromUtf8_eq cliGhostExterns_memrchr_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget rustAllocEvents)
open LibsignalBinary.Heap.Fine
  (FineBudget fineCostModel fineHookRustCliAllocBudget hookPool_entails_needLocks_anyHeap)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad
  (argvAtROPPad b2MainFrameFinePad b2MainSpecTightNeedLocksFineAtPad strlenSpecROSat)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
  (argvAtROP exitKPool_b2NeedLocks_tight_placed libsignalPlacementOf
   mProgPlaced_eq_cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudgetSat
  (sepWPp_argvAtROPPad_to_unpadded_needLocks sepWPp_b2MainFrameFinePad_mainLitsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
  (fromUtf8AsciiSpecRO memrchrSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesROSat
  (hookSat_fromUtf8ROVm_of_eq hookSat_memrchrROVm_ls_of_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
  (B2MainEntryFacts cliStaticsPlacedAt cliStaticsPlacedAt_eq_cliStaticsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlacedPadSat
  (MainOkCliExtOverB2NeedLocksPadPlacedAt MainOkCliExtPqB2NeedLocksPadPlacedAt
   mainOkCliExtOverB2NeedLocksPadPlacedAt_of_pqScopedMainSubroutine
   mainOkCliExtPqB2NeedLocksPadPlacedAt_of_pqScopedMainSubroutine)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
  (B2St1CapOf B2St2CapOf B2St3Cap B2St4Cap B2St5Cap MainEntryBudgetFitsCapOf
   b2St0Cap_init b2St01_of_mainEntryBudgetFitsCapOf
   cliGhostExterns_handleErrorMain cliGhostExterns_strlen domScopedRun domScopedRun_dom)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInstSat
  (hookSat_fromUtf8Vm_of_eq hookSat_strlenRO_of_eq
   mainCalleesBlk617_of_allocFs_and_hooks_cliResStack_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced (ReadStdinBoundedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
  (cliRunSemD2c_placed initFsState_cliProcessInputs_eq mainFrameSize_le_cliMainStk pqScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1PlacedBudgetSat
  (hookSat_memrchrVm_ls_of_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1PlacedRoBudgetSat
  (main_m1_ro_pool_placed_step1_of_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2PlacedBudgetSat
  (b2_step2_pool_placed_of_hooks_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudgetFd
  (MainIoOfPlacedFd main_m3_bounded_readOf_pool_placed_proof_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4PlacedBudget
  (main_m4_sendOverCap_pool_placed_proof)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4PlacedBudgetFd
  (main_m4_pool_placed_proof_preFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5PlacedBudget
  (main_m5_of_proof_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M6PlacedBudget
  (main_m6_of_m6Env_pool_proof_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget (ExitKPoolPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks allocContractsFsPlaced_of_hooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (runSpecTightPlacedPreFd)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMainEntryFits
  (B2MainRemainingHopsPreFd subroutine_ok_runSpecTightPlacedPreFd_mono_run)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

private theorem runSpecTightPlacedPreFd_eq_m4 [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (RunEnv : RunCall → List AllocEvent → Prop) (uuidParse : UuidParser)
    (Run : Inputs → RunAnswer → Prop) (wrOk : List (BitVec 8) → Prop) (resStack : Nat) :
    runSpecTightPlacedPreFd CodeOk A lim RunEnv uuidParse Run wrOk resStack =
      LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4PlacedBudgetFd.runSpecTightPlacedPreFd
        CodeOk A lim RunEnv uuidParse Run wrOk resStack :=
  rfl

/-- `HookSat` sibling of `b2MainRemainingHopsCapOf_of_allocFs_and_io_preFd`
    (`ElfSlicesPqOomH2KMainEntryFits.lean:1109`), dropping unused `err`. -/
theorem b2MainRemainingHopsCapOf_of_allocFs_and_io_preFd_sat [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hFs : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hioOf : MainIoOfPlacedFd (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W)
      cliIo hookStack ReadStdinBoundedEnv ReadEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hutf8 : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : HookSat (ext W) lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : HookSat (ext W) lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide) :
    B2MainRemainingHopsPreFd CodeOk mmpl ext W brkStart lim γ tp
      (B2St1CapOf fineCostModel lim cliIo ReadEnv uuidTryParse RunEnv Run)
      (B2St2CapOf fineCostModel lim cliIo ReadEnv RunEnv Run)
      (B2St3Cap fineCostModel lim cliIo RunEnv Run)
      (B2St4Cap fineCostModel lim)
      (B2St5Cap fineCostModel lim)
      RunEnv Run :=
  let hc := mainCalleesBlk617_of_allocFs_and_hooks_cliResStack_sat hFs hstrlen hutf8 hmemrchr hpan
  { step2 :=
      b2_step2_pool_placed_of_hooks_sat hc hstrlen hutf8RO hmemrchrRO
        cli_resStack_callees.2.2.1 cli_resStack_callees.2.2.2 hstk cli_hstk64
        (fun hst1 _ _ => hst1.1)
        (fun hst1 _ _ hevs_c hvcap hp => hst1.2 _ _ _ hevs_c hvcap hp)
    step3 := fun hst2 hs0fs hs0tr hstdin hcoinsOk hcoins hpc hs _hpan hexit hnext =>
      main_m3_bounded_readOf_pool_placed_proof_fd hc hioOf hstk cli_hstk64 hs0fs hs0tr hstdin
        hcoinsOk hcoins hpc hst2.1 hs hexit
        fun s' cc cp ic ip evs hevs hin hat4 hfds' =>
          hnext s' cc cp ic ip _ ((hst2.2 evs hevs).2 hin) hin hat4 hfds'
    step4_overCap := fun _hst3 hsp hs0tr hpc hover hs hpan hexit =>
      main_m4_sendOverCap_pool_placed_proof hc hstk cli_hstk64 hsp hs0tr hpc hover hs hpan hexit
    step4_call := fun hrun {_i _a _c _w s0 _s _buf _p0 coinsCap coinsPtr _inCap inPtr _ps _st3 _Q _Qp}
        hst3 hsp hs0tr hRun hnover hpc hs hfds hpan hexit hnext =>
      let _ := coinsCap
      main_m4_pool_placed_proof_preFd hc
        (runSpecTightPlacedPreFd_eq_m4 CodeOk _ lim RunEnv uuidTryParse Run cliWrOk cliResStack ▸ hrun)
        hstk cli_hstk64 hsp hs0tr hRun
        (fun peer hc_eq => Nat.le_of_not_lt fun hgt => hnover ⟨⟨peer, hc_eq ▸ hpc⟩, hgt⟩)
        hpc
        (hst3.2 _
          (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64)
          (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64)
          (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64)
          inPtr coinsPtr hRun).1
        hs hfds hpan hexit
        fun s' sg out evs hevs hans hwr htr hat4e =>
          hnext s' sg out _
            (((hst3.2 _
              (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64)
              (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64)
              (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64)
              inPtr coinsPtr hRun).2 evs hevs).2 sg out hans hwr)
            hans hwr htr hat4e
    step5 := fun hst4 _hs0tr hpaths hs _hpan hnext =>
      main_m5_of_proof_placed hc hioOf.toWriteOnlyMainIo (hst4 false).seq_left hstk cli_hstk64
        hpaths hs
        fun s' _evs ok outCap outPtr hevs hcom htr hstdout hat6 =>
          hnext s' ok outCap outPtr _ ((hst4 ok).seq_right hevs) hcom htr hstdout hat6
    step6 := fun hst5 hs hexit =>
      main_m6_of_m6Env_pool_proof_placed hc hioOf.toWriteOnlyMainIo hst5 hstk cli_hstk64 hs hexit }

/-! ## SWAR-Padded Pre-Fd Block-`617` Hop Composer & `hhops`-Level `579 → 617` Lifts -/

/-- K-route SWAR-padded twin of `ElfSlicesPqOomH2KMainEntryFits.b2_main_ok_tight_needLocks_with_inv_placed_preFd`:
`step1` runs over `b2MainFrameFinePad` / `argvAtROPPad`, `sepWPp_argvAtROPPad_to_unpadded_needLocks`
peels the SWAR pad at `M1 → M2`, and `step3` threads `FdsGe3Closed s'.fs` into `step4_call`. -/
theorem b2_main_ok_tight_needLocks_with_inv_placed_preFd_pad [LibsignalPlacement]
    {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks}
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
        FdsGe3Closed s'.fs →
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
      FdsGe3Closed s.fs →
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
          · intro _ _ _ _ _ _ _ hin_le _ _
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
          · intro s3 coinsCap coinsPtr inCap inPtr st3 hst3 _ hs3 _hfds3
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
          · intro s3 coinsCap coinsPtr inCap inPtr st3 hst3 _ hs3 hfds3
            refine step4_call hst3 hsp htr0 hRun hnover hpc_parse hs3 hfds3 ?_ ?_ ?_
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

/-- Pure `HookSat (ext W) "strlen" (strlenSpecROSat hookStack)` K-route `579 → 617` lift
over `B2MainRemainingHopsPreFd` (zero `strlenHook`). -/
theorem b2MainSpecTightNeedLocksFineAtPad_of_runTight_lsmpl_preFd_sat [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : MultiPlacement} {ext : CliHooks → String → Option (State → State)}
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
      (runSpecTightPlacedPreFd CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse Run cliWrOk cliResStack))
    (hhops : B2MainRemainingHopsPreFd CodeOk mmpl ext W brkStart lim γ tp
      St1 St2 St3 St4 St5 RunEnv Run) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl) Run inputsOf) := by
  subst hlibc
  rw [← mProgPlaced_eq_cliProgExtPlacedAt ext W, cliStaticsPlacedAt_eq_cliStaticsPlaced]
  exact b2_main_ok_tight_needLocks_with_inv_placed_preFd_pad
    ⟨cliIo_stdin, cliIo_coinsPath, cliIo_coins, cliIo_commit⟩ hfs_eq
    (fun st' sf => hookPool_entails_needLocks_anyHeap γ mmpl tp brkStart lim st' sf)
    hparse mainFrameSize_le_cliMainStk hSt0
    (fun hst0 hs0 hok hpanic hexit hnext =>
      main_m1_ro_pool_placed_step1_of_sat hc_alloc hstrlenRO hstk cli_hstk64 hSt01
        hst0 hs0 hok hpanic hexit hnext)
    hhops.step2 hhops.step3 hhops.step4_overCap (hhops.step4_call hrun) hhops.step5 hhops.step6

/-- `domScopedRun Dom (runRel S)` specialization of
`b2MainSpecTightNeedLocksFineAtPad_of_runTight_lsmpl_preFd_sat` (zero `strlenHook`). -/
theorem b2MainSpecTightNeedLocksFineAtPad_of_domScopedRunSem_lsmpl_preFd_sat [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : MultiPlacement} {ext : CliHooks → String → Option (State → State)}
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
      (runSpecTightPlacedPreFd CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse (runRel S) cliWrOk cliResStack))
    (hhops : B2MainRemainingHopsPreFd CodeOk mmpl ext W brkStart lim γ tp
      St1 St2 St3 St4 St5 RunEnv (domScopedRun Dom (runRel S))) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl)
        (domScopedRun Dom (runRel S)) inputsOf) :=
  b2MainSpecTightNeedLocksFineAtPad_of_runTight_lsmpl_preFd_sat
    hlibc hfs_eq (hparse_of_domains fun _ _ hr => domScopedRun_dom hr)
    hstrlenRO hc_alloc hstk hSt0 hSt01
    (subroutine_ok_runSpecTightPlacedPreFd_mono_run (fun _ _ hr => hr.2) hrun)
    hhops

/-! ## Capped `MainEntryBudgetFitsCapOf` `579 → 617` & End-to-End `hmain` / `hover` `HookSat` Lifts -/

/-- `HookSat` sibling of `b2MainSpecTightNeedLocksFineAt_of_runTight_and_budgetFitsCapOf_lsmpl_preFd`
    (`ElfSlicesPqOomH2KMainEntryFits.lean:1219`), dropping unused `err` and routing `step1`
    through `HookSat … strlenSpecROSat` into `b2MainSpecTightNeedLocksFineAtPad`. -/
theorem b2MainSpecTightNeedLocksFineAt_of_runTight_and_budgetFitsCapOf_lsmpl_preFd_sat
    [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hFs : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hioOf : MainIoOfPlacedFd (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W)
      cliIo hookStack ReadStdinBoundedEnv ReadEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hstrlenRO : HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : HookSat (ext W) lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : HookSat (ext W) lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv
      uuidTryParse RunEnv Run)
    (hrun : subroutine_ok (mProgPlaced (ext W)) (lsmpl.base 579)
      (runSpecTightPlacedPreFd CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse Run cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl) Run inputsOf) :=
  b2MainSpecTightNeedLocksFineAtPad_of_runTight_lsmpl_preFd_sat
    hlibc hfs_eq hparse hstrlenRO hFs hstk
    (b2St0Cap_init fineCostModel fineCostModel.init)
    (b2St01_of_mainEntryBudgetFitsCapOf hfitCap)
    hrun
    (b2MainRemainingHopsCapOf_of_allocFs_and_io_preFd_sat
      hFs hioOf hstrlen hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk)

/-- `HookSat` sibling of `b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_lsmpl_preFd`
    (`ElfSlicesPqOomH2KMainEntryFits.lean:1260`), dropping unused `err`. -/
theorem b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_lsmpl_preFd_sat
    [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (Dom : Inputs → Prop) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hFs : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hioOf : MainIoOfPlacedFd (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W)
      cliIo hookStack ReadStdinBoundedEnv ReadEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hstrlenRO : HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : HookSat (ext W) lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : HookSat (ext W) lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv
      uuidTryParse RunEnv (domScopedRun Dom (runRel S)))
    (hrun : subroutine_ok (mProgPlaced (ext W)) (lsmpl.base 579)
      (runSpecTightPlacedPreFd CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse (runRel S) cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl)
        (domScopedRun Dom (runRel S)) inputsOf) :=
  b2MainSpecTightNeedLocksFineAtPad_of_domScopedRunSem_lsmpl_preFd_sat Dom S
    hlibc hfs_eq hstrlenRO hFs hstk
    (b2St0Cap_init fineCostModel fineCostModel.init)
    (b2St01_of_mainEntryBudgetFitsCapOf hfitCap)
    hrun
    (b2MainRemainingHopsCapOf_of_allocFs_and_io_preFd_sat
      hFs hioOf hstrlen hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk)

/-- `HookSat` sibling of `b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed_preFd`
    (`ElfSlicesPqOomH2KMainEntryFits.lean:1301`), dropping unused `err`. -/
theorem b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed_preFd_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (Dom : Inputs → Prop) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hFs : @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hioOf : @MainIoOfPlacedFd (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
      ReadStdinBoundedEnv ReadEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hstrlenRO : HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : HookSat (ext W) lsMemrchrSym
      (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
        (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : HookSat (ext W) lsMemrchrSym
      (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
        (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv
      uuidTryParse RunEnv (domScopedRun Dom (runRel S)))
    (hrun : @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
      (mpl.base 579)
      (@runSpecTightPlacedPreFd (libsignalPlacementOf mpl hblk hext_nodup) _
        CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse (runRel S)
        cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt mpl ext 617 W) (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
        (domScopedRun Dom (runRel S)) inputsOf) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  letI : LsCodeInv CodeOk := hCI
  exact b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_lsmpl_preFd_sat Dom S
    hlibc hfs_eq hFs hioOf hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk hfitCap
    hrun

/-- `HookSat` sibling of `mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCapOf_preFd`
    (`ElfSlicesPqOomH2KMainEntryFits.lean:1347`), dropping `errOf` and re-anchoring to
    `MainOkCliExtPqB2NeedLocksPadPlacedAt`. -/
theorem mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCapOf_preFd_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlacedFd (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hstrlenRO : ∀ W : CliHooks, HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlacedPreFd (libsignalPlacementOf mpl hblk hext_nodup) _
            CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPadPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPadPlacedAt_of_pqScopedMainSubroutine hblk hext_nodup
    fun h547 X W γ tp =>
      b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed_preFd_sat
        hblk hext_nodup hCI
        (CliPqxdhInputs ⟨W.C, W.Q⟩)
        (cliRunSemD2c_placed X W)
        hlibc initFsState_cliProcessInputs_eq
        (hFs W γ tp) (hioOf W γ tp)
        (hstrlen W) (hstrlenRO W) (hutf8 W) (hutf8RO W) (hmemrchr W) (hmemrchrRO W) (hpan W) hstk
        (hfitCap h547 X W γ tp) (hrun h547 X W γ tp)

/-- `HookSat` sibling of `mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCapOf_preFd`
    (`ElfSlicesPqOomH2KMainEntryFits.lean:1401`), dropping `errOf` and re-anchoring to
    `MainOkCliExtOverB2NeedLocksPadPlacedAt`. -/
theorem mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCapOf_preFd_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlacedFd (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstrlen : ∀ W : CliHooks, ext W "strlen" = some strlenHook)
    (hstrlenRO : ∀ W : CliHooks, HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : ∀ W : CliHooks,
      HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : ∀ W : CliHooks,
      HookSat (ext W) lsMemrchrSym
        (@withLsRet (libsignalPlacementOf mpl hblk hext_nodup) _
          (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ∀ W : CliHooks, ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlacedPreFd (libsignalPlacementOf mpl hblk hext_nodup) _
            CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPadPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPadPlacedAt_of_pqScopedMainSubroutine hblk hext_nodup
    fun h547 X W γ tp =>
      b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed_preFd_sat
        hblk hext_nodup hCI
        (CliPqxdhInputs ⟨W.C, W.Q⟩)
        (cliRunSemD2c_placed X W)
        hlibc initFsState_cliProcessInputs_eq
        (hFs W γ tp) (hioOf W γ tp)
        (hstrlen W) (hstrlenRO W) (hutf8 W) (hutf8RO W) (hmemrchr W) (hmemrchrRO W) (hpan W) hstk
        (hfitCap h547 X W γ tp) (hrun h547 X W γ tp)

/-- `toSat` bridge for `mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf_preFd`
    (`ElfSlicesPqOomH2KMainEntryFits.lean:1456`), discharging `hstrlenRO` via `hookSat_strlenRO_of_eq`
    and re-anchoring to `MainOkCliExtPqB2NeedLocksPadPlacedAt`. -/
theorem mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf_preFd_via_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ghOf W))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlacedFd (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlacedPreFd (libsignalPlacementOf mpl hblk hext_nodup) _
            CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPadPlacedAt mpl mmpl
      (fun W => cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCapOf_preFd_sat
    hblk hext_nodup hCI RunEnv hlibc
    (fun W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact allocContractsFsPlaced_of_hooks mmpl (ghOf W) W (hG W γ tp))
    hioOf
    (fun W => cliGhostExterns_strlen mmpl (ghOf W) W)
    (fun W => hookSat_strlenRO_of_eq hookStack (cliGhostExterns_strlen mmpl (ghOf W) W))
    (fun W => hookSat_fromUtf8Vm_of_eq hookStack (cliGhostExterns_fromUtf8_eq mmpl (ghOf W) W))
    (fun W => hookSat_fromUtf8ROVm_of_eq hookStack (cliGhostExterns_fromUtf8_eq mmpl (ghOf W) W))
    (fun W => @hookSat_memrchrVm_ls_of_eq (libsignalPlacementOf mpl hblk hext_nodup) _
      (cliGhostExterns_memrchr_eq mmpl (ghOf W) W))
    (fun W => @hookSat_memrchrROVm_ls_of_eq (libsignalPlacementOf mpl hblk hext_nodup) _
      extHookStack (cliGhostExterns_memrchr_eq mmpl (ghOf W) W))
    (fun W => cliGhostExterns_handleErrorMain mmpl (ghOf W) W)
    hstk hfitCap hrun

/-- `toSat` bridge for `mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf_preFd`
    (`ElfSlicesPqOomH2KMainEntryFits.lean:1511`), discharging `hstrlenRO` via `hookSat_strlenRO_of_eq`
    and re-anchoring to `MainOkCliExtOverB2NeedLocksPadPlacedAt`. -/
theorem mainOkCliExtOverB2NeedLocksPlacedAt_cliGhostExterns_of_runTight_and_budgetFitsCapOf_preFd_via_sat
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    (ghOf : CliHooks → CliGhostHooks)
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hG : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup) fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ghOf W))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlacedFd (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
        (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _
          (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)))
          (mpl.base 579)
          (@runSpecTightPlacedPreFd (libsignalPlacementOf mpl hblk hext_nodup) _
            CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPadPlacedAt mpl mmpl
      (fun W => cliGhostExterns (ghOf W) (cliExternsPlaced mmpl W)) 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCapOf_preFd_sat
    hblk hext_nodup hCI RunEnv hlibc
    (fun W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact allocContractsFsPlaced_of_hooks mmpl (ghOf W) W (hG W γ tp))
    hioOf
    (fun W => cliGhostExterns_strlen mmpl (ghOf W) W)
    (fun W => hookSat_strlenRO_of_eq hookStack (cliGhostExterns_strlen mmpl (ghOf W) W))
    (fun W => hookSat_fromUtf8Vm_of_eq hookStack (cliGhostExterns_fromUtf8_eq mmpl (ghOf W) W))
    (fun W => hookSat_fromUtf8ROVm_of_eq hookStack (cliGhostExterns_fromUtf8_eq mmpl (ghOf W) W))
    (fun W => @hookSat_memrchrVm_ls_of_eq (libsignalPlacementOf mpl hblk hext_nodup) _
      (cliGhostExterns_memrchr_eq mmpl (ghOf W) W))
    (fun W => @hookSat_memrchrROVm_ls_of_eq (libsignalPlacementOf mpl hblk hext_nodup) _
      extHookStack (cliGhostExterns_memrchr_eq mmpl (ghOf W) W))
    (fun W => cliGhostExterns_handleErrorMain mmpl (ghOf W) W)
    hstk hfitCap hrun

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMainEntryFitsSat
