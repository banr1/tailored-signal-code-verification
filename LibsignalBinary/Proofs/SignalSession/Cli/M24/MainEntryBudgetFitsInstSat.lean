/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesROSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlacedPadSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1PlacedBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2PlacedBudgetSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `HookSat` Sibling of `MainEntryBudgetFitsInst` (`MainEntryBudgetFitsInstSat`)

Replaces both exact-hook hypotheses
- `hutf8 : H lsFromUtf8Sym = some (fromUtf8Hook err)` / `∀ W, ext W lsFromUtf8Sym = some (fromUtf8Hook (errOf W))`
  (dropping unused `err` / `errOf`), and
- `hmemrchr : H lsMemrchrSym = some memrchrHook` / `∀ W, ext W lsMemrchrSym = some memrchrHook`
with `HookSat` RW (`withVmPreserved (fromUtf8AsciiSpec hookStack)`, `withVmPreserved (memrchrSpec extHookStack)`)
and RO (`withVmPreserved (fromUtf8AsciiSpecRO hookStack)`, `withVmPreserved (memrchrSpecRO extHookStack)`)
contracts across all 14 general-`H` / general-`ext` theorems of `MainEntryBudgetFitsInst`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInstSat

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns
   ls_externAt?_of_mem ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles subroutine_ok_rocl_of_plain withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet
  (doReserveStackX extHookStack finishGrowStackX)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs cliProcessInputs fromUtf8Hook libsignalSessionLib
   lsFromUtf8Sym lsMemrchrSym strlenHook)
open CryptoVerification.SignalSession.Cli (RunAnswer cliInputs)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_588)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (LsCodeInv RunCall cliIo cliMainStk cliResStack cliWrOk cli_hstk64 cli_resStack_callees
   fromUtf8AsciiSpec fromUtf8Hook_ok lsHandleErrorSymMain mProgPlaced mainFrameSize
   memrchrSpec parseArgs strlenHook_ok)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runRel)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine
  (fineCostModel fineHookRustCliAllocBudget fromUtf8Hook_vmPreserved strlenHook_vmPreserved)
open LibsignalBinary.Heap.SpecBudget (hookSat_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad
  (b2MainSpecTightNeedLocksFineAtPad hookSat_strlenHook_ro_sat strlenSpecROSat)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
  (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudgetSat
  (b2MainSpecTightNeedLocksFineAtPad_of_domScopedRunSem_lsmpl_sat
   b2MainSpecTightNeedLocksFineAtPad_of_runTight_lsmpl_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (fromUtf8AsciiSpecRO memrchrSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced (cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlacedPadSat
  (MainOkCliExtOverB2NeedLocksPadPlacedAt MainOkCliExtPqB2NeedLocksPadPlacedAt
   mainOkCliExtOverB2NeedLocksPadPlacedAt_of_pqScopedMainSubroutine
   mainOkCliExtPqB2NeedLocksPadPlacedAt_of_pqScopedMainSubroutine)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
  (B2St1Cap B2St1CapOf B2St2Cap B2St2CapOf B2St3Cap B2St4Cap B2St5Cap
   MainEntryBudgetFitsCap MainEntryBudgetFitsCapOf
   b2St0Cap_init b2St01_of_mainEntryBudgetFitsCap b2St01_of_mainEntryBudgetFitsCapOf
   domScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoBoundedPlaced MainIoOfPlaced ReadStdinBoundedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
  (B2MainRemainingHops cliRunSemD2c_placed initFsState_cliProcessInputs_eq pqScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
  (MainCalleesBlk617 runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1PlacedBudgetSat
  (address_placed_ok_a1_of_hooks_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1PlacedBudget
  (allocContractsFsPlaced_toAllocContractsX)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
  (AllocContractsFsPlaced.shim2_rocl)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2PlacedBudgetSat
  (b2_step2_pool_placed_of_hooks_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudget
  (main_m3_bounded_pool_placed_proof main_m3_bounded_readOf_pool_placed_proof)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4PlacedBudget
  (main_m4_pool_placed_proof main_m4_sendOverCap_pool_placed_proof)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5PlacedBudget
  (main_m5_of_proof_placed main_m5_proof_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M6PlacedBudget
  (main_m6_m6Env_pool_proof_placed main_m6_of_m6Env_pool_proof_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11PlacedBudget
  (allocNoOomExtern_fs_rocl reserve16_placed_ok reserve1_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.TryAllocateIn3PlacedBudget
  (tryAllocateIn3_placed_okFs_of_hooks_at)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced MainIoPlaced)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

private theorem ls_hook_placed_rocl_ok_local [LibsignalPlacement] {α : Type}
    {H : LibsignalHooks} {sym : String} {spec : Spec α}
    (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide) :
    subroutine_ok (lsProg_617 H) (lsρ sym) (withLsRoCl lsmpl spec) :=
  subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hsat hmem

/-- Exact-hook to `HookSat` bridge (`toSat`) for `withVmPreserved (fromUtf8AsciiSpec hookStack)`. -/
theorem hookSat_fromUtf8Vm_of_eq {H : LibsignalHooks} (hookStack : Nat)
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    (hutf8 : H lsFromUtf8Sym = some (fromUtf8Hook err)) :
    HookSat H lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)) :=
  hookSat_withVmPreserved ⟨fromUtf8Hook err, hutf8, fromUtf8Hook_ok hookStack err⟩
    (fun f hf s => by
      cases hutf8.symm.trans hf
      exact fromUtf8Hook_vmPreserved err s)

/-- Exact-hook to `HookSat` bridge (`toSat`) for `strlenSpecROSat hookStack`. -/
theorem hookSat_strlenRO_of_eq {H : LibsignalHooks} (hookStack : Nat)
    (hstrlen : H "strlen" = some strlenHook) :
    HookSat H "strlen" (strlenSpecROSat hookStack) :=
  hookSat_strlenHook_ro_sat hstrlen

/-- `HookSat` sibling of `mainCalleesBlk617_of_allocFs_and_hooks`
    (`MainEntryBudgetFitsInst.lean:353`), dropping unused `err`. -/
theorem mainCalleesBlk617_of_allocFs_and_hooks_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {hookStack resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstrlen : H "strlen" = some strlenHook)
    (hutf8 : HookSat H lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hmemrchr : HookSat H lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpec extHookStack))))
    (hpan : H lsHandleErrorSymMain = some Rust.panicked)
    (hfg : finishGrowStackX ≤ resStack)
    (hdr : doReserveStackX ≤ resStack)
    (haddr : 0xB0 + extHookStack ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63) :
    MainCalleesBlk617 A lim H uuidTryParse hookStack resStack where
  alloc := allocContractsFsPlaced_toAllocContractsX hFs
  allocFs := hFs
  strlen := ls_hook_placed_rocl_ok_local <|
    hookSat_withVmPreserved ⟨strlenHook, hstrlen, strlenHook_ok hookStack⟩
      (fun f hf s => by
        cases hstrlen.symm.trans hf
        exact strlenHook_vmPreserved s)
  fromUtf8 := ls_hook_placed_rocl_ok_local hutf8
  address := address_placed_ok_a1_of_hooks_sat hFs hmemrchr haddr hres64
  reserve16 := reserve16_placed_ok hFs hdr hpan
  reserve1 := reserve1_placed_ok hFs hdr hpan
  tryAllocateIn3 :=
    tryAllocateIn3_placed_okFs_of_hooks_at
      (prog := lsProg_617 H) (i := 617)
      (AllocContractsFsPlaced.shim2_rocl (prog := lsProg_588 H) (i := 588) hFs)
      (allocNoOomExtern_fs_rocl (prog := lsProg_588 H) (i := 588) hFs)
      hfg hres64
  handleErrorPanic :=
    (ls_externAt?_of_mem (prog := lsProg_617 H) (i := 617) (by decide)).trans hpan

/-- `HookSat` sibling of `mainCalleesBlk617_of_allocFs_and_hooks_cliResStack`
    (`MainEntryBudgetFitsInst.lean:392`). -/
theorem mainCalleesBlk617_of_allocFs_and_hooks_cliResStack_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {hookStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstrlen : H "strlen" = some strlenHook)
    (hutf8 : HookSat H lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hmemrchr : HookSat H lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpec extHookStack))))
    (hpan : H lsHandleErrorSymMain = some Rust.panicked) :
    MainCalleesBlk617 A lim H uuidTryParse hookStack cliResStack :=
  mainCalleesBlk617_of_allocFs_and_hooks_sat hFs hstrlen hutf8 hmemrchr hpan
    cli_resStack_callees.1 cli_resStack_callees.2.1
    cli_resStack_callees.2.2.1 cli_resStack_callees.2.2.2

/-- `HookSat` sibling of `b2MainRemainingHopsCap_of_allocFs_and_io`
    (`MainEntryBudgetFitsInst.lean:760`). -/
theorem b2MainRemainingHopsCap_of_allocFs_and_io_sat [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hFs : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : MainIoPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : MainIoBoundedPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W)
      cliIo hookStack ReadStdinBoundedEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hutf8 : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : HookSat (ext W) lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : HookSat (ext W) lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide) :
    B2MainRemainingHops CodeOk mmpl ext W brkStart lim γ tp
      (B2St1Cap fineCostModel lim cliIo uuidTryParse RunEnv Run)
      (B2St2Cap fineCostModel lim cliIo RunEnv Run)
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
      main_m3_bounded_pool_placed_proof hc hioBounded hstk cli_hstk64 hs0fs hs0tr hstdin
        hcoinsOk hcoins hpc hst2.1 hs hexit
        fun s' cc cp ic ip evs hevs hin hat4 =>
          hnext s' cc cp ic ip _ ((hst2.2 evs hevs).2 hin) hin hat4
    step4_overCap := fun _hst3 hsp hs0tr hpc hover hs hpan hexit =>
      main_m4_sendOverCap_pool_placed_proof hc hstk cli_hstk64 hsp hs0tr hpc hover hs hpan hexit
    step4_call := fun hrun {_i _a _c _w s0 _s _buf _p0 coinsCap coinsPtr _inCap inPtr _ps _st3 _Q _Qp}
        hst3 hsp hs0tr hRun hnover hpc hs hpan hexit hnext =>
      let _ := coinsCap
      main_m4_pool_placed_proof hc hrun hstk cli_hstk64 hsp hs0tr hRun
        (fun peer hc_eq => Nat.le_of_not_lt fun hgt => hnover ⟨⟨peer, hc_eq ▸ hpc⟩, hgt⟩)
        hpc
        (hst3.2 _
          (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64)
          (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64)
          (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64)
          inPtr coinsPtr hRun).1
        hs hpan hexit
        fun s' sg out evs hevs hans hwr htr hat4e =>
          hnext s' sg out _
            (((hst3.2 _
              (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64)
              (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64)
              (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64)
              inPtr coinsPtr hRun).2 evs hevs).2 sg out hans hwr)
            hans hwr htr hat4e
    step5 := fun hst4 _hs0tr hpaths hs _hpan hnext =>
      main_m5_proof_placed hc hio (hst4 false).seq_left hstk cli_hstk64 hpaths hs
        fun s' _evs ok outCap outPtr hevs hcom htr hstdout hat6 =>
          hnext s' ok outCap outPtr _ ((hst4 ok).seq_right hevs) hcom htr hstdout hat6
    step6 := fun hst5 hs hexit =>
      main_m6_m6Env_pool_proof_placed hc hio hst5 hstk cli_hstk64 hs hexit }

/-- `HookSat` sibling of `b2MainRemainingHopsCapOf_of_allocFs_and_io`
    (`MainEntryBudgetFitsInst.lean:893`). -/
theorem b2MainRemainingHopsCapOf_of_allocFs_and_io_sat [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hFs : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hioOf : MainIoOfPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W)
      cliIo hookStack ReadStdinBoundedEnv ReadEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hutf8 : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : HookSat (ext W) lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : HookSat (ext W) lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide) :
    B2MainRemainingHops CodeOk mmpl ext W brkStart lim γ tp
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
      main_m3_bounded_readOf_pool_placed_proof hc hioOf hstk cli_hstk64 hs0fs hs0tr hstdin
        hcoinsOk hcoins hpc hst2.1 hs hexit
        fun s' cc cp ic ip evs hevs hin hat4 =>
          hnext s' cc cp ic ip _ ((hst2.2 evs hevs).2 hin) hin hat4
    step4_overCap := fun _hst3 hsp hs0tr hpc hover hs hpan hexit =>
      main_m4_sendOverCap_pool_placed_proof hc hstk cli_hstk64 hsp hs0tr hpc hover hs hpan hexit
    step4_call := fun hrun {_i _a _c _w s0 _s _buf _p0 coinsCap coinsPtr _inCap inPtr _ps _st3 _Q _Qp}
        hst3 hsp hs0tr hRun hnover hpc hs hpan hexit hnext =>
      let _ := coinsCap
      main_m4_pool_placed_proof hc hrun hstk cli_hstk64 hsp hs0tr hRun
        (fun peer hc_eq => Nat.le_of_not_lt fun hgt => hnover ⟨⟨peer, hc_eq ▸ hpc⟩, hgt⟩)
        hpc
        (hst3.2 _
          (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64)
          (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64)
          (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64)
          inPtr coinsPtr hRun).1
        hs hpan hexit
        fun s' sg out evs hevs hans hwr htr hat4e =>
          hnext s' sg out _
            (((hst3.2 _
              (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1b8#64)
              (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64)
              (s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64)
              inPtr coinsPtr hRun).2 evs hevs).2 sg out hans hwr)
            hans hwr htr hat4e
    step5 := fun hst4 _hs0tr hpaths hs _hpan hnext =>
      main_m5_of_proof_placed hc hioOf (hst4 false).seq_left hstk cli_hstk64 hpaths hs
        fun s' _evs ok outCap outPtr hevs hcom htr hstdout hat6 =>
          hnext s' ok outCap outPtr _ ((hst4 ok).seq_right hevs) hcom htr hstdout hat6
    step6 := fun hst5 hs hexit =>
      main_m6_of_m6Env_pool_proof_placed hc hioOf hst5 hstk cli_hstk64 hs hexit }

/-! ## Capped `579 → 617` & End-to-End `hmain` / `hover` `HookSat` Lifts -/

/-- `HookSat` sibling of `b2MainSpecTightNeedLocksFineAt_of_runTight_and_budgetFitsCap_lsmpl`
    (`MainEntryBudgetFitsInst.lean:962`), routing `step1` through `HookSat … strlenSpecROSat`
    into SWAR-padded `b2MainSpecTightNeedLocksFineAtPad` while retaining dead `hstrlen` for
    `MainCalleesBlk617.strlen`. -/
theorem b2MainSpecTightNeedLocksFineAt_of_runTight_and_budgetFitsCap_lsmpl_sat [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Run : Inputs → RunAnswer → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hFs : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : MainIoPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : MainIoBoundedPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W)
      cliIo hookStack ReadStdinBoundedEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hstrlenRO : HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : HookSat (ext W) lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : HookSat (ext W) lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
      RunEnv Run)
    (hrun : subroutine_ok (mProgPlaced (ext W)) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse Run cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl) Run inputsOf) :=
  b2MainSpecTightNeedLocksFineAtPad_of_runTight_lsmpl_sat
    hlibc hfs_eq hparse hstrlenRO hFs hstk
    (b2St0Cap_init fineCostModel fineCostModel.init)
    (b2St01_of_mainEntryBudgetFitsCap hfitCap)
    hrun
    (b2MainRemainingHopsCap_of_allocFs_and_io_sat
      hFs hio hioBounded hstrlen hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk)

/-- `HookSat` sibling of `b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCap_lsmpl`
    (`MainEntryBudgetFitsInst.lean:1043`). -/
theorem b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCap_lsmpl_sat
    [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (Dom : Inputs → Prop) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hFs : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : MainIoPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : MainIoBoundedPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W)
      cliIo hookStack ReadStdinBoundedEnv)
    (hstrlen : ext W "strlen" = some strlenHook)
    (hstrlenRO : HookSat (ext W) "strlen" (strlenSpecROSat hookStack))
    (hutf8 : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec hookStack)))
    (hutf8RO : HookSat (ext W) lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : HookSat (ext W) lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpec extHookStack))))
    (hmemrchrRO : HookSat (ext W) lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpecRO extHookStack))))
    (hpan : ext W lsHandleErrorSymMain = some Rust.panicked)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hfitCap : MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
      RunEnv (domScopedRun Dom (runRel S)))
    (hrun : subroutine_ok (mProgPlaced (ext W)) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse (runRel S) cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl)
        (domScopedRun Dom (runRel S)) inputsOf) :=
  b2MainSpecTightNeedLocksFineAtPad_of_domScopedRunSem_lsmpl_sat Dom S
    hlibc hfs_eq hstrlenRO hFs hstk
    (b2St0Cap_init fineCostModel fineCostModel.init)
    (b2St01_of_mainEntryBudgetFitsCap hfitCap)
    hrun
    (b2MainRemainingHopsCap_of_allocFs_and_io_sat
      hFs hio hioBounded hstrlen hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk)

/-- `HookSat` sibling of `b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCap_placed`
    (`MainEntryBudgetFitsInst.lean:1083`). -/
theorem b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCap_placed_sat
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (Dom : Inputs → Prop) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hFs : @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
      ReadStdinBoundedEnv)
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
    (hfitCap : MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
      RunEnv (domScopedRun Dom (runRel S)))
    (hrun : @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
      (mpl.base 579)
      (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse (runRel S)
        cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt mpl ext 617 W) (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
        (domScopedRun Dom (runRel S)) inputsOf) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  letI : LsCodeInv CodeOk := hCI
  exact b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCap_lsmpl_sat Dom S
    hlibc hfs_eq hFs hio hioBounded hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO hpan
    hstk hfitCap hrun

/-- `HookSat` sibling of `mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap`
    (`MainEntryBudgetFitsInst.lean:1135`), dropping `errOf` and re-anchoring to
    `MainOkCliExtPqB2NeedLocksPadPlacedAt`. -/
theorem mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap_sat
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
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
        MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPadPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPadPlacedAt_of_pqScopedMainSubroutine hblk hext_nodup
    fun h547 X W γ tp =>
      b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCap_placed_sat
        hblk hext_nodup hCI
        (CliPqxdhInputs ⟨W.C, W.Q⟩)
        (cliRunSemD2c_placed X W)
        hlibc initFsState_cliProcessInputs_eq
        (hFs W γ tp) (hio W γ tp) (hioBounded W γ tp)
        (hstrlen W) (hstrlenRO W) (hutf8 W) (hutf8RO W) (hmemrchr W) (hmemrchrRO W) (hpan W) hstk
        (hfitCap h547 X W γ tp) (hrun h547 X W γ tp)

/-- `HookSat` sibling of `mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap`
    (`MainEntryBudgetFitsInst.lean:1194`), dropping `errOf` and re-anchoring to
    `MainOkCliExtOverB2NeedLocksPadPlacedAt`. -/
theorem mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCap_sat
    {mpl mmpl : Obj.MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {CodeOk : Memory → Prop}
    (hCI : @LsCodeInv (libsignalPlacementOf mpl hblk hext_nodup) CodeOk)
    {ext : CliHooks → String → Option (State → State)}
    {libcAddr brkStart : BitVec 64} {lim : BudgetLimits} {hookStack : Nat}
    (RunEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      RunCall → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hFs : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @AllocContractsFsPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hio : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack)
    (hioBounded : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoBoundedPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W) cliIo hookStack
        ReadStdinBoundedEnv)
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
        MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
          (RunEnv X W γ tp)
          (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))))
    (hrun : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @subroutine_ok _ (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup) (ext W))
          (mpl.base 579)
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPadPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPadPlacedAt_of_pqScopedMainSubroutine hblk hext_nodup
    fun h547 X W γ tp =>
      b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCap_placed_sat
        hblk hext_nodup hCI
        (CliPqxdhInputs ⟨W.C, W.Q⟩)
        (cliRunSemD2c_placed X W)
        hlibc initFsState_cliProcessInputs_eq
        (hFs W γ tp) (hio W γ tp) (hioBounded W γ tp)
        (hstrlen W) (hstrlenRO W) (hutf8 W) (hutf8RO W) (hmemrchr W) (hmemrchrRO W) (hpan W) hstk
        (hfitCap h547 X W γ tp) (hrun h547 X W γ tp)

/-- `HookSat` sibling of `b2MainSpecTightNeedLocksFineAt_of_runTight_and_budgetFitsCapOf_lsmpl`
    (`MainEntryBudgetFitsInst.lean:1890`). -/
theorem b2MainSpecTightNeedLocksFineAt_of_runTight_and_budgetFitsCapOf_lsmpl_sat [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
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
    (hioOf : MainIoOfPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W)
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
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse Run cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl) Run inputsOf) :=
  b2MainSpecTightNeedLocksFineAtPad_of_runTight_lsmpl_sat
    hlibc hfs_eq hparse hstrlenRO hFs hstk
    (b2St0Cap_init fineCostModel fineCostModel.init)
    (b2St01_of_mainEntryBudgetFitsCapOf hfitCap)
    hrun
    (b2MainRemainingHopsCapOf_of_allocFs_and_io_sat
      hFs hioOf hstrlen hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk)

/-- `HookSat` sibling of `b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_lsmpl`
    (`MainEntryBudgetFitsInst.lean:1929`). -/
theorem b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_lsmpl_sat
    [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {W : CliHooks} {libcAddr brkStart : BitVec 64} {lim : BudgetLimits}
    {γ : GhostName} {tp : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (Dom : Inputs → Prop) (S : RunSem)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hFs : AllocContractsFsPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W))
    (hioOf : MainIoOfPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (ext W)
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
      (runSpecTightPlaced CodeOk (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim RunEnv uuidTryParse (runRel S) cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt lsmpl ext 617 W) (lsmpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt lsmpl)
        (domScopedRun Dom (runRel S)) inputsOf) :=
  b2MainSpecTightNeedLocksFineAtPad_of_domScopedRunSem_lsmpl_sat Dom S
    hlibc hfs_eq hstrlenRO hFs hstk
    (b2St0Cap_init fineCostModel fineCostModel.init)
    (b2St01_of_mainEntryBudgetFitsCapOf hfitCap)
    hrun
    (b2MainRemainingHopsCapOf_of_allocFs_and_io_sat
      hFs hioOf hstrlen hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk)

/-- `HookSat` sibling of `b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed`
    (`MainEntryBudgetFitsInst.lean:1969`). -/
theorem b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed_sat
    {mpl mmpl : Obj.MultiPlacement}
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
    (hioOf : @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
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
      (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim RunEnv uuidTryParse (runRel S)
        cliWrOk cliResStack)) :
    subroutine_ok (cliProgExtPlacedAt mpl ext 617 W) (mpl.base 617)
      (b2MainSpecTightNeedLocksFineAtPad libcAddr CodeOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
        (domScopedRun Dom (runRel S)) inputsOf) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  letI : LsCodeInv CodeOk := hCI
  exact b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_lsmpl_sat Dom S
    hlibc hfs_eq hFs hioOf hstrlen hstrlenRO hutf8 hutf8RO hmemrchr hmemrchrRO hpan hstk hfitCap hrun

/-- `HookSat` sibling of `mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCapOf`
    (`MainEntryBudgetFitsInst.lean:2016`), dropping `errOf` and re-anchoring to
    `MainOkCliExtPqB2NeedLocksPadPlacedAt`. -/
theorem mainOkCliExtPqB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCapOf_sat
    {mpl mmpl : Obj.MultiPlacement}
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
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
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
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtPqB2NeedLocksPadPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtPqB2NeedLocksPadPlacedAt_of_pqScopedMainSubroutine hblk hext_nodup
    fun h547 X W γ tp =>
      b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed_sat
        hblk hext_nodup hCI
        (CliPqxdhInputs ⟨W.C, W.Q⟩)
        (cliRunSemD2c_placed X W)
        hlibc initFsState_cliProcessInputs_eq
        (hFs W γ tp) (hioOf W γ tp)
        (hstrlen W) (hstrlenRO W) (hutf8 W) (hutf8RO W) (hmemrchr W) (hmemrchrRO W) (hpan W) hstk
        (hfitCap h547 X W γ tp) (hrun h547 X W γ tp)

/-- `HookSat` sibling of `mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCapOf`
    (`MainEntryBudgetFitsInst.lean:2071`), dropping `errOf` and re-anchoring to
    `MainOkCliExtOverB2NeedLocksPadPlacedAt`. -/
theorem mainOkCliExtOverB2NeedLocksPlacedAt_of_runTight_and_budgetFitsCapOf_sat
    {mpl mmpl : Obj.MultiPlacement}
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
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
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
          (@runSpecTightPlaced (libsignalPlacementOf mpl hblk hext_nodup)
            (libsignalPlacementOf mpl hblk hext_nodup) _ CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim (RunEnv X W γ tp) uuidTryParse
            (runRel (cliRunSemD2c_placed X W))
            cliWrOk cliResStack)) :
    MainOkCliExtOverB2NeedLocksPadPlacedAt mpl mmpl ext 617 cliProcessInputs CodeOk
      libcAddr brkStart cliMainStk lim :=
  mainOkCliExtOverB2NeedLocksPadPlacedAt_of_pqScopedMainSubroutine hblk hext_nodup
    fun h547 X W γ tp =>
      b2MainSpecTightNeedLocksFineAt_of_domScopedRunSem_and_budgetFitsCapOf_placed_sat
        hblk hext_nodup hCI
        (CliPqxdhInputs ⟨W.C, W.Q⟩)
        (cliRunSemD2c_placed X W)
        hlibc initFsState_cliProcessInputs_eq
        (hFs W γ tp) (hioOf W γ tp)
        (hstrlen W) (hstrlenRO W) (hutf8 W) (hutf8RO W) (hmemrchr W) (hmemrchrRO W) (hpan W) hstk
        (hfitCap h547 X W γ tp) (hrun h547 X W γ tp)

end LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInstSat
