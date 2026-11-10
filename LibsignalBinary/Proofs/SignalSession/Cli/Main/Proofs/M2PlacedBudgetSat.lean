/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRoA1PlacedBudgetSat -- proof-setup: allow-public-import

/-!
# `HookSat` Sibling of `M2PlacedBudget` (`M2PlacedBudgetSat`)

Replaces both `hutf8 : H lsFromUtf8Sym = some (fromUtf8Hook err)` (dropping `err`) and
`hmemrchr : H lsMemrchrSym = some memrchrHook` with `HookSat` contracts
(`withVmPreserved (fromUtf8AsciiSpecRO hookStack)` and
`withVmPreserved (memrchrSpecRO extHookStack)`) across
`main_m2_pool_placed_of_hooks_sat` and `b2_step2_pool_placed_of_hooks_sat`.
-/

public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2PlacedBudgetSat

open Arm64 Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (allocFailedIn)
open CryptoVerification.SignalSession
  (Inputs lsFromUtf8Sym lsMemrchrSym strlenHook)
open CryptoVerification.SignalSession.Cli (CliInputsOk)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtCallPlaced AtM1EndPlaced CallV CallW LsCodeInv argsBuf callCellsPlaced callHeap locals
   mProgPlaced mainFrameSize mainSaved parseArgs)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRoA1PlacedBudgetSat
  (mainCalleesROBlk617_of_mainCalleesBlk617_and_hooks_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (argvAtROP)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (fromUtf8AsciiSpecRO memrchrSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.EntryPlacedBudget
  (M2CollectEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2DispatchPlacedBudget
  (m2DispatchEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2PlacedBudget
  (M2PreDeallocEnv main_m2_pool_placed_proof)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
  (ExitKPoolPlaced)

/-- `HookSat` sibling of `main_m2_pool_placed_of_hooks` (`M2PlacedBudget.lean:377`), weakening
    both `hutf8` and `hmemrchr` to `HookSat` and dropping `err`. -/
theorem main_m2_pool_placed_of_hooks_sat [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {i : Inputs} {s0 s : State} {stk hookStack resStack : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidTryParse hookStack resStack)
    (hstrlen : H "strlen" = some strlenHook)
    (hutf8 : HookSat H lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : HookSat H lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpecRO extHookStack))))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEnv M lim st (M2PreDeallocEnv uuidTryParse (i.argv.map bytesOfString)))
    (hs : AtM1EndPlaced CodeOk s0 s i.argv.length buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidTryParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (vcap : BitVec 64) (evs_c : List AllocEvent) (w : CallW) (c : CallV),
      M2CollectEnv i.argv.length evs_c →
      vcap ≠ 0#64 →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim
            (M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
              (M.stepEvents (m2DispatchEvents uuidTryParse (i.argv.map bytesOfString))
                (M.stepEvents evs_c st))) s' ∗
          Statics)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics)
      Q Qp oom :=
  main_m2_pool_placed_proof
    (mainCalleesROBlk617_of_mainCalleesBlk617_and_hooks_sat hc hstrlen hutf8 hmemrchr hres hres64)
    hstk hstk64 hok hne hps hfit hs hexit hnext

/-- `HookSat` sibling of `b2_step2_pool_placed_of_hooks` (`M2PlacedBudget.lean:475`), weakening
    both `hutf8` and `hmemrchr` to `HookSat` and dropping `err`. -/
theorem b2_step2_pool_placed_of_hooks_sat [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {stk hookStack resStack : Nat}
    {St1 : Inputs → M.σ → Prop} {St2 : Inputs → CallV → M.σ → Prop}
    (hc : MainCalleesBlk617 A lim H uuidTryParse hookStack resStack)
    (hstrlen : H "strlen" = some strlenHook)
    (hutf8 : HookSat H lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpecRO hookStack)))
    (hmemrchr : HookSat H lsMemrchrSym (withLsRet (withVmPreserved (memrchrSpecRO extHookStack))))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hfit_st1 : ∀ {i : Inputs} {st1 : M.σ}, St1 i st1 → CliInputsOk i → i.argv ≠ [] →
      FitsEnv M lim st1 (M2PreDeallocEnv uuidTryParse (i.argv.map bytesOfString)))
    (hst2 : ∀ {i : Inputs} {c : CallV} {st1 : M.σ} {vcap : BitVec 64} {evs_c : List AllocEvent},
      St1 i st1 → CliInputsOk i → i.argv ≠ [] →
      M2CollectEnv i.argv.length evs_c → vcap ≠ 0#64 →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      St2 i c
        (M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
          (M.stepEvents (m2DispatchEvents uuidTryParse (i.argv.map bytesOfString))
            (M.stepEvents evs_c st1)))) :
    ∀ {i : Inputs} {s0 s : State} {buf p0 : BitVec 64}
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
        Q Qp oom :=
  fun hst1 hok hne hps hs _hpanic hexit hnext =>
    main_m2_pool_placed_of_hooks_sat hc hstrlen hutf8 hmemrchr hres hres64 hstk hstk64 hok hne hps
      (hfit_st1 hst1 hok hne) hs hexit
      fun s' vcap evs_c w c hevs_c hvcap hp ha =>
        hnext s' w c _ (hst2 hst1 hok hne hevs_c hvcap hp) hp ha

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2PlacedBudgetSat
