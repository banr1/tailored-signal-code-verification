/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRoA1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.EntryPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2CollectPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2DispatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `main` Hop M2 (`M+0xc0 → M+0x568 / M+0xb80`, Block `617`)

Composes `M2CollectPlacedBudget` and `M2DispatchPlacedBudget` on Block `617` under
`RustCliAllocBudget M` and `M2PreDeallocEnv`, plus unconditional `MainCalleesBlk617` corollaries
discharging read-only `MainCalleesROBlk617`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2PlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.RustHeap (allocFailedIn)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliExternsPlaced fromUtf8Hook lsFromUtf8Sym lsMemrchrSym memrchrHook strlenHook)
open CryptoVerification.SignalSession.Cli (CliInputsOk)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtCallPlaced AtM1EndPlaced CallV CallW LsCodeInv argsBuf callCellsPlaced callHeap locals
   mProgPlaced mainFrameSize mainSaved parseArgs)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents OomPreserved RustCliAllocBudget SeqEnv
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRoA1PlacedBudget
  (mainCalleesROBlk617_of_mainCalleesBlk617_and_hooks
   mainCalleesROBlk617_of_mainCalleesBlk617_cliExterns)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (argvAtROP)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (MainCalleesROBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
  (ExitKPlaced MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.EntryPlacedBudget
  (M2CollectEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.StepsPlacedBudget
  (M2CollectLoopEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2CollectPlacedBudget
  (main_m2_collect_oom_placed main_m2_collect_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2DispatchPlacedBudget
  (M2DispatchEnv m2DispatchEvents main_m2_dispatch_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
  (ExitKPoolPlaced exitKPoolPlaced_of_exitKPlaced)

/-- Sequential `AllocEvent` envelope for `main`'s `M2` collect + dispatch phase prior to the tail
`vptr` deallocation (`rustDeallocEvents (vcap.toNat * 16) 8`). -/
def M2PreDeallocEnv (uuidParse : UuidParser) (args : List (List (BitVec 8))) :
    List AllocEvent → Prop :=
  SeqEnv (M2CollectEnv args.length) (M2DispatchEnv uuidParse args)

/-- Pool-preserving OOM-callback composition of `main_m2_collect_oom_placed` and
`main_m2_dispatch_pool_placed` (`M+0xc0 → M+0x568 / M+0xb80`). -/
theorem main_m2_placed_oom_pool_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {stk hookStack resStack : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hoom_cb : ∀ s_pre sf R',
      s_pre.trace = s0.trace → s_pre.fs = s0.fs →
      sf.status = .OutOfMemory →
      ¬ FitsEvents M lim st (rustAllocEvents 64 8) →
      OomPreserved s_pre sf →
      (sf.mem ⊨ anyHeap ∗ R') → (sf.mem ⊨ oom sf ∗ R'))
    (hfit_loop : 1 < i.argv.length →
      FitsEnv M lim (M.stepEvents (rustAllocEvents 64 8) st) (M2CollectLoopEnv i.argv.length 1))
    (hfit_disp : ∀ evs_c, M2CollectEnv i.argv.length evs_c →
      FitsEvents M lim (M.stepEvents evs_c st)
        (m2DispatchEvents uuidParse (i.argv.map bytesOfString)))
    (hs : AtM1EndPlaced CodeOk s0 s i.argv.length buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (vcap : BitVec 64) (evs_c : List AllocEvent) (w : CallW) (c : CallV),
      M2CollectEnv i.argv.length evs_c →
      vcap ≠ 0#64 →
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim
            (M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
              (M.stepEvents (m2DispatchEvents uuidParse (i.argv.map bytesOfString))
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
  main_m2_collect_oom_placed hc hstk hstk64 hok hne hps hoom_cb hfit_loop hs
    fun _s1 vcap _vptr evs_c hevs_c hd =>
      main_m2_dispatch_pool_placed hc hstk hstk64 hok hne hps (hfit_disp evs_c hevs_c) hd hexit
        fun s' w c hp ha => hnext s' vcap evs_c w c hevs_c hd.vcap_ne hp ha

theorem main_m2_placed_oom_proof [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {stk hookStack resStack : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hoom_cb : ∀ s_pre sf R',
      s_pre.trace = s0.trace → s_pre.fs = s0.fs →
      sf.status = .OutOfMemory →
      ¬ FitsEvents M lim st (rustAllocEvents 64 8) →
      OomPreserved s_pre sf →
      (sf.mem ⊨ anyHeap ∗ R') → (sf.mem ⊨ oom sf ∗ R'))
    (hfit_loop : 1 < i.argv.length →
      FitsEnv M lim (M.stepEvents (rustAllocEvents 64 8) st) (M2CollectLoopEnv i.argv.length 1))
    (hfit_disp : ∀ evs_c, M2CollectEnv i.argv.length evs_c →
      FitsEvents M lim (M.stepEvents evs_c st)
        (m2DispatchEvents uuidParse (i.argv.map bytesOfString)))
    (hs : AtM1EndPlaced CodeOk s0 s i.argv.length buf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (vcap : BitVec 64) (evs_c : List AllocEvent) (w : CallW) (c : CallV),
      M2CollectEnv i.argv.length evs_c →
      vcap ≠ 0#64 →
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim
            (M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
              (M.stepEvents (m2DispatchEvents uuidParse (i.argv.map bytesOfString))
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
  main_m2_placed_oom_pool_proof hc hstk hstk64 hok hne hps hoom_cb hfit_loop hfit_disp hs
    (exitKPoolPlaced_of_exitKPlaced hexit) hnext

/-- Pool-preserving composition of `main_m2_collect_placed` and `main_m2_dispatch_pool_placed`
(`M+0xc0 → M+0x568 / M+0xb80`). -/
theorem main_m2_pool_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {stk hookStack resStack : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEnv M lim st (M2PreDeallocEnv uuidParse (i.argv.map bytesOfString)))
    (hs : AtM1EndPlaced CodeOk s0 s i.argv.length buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (vcap : BitVec 64) (evs_c : List AllocEvent) (w : CallW) (c : CallV),
      M2CollectEnv i.argv.length evs_c →
      vcap ≠ 0#64 →
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim
            (M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
              (M.stepEvents (m2DispatchEvents uuidParse (i.argv.map bytesOfString))
                (M.stepEvents evs_c st))) s' ∗
          Statics)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics)
      Q Qp oom := by
  have hfit_c : FitsEnv M lim st (M2CollectEnv i.argv.length) := by
    simpa only [M2PreDeallocEnv, List.length_map] using hfit.seq_left
  exact main_m2_collect_placed hc hstk hstk64 hok hne hps hfit_c hs
    fun _s1 vcap _vptr evs_c hevs_c hd =>
      have hfit_d : FitsEvents M lim (M.stepEvents evs_c st)
          (m2DispatchEvents uuidParse (i.argv.map bytesOfString)) :=
        (hfit.seq_right (by simpa only [List.length_map] using hevs_c)) _ rfl
      main_m2_dispatch_pool_placed hc hstk hstk64 hok hne hps hfit_d hd hexit
        fun s' w c hp ha => hnext s' vcap evs_c w c hevs_c hd.vcap_ne hp ha

theorem main_m2_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {stk hookStack resStack : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEnv M lim st (M2PreDeallocEnv uuidParse (i.argv.map bytesOfString)))
    (hs : AtM1EndPlaced CodeOk s0 s i.argv.length buf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (vcap : BitVec 64) (evs_c : List AllocEvent) (w : CallW) (c : CallV),
      M2CollectEnv i.argv.length evs_c →
      vcap ≠ 0#64 →
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim
            (M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
              (M.stepEvents (m2DispatchEvents uuidParse (i.argv.map bytesOfString))
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
  main_m2_pool_placed_proof hc hstk hstk64 hok hne hps hfit hs
    (exitKPoolPlaced_of_exitKPlaced hexit) hnext

theorem main_m2_pool_placed_proof_any_st [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {stk hookStack resStack : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEnv M lim st (M2PreDeallocEnv uuidParse (i.argv.map bytesOfString)))
    (hs : AtM1EndPlaced CodeOk s0 s i.argv.length buf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (st' : M.σ) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st' s' ∗ Statics)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics)
      Q Qp oom :=
  main_m2_pool_placed_proof hc hstk hstk64 hok hne hps hfit hs hexit
    fun s' _vcap _evs_c w' c' _ _ hp ha => hnext s' _ w' c' hp ha

theorem main_m2_placed_proof_any_st [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {stk hookStack resStack : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEnv M lim st (M2PreDeallocEnv uuidParse (i.argv.map bytesOfString)))
    (hs : AtM1EndPlaced CodeOk s0 s i.argv.length buf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (st' : M.σ) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st' s' ∗ Statics)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics)
      Q Qp oom :=
  main_m2_pool_placed_proof_any_st hc hstk hstk64 hok hne hps hfit hs
    (exitKPoolPlaced_of_exitKPlaced hexit) hnext

/-! ## Unconditional `MainCalleesBlk617` Corollaries for `B2MainFrameComposeBudget` (`step2`) -/

/-- Unconditional `MainCalleesBlk617` wrapper around `main_m2_pool_placed_proof` for
`uuidTryParse`, discharging `MainCalleesROBlk617` via
`AddressRoA1PlacedBudget.mainCalleesROBlk617_of_mainCalleesBlk617_and_hooks`. -/
theorem main_m2_pool_placed_of_hooks [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    {i : Inputs} {s0 s : State} {stk hookStack resStack : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim H uuidTryParse hookStack resStack)
    (hstrlen : H "strlen" = some strlenHook)
    (hutf8 : H lsFromUtf8Sym = some (fromUtf8Hook err))
    (hmemrchr : H lsMemrchrSym = some memrchrHook)
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
    (mainCalleesROBlk617_of_mainCalleesBlk617_and_hooks hc hstrlen hutf8 hmemrchr hres hres64)
    hstk hstk64 hok hne hps hfit hs hexit hnext

/-- Specialization of `main_m2_pool_placed_of_hooks` to `cliExternsPlaced mmpl W` via
`AddressRoA1PlacedBudget.mainCalleesROBlk617_of_mainCalleesBlk617_cliExterns`. -/
theorem main_m2_pool_placed_cliExterns [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {i : Inputs} {s0 s : State} {stk hookStack resStack : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A lim (cliExternsPlaced mmpl W) uuidTryParse hookStack resStack)
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEnv M lim st (M2PreDeallocEnv uuidTryParse (i.argv.map bytesOfString)))
    (hs : AtM1EndPlaced CodeOk s0 s i.argv.length buf)
    (hexit : ExitKPoolPlaced CodeOk (cliExternsPlaced mmpl W) A lim s0 stk
      (fun code s' => code = 2 ∧ parseArgs uuidTryParse (i.argv.map bytesOfString) = none ∧
        s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp)
    (hnext : ∀ (s' : State) (vcap : BitVec 64) (evs_c : List AllocEvent) (w : CallW) (c : CallV),
      M2CollectEnv i.argv.length evs_c →
      vcap ≠ 0#64 →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      ProofLib.SepWPp (mProgPlaced (cliExternsPlaced mmpl W)) (s0.readReg64 .lr) s'
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
    ProofLib.SepWPp (mProgPlaced (cliExternsPlaced mmpl W)) (s0.readReg64 .lr) s
      (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics)
      Q Qp oom :=
  main_m2_pool_placed_proof
    (mainCalleesROBlk617_of_mainCalleesBlk617_cliExterns mmpl W hc hres hres64)
    hstk hstk64 hok hne hps hfit hs hexit hnext

/-- Ready-made `step2` discharge for `B2MainFrameComposeBudget.b2MainSpecTightNeedLocksFineAt_of_steps`
over any `H : LibsignalHooks` satisfying `MainCalleesBlk617` and the three hook equalities. -/
theorem b2_step2_pool_placed_of_hooks [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    {stk hookStack resStack : Nat}
    {St1 : Inputs → M.σ → Prop} {St2 : Inputs → CallV → M.σ → Prop}
    (hc : MainCalleesBlk617 A lim H uuidTryParse hookStack resStack)
    (hstrlen : H "strlen" = some strlenHook)
    (hutf8 : H lsFromUtf8Sym = some (fromUtf8Hook err))
    (hmemrchr : H lsMemrchrSym = some memrchrHook)
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
    main_m2_pool_placed_of_hooks hc hstrlen hutf8 hmemrchr hres hres64 hstk hstk64 hok hne hps
      (hfit_st1 hst1 hok hne) hs hexit
      fun s' vcap evs_c w c hevs_c hvcap hp ha =>
        hnext s' w c _ (hst2 hst1 hok hne hevs_c hvcap hp) hp ha

/-- Ready-made `step2` discharge specialized to `cliExternsPlaced mmpl W`. -/
theorem b2_step2_pool_placed_cliExterns [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {stk hookStack resStack : Nat}
    {St1 : Inputs → M.σ → Prop} {St2 : Inputs → CallV → M.σ → Prop}
    (hc : MainCalleesBlk617 A lim (cliExternsPlaced mmpl W) uuidTryParse hookStack resStack)
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
      ExitKPoolPlaced CodeOk (cliExternsPlaced mmpl W) A lim s0 stk
        (fun code s' => code = 2 ∧ parseArgs uuidTryParse (i.argv.map bytesOfString) = none ∧
          s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp →
      (∀ (s' : State) (w : CallW) (c : CallV) (st2 : M.σ),
        St2 i c st2 →
        parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
        AtCallPlaced CodeOk s0 s' w i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced (cliExternsPlaced mmpl W)) (s0.readReg64 .lr) s'
          (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st2 s' ∗ Statics)
          Q Qp oom) →
      ProofLib.SepWPp (mProgPlaced (cliExternsPlaced mmpl W)) (s0.readReg64 .lr) s
        (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st1 s ∗ Statics)
        Q Qp oom :=
  fun hst1 hok hne hps hs _hpanic hexit hnext =>
    main_m2_pool_placed_cliExterns mmpl W hc hres hres64 hstk hstk64 hok hne hps
      (hfit_st1 hst1 hok hne) hs hexit
      fun s' vcap evs_c w c hevs_c hvcap hp ha =>
        hnext s' w c _ (hst2 hst1 hok hne hevs_c hvcap hp) hp ha

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2PlacedBudget
