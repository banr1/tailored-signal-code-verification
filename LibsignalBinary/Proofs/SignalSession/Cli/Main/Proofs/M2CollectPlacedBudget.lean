/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.EntryPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2CollectPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1Frame

/-!
# Budget-Threaded Relocatable `main` M2 Collect Half (`M+0xc0 → M+0x2f4 / M+0x1b0`)

Composes the budget-threaded first-element setup and `Vec<&str>` push loop on Block `617` with
read-only `argvAtROP`, advancing `A.pool` under `M2CollectEnv` from `AtM1EndPlaced` to
`AtM2DispatchPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2CollectPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli (CliInputsOk)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtM1EndPlaced AtM2DispatchPlaced LsCodeInv argsBuf argv_len_le fsp_spAligned locals
   mPcPlaced_eq mProgPlaced mProgPlaced_eq mainFrameSize mainSaved ps_getElem_bounds ps_length_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents OomPreserved RustCliAllocBudget
   rustAllocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (argvAtROP)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (MainCalleesROBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.EntryPlacedBudget
  (M2CollectEnv step_collect_first_oom_placed step_collect_first_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.StepsPlacedBudget
  (M2CollectLoopEnv m2EnvPlaced_init)

/-- OOM-callback form of `main`'s M2 argument collection (`M+0xc0 → M+0x2f4` if `i.argv.length = 2`,
else `M+0x1b0`) on Block `617` with `RustCliAllocBudget M` and `argvAtROP`. -/
theorem main_m2_collect_oom_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat}
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
    (hs : AtM1EndPlaced CodeOk s0 s i.argv.length buf)
    (hnext : ∀ (s' : State) (vcap vptr : BitVec 64) (evs : List AllocEvent),
      M2CollectEnv i.argv.length evs →
      AtM2DispatchPlaced CodeOk s0 s' i.argv.length buf vcap vptr →
      ProofLib.SepWPp (mProgPlaced H) ret s'
        (argsBuf A.repAlloc vcap vptr ps ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st) s' ∗ Statics)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) ret s
      (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics)
      Q Qp oom := by
  have hn1_le : 1 ≤ i.argv.length := by
    cases h : i.argv with
    | nil => exact False.elim (hne h)
    | cons _ _ => simp
  rw [mProgPlaced_eq]
  exact step_collect_first_oom_placed (m2EnvPlaced_init hc)
    hstk hstk64 hn1_le (argv_len_le hok) (ps_length_eq hps)
    (fun k hk => (ps_getElem_bounds hok hps k hk).1)
    hoom_cb hfit_loop
    ⟨by simpa only [mPcPlaced_eq] using hs.base.pc,
      hs.base.run, hs.base.sp, hs.base.fp, hs.base.inv,
      hs.base.vregs, hs.base.spAligned, fsp_spAligned hs.base.spAligned hs.base.sp⟩
    hs.x19 hs.x22 hs.x23 hs.x24 hs.x25 hs.trace hs.fs
    (fun s' vcap vptr evs hevs hf' hx19' hx20' hx21' hx23' hx24' htr' hfs' hvcap_ne' => by
      rw [← mProgPlaced_eq]
      exact hnext s' vcap vptr evs hevs
        ⟨⟨by simpa only [mPcPlaced_eq] using hf'.pc,
          hf'.run, hf'.sp, hf'.fp, hf'.inv, hf'.vregs, hf'.spAligned⟩,
          hf'.spAligned, hx19', hx20', hx21', hx23', hx24', hvcap_ne', htr', hfs'⟩)

/-- Argument-collection half of `main_m2` (`M+0xc0 → M+0x2f4` if `i.argv.length = 2`, else
`M+0x1b0`) on Block `617` under `FitsEnv M lim st (M2CollectEnv i.argv.length)` and `argvAtROP`. -/
theorem main_m2_collect_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEnv M lim st (M2CollectEnv i.argv.length))
    (hs : AtM1EndPlaced CodeOk s0 s i.argv.length buf)
    (hnext : ∀ (s' : State) (vcap vptr : BitVec 64) (evs : List AllocEvent),
      M2CollectEnv i.argv.length evs →
      AtM2DispatchPlaced CodeOk s0 s' i.argv.length buf vcap vptr →
      ProofLib.SepWPp (mProgPlaced H) ret s'
        (argsBuf A.repAlloc vcap vptr ps ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim (M.stepEvents evs st) s' ∗ Statics)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) ret s
      (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics)
      Q Qp oom := by
  have hn1_le : 1 ≤ i.argv.length := by
    cases h : i.argv with
    | nil => exact False.elim (hne h)
    | cons _ _ => simp
  rw [mProgPlaced_eq]
  exact step_collect_first_placed (m2EnvPlaced_init hc)
    hstk hstk64 hn1_le (argv_len_le hok) (ps_length_eq hps)
    (fun k hk => (ps_getElem_bounds hok hps k hk).1)
    hfit
    ⟨by simpa only [mPcPlaced_eq] using hs.base.pc,
      hs.base.run, hs.base.sp, hs.base.fp, hs.base.inv,
      hs.base.vregs, hs.base.spAligned, fsp_spAligned hs.base.spAligned hs.base.sp⟩
    hs.x19 hs.x22 hs.x23 hs.x24 hs.x25 hs.trace hs.fs
    (fun s' vcap vptr evs hevs hf' hx19' hx20' hx21' hx23' hx24' htr' hfs' hvcap_ne' => by
      rw [← mProgPlaced_eq]
      exact hnext s' vcap vptr evs hevs
        ⟨⟨by simpa only [mPcPlaced_eq] using hf'.pc,
          hf'.run, hf'.sp, hf'.fp, hf'.inv, hf'.vregs, hf'.spAligned⟩,
          hf'.spAligned, hx19', hx20', hx21', hx23', hx24', hvcap_ne', htr', hfs'⟩)

theorem main_m2_collect_placed_any_st [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hok : CliInputsOk i) (hne : i.argv ≠ [])
    (hps : ps.map (·.2) = i.argv.map bytesOfString)
    (hfit : FitsEnv M lim st (M2CollectEnv i.argv.length))
    (hs : AtM1EndPlaced CodeOk s0 s i.argv.length buf)
    (hnext : ∀ (s' : State) (st' : M.σ) (vcap vptr : BitVec 64),
      AtM2DispatchPlaced CodeOk s0 s' i.argv.length buf vcap vptr →
      ProofLib.SepWPp (mProgPlaced H) ret s'
        (argsBuf A.repAlloc vcap vptr ps ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st' s' ∗ Statics)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) ret s
      (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ Statics)
      Q Qp oom :=
  main_m2_collect_placed hc hstk hstk64 hok hne hps hfit hs
    fun s' vcap vptr _ _ hd => hnext s' _ vcap vptr hd

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2CollectPlacedBudget
