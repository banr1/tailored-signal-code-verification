/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.ParseFailPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.TopBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Parse-Failure Composition for `main` (Block `617`)

Composes budget-threaded `main_m1`, `main_m2`, and `main_ret` placed hop contracts on inputs where
`parseArgs` returns `none` under `ParseFailEnvOf`, retaining `A.pool` into `ExitKPoolPlaced` (with
`ExitKPlaced` and `NeedLocks` corollaries).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.ParseFailPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli (CliInputsOk)
open CryptoVerification.SignalSession.Cli.MainHops
  (AtCallPlaced AtEntryPlaced AtM1EndPlaced AtRetPlaced CallV CallW argsBuf argvAtP
   callCellsPlaced callHeap locals mProgPlaced mainFrameSize mainOom mainSaved parseArgs)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget SeqEnv
   VmPreserved rustAllocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (argvAtROP)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced (b2MainFrameFine)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
  (ExitKPlaced MainCalleesBlk617 retMem)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
  (ExitKPoolPlaced main_ret_placed_needLocks_proof main_ret_placed_proof)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.TopBudget (mainFrame)

private theorem sepWPp_mono_post_placed {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hQ : ∀ sf Pf, Q sf Pf → Q' sf Pf)
    (h : ProofLib.SepWPp prog ret s P Q Qp oom) :
    ProofLib.SepWPp prog ret s P Q' Qp oom := by
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, Pf, hmf, hq⟩ | hpan | hoom
  · exact Or.inl ⟨hpc, hrun, Pf, hmf, hQ sf Pf hq⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hoom)

/-- Exact `AllocEvent` envelope along `main` on inputs where `parseArgs` returns `none`
(prior to the zero-cost `vptr` deallocation), parameterized by `M2PreDeallocEnv`. -/
def ParseFailEnvOf (M2PreDeallocEnv : List (List (BitVec 8)) → List AllocEvent → Prop)
    (i : Inputs) (evs : List AllocEvent) : Prop :=
  if i.argv = [] then evs = []
  else SeqEnv (· = rustAllocEvents (16 * i.argv.length) 8)
    (M2PreDeallocEnv (i.argv.map bytesOfString)) evs

/-- Generic pool-retaining composition of budgeted `main_m1`, `main_m2`, and `main_ret` placed hop
contracts on inputs where `parseArgs uuidParse (i.argv.map bytesOfString) = none`, parameterized
over `(EntryFrame, ArgvP)` and `M2PreDeallocEnv`. -/
theorem main_parseFail_pool_placed_of_hops [LibsignalPlacement] {CodeOk : Memory → Prop}
    {M : AllocCostModel} {H : LibsignalHooks}
    {EntryFrame :
      RustCliAllocBudget M → BudgetLimits → M.σ → Nat → SepProp → Inputs → State → SepProp}
    {ArgvP : BitVec 64 → List (BitVec 64 × List (BitVec 8)) → SepProp}
    {M2PreDeallocEnv : List (List (BitVec 8)) → List AllocEvent → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 : State}
    {stk hookStack resStack : Nat} {Statics OutPost : SepProp} {Qp : State → SepProp → Prop}
    (hm1 : ∀ {st : M.σ} {Q : State → SepProp → Prop},
      mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk →
      stk ≤ 2 ^ 63 →
      AtEntryPlaced CodeOk i s0 →
      CliInputsOk i →
      (i.argv ≠ [] → FitsEvents M lim st (rustAllocEvents (16 * i.argv.length) 8)) →
      ExitKPoolPlaced CodeOk H A lim s0 stk
        (fun code s => code = 2 ∧ i.argv = [] ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp →
      (∀ (s : State) (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) (p0 : BitVec 64),
        i.argv ≠ [] → ps.map (·.2) = i.argv.map bytesOfString →
        AtM1EndPlaced CodeOk s0 s i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
          (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            ArgvP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim (M.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st) s ∗ Statics)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0 (EntryFrame A lim st stk Statics i s0)
        Q Qp (mainOom s0))
    (hm2 : ∀ {st1 : M.σ} {s : State} {buf p0 : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {Q : State → SepProp → Prop},
      mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk →
      stk ≤ 2 ^ 63 →
      CliInputsOk i → i.argv ≠ [] →
      ps.map (·.2) = i.argv.map bytesOfString →
      FitsEnv M lim st1 (M2PreDeallocEnv (i.argv.map bytesOfString)) →
      AtM1EndPlaced CodeOk s0 s i.argv.length buf →
      ExitKPoolPlaced CodeOk H A lim s0 stk
        (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
          s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp →
      (∀ (s' : State) (st2 : M.σ) (w : CallW) (c : CallV),
        parseArgs uuidParse (i.argv.map bytesOfString) = some c →
        AtCallPlaced CodeOk s0 s' w i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            ArgvP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st2 s' ∗ Statics)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          ArgvP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st1 s ∗ Statics)
        Q Qp (mainOom s0))
    (hret : ∀ {s : State} {st_r : M.σ} {code : Nat},
      mainFrameSize ≤ stk → AtRetPlaced CodeOk s0 s code →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (CryptoVerification.SignalSession.Cli.MainHops.retMem (A.atState lim st_r s) s0 stk)
        (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code ∧ sf.trace = s.trace ∧
          sf.fs = s.fs ∧ (Pf ⊢ OutPost))
        Qp (mainOom s0))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtEntryPlaced CodeOk i s0) (hok : CliInputsOk i)
    (hfail : parseArgs uuidParse (i.argv.map bytesOfString) = none)
    (hfit : FitsEnv M lim st (ParseFailEnvOf M2PreDeallocEnv i)) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0 (EntryFrame A lim st stk Statics i s0)
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 2 ∧ sf.trace = s0.trace ∧
        sf.fs = s0.fs ∧ (Pf ⊢ OutPost))
      Qp (mainOom s0) := by
  let Q : State → SepProp → Prop :=
    fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
      (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 2 ∧ sf.trace = s0.trace ∧
      sf.fs = s0.fs ∧ (Pf ⊢ OutPost)
  have hstk_ret : mainFrameSize ≤ stk :=
    Nat.le_trans (Nat.le_add_right mainFrameSize _) hstk
  have hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s => code = 2 ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp :=
    fun s st_r code hs ⟨hcode, htr, hfs⟩ =>
      sepWPp_mono_post_placed
        (fun _ _ ⟨hsp, hcs, hx0, htr_f, hfs_f, hmem⟩ =>
          ⟨hsp, hcs, hx0.trans (congrArg (BitVec.ofNat 32) hcode),
            htr_f.trans htr, hfs_f.trans hfs, hmem⟩)
        (hret (st_r := st_r) hstk_ret hs)
  have hfit_m1 : i.argv ≠ [] → FitsEvents M lim st (rustAllocEvents (16 * i.argv.length) 8) :=
    fun hne => by
      have hseq : FitsEnv M lim st
          (SeqEnv (· = rustAllocEvents (16 * i.argv.length) 8)
            (M2PreDeallocEnv (i.argv.map bytesOfString))) :=
        fun evs hevs => hfit evs (by simp only [ParseFailEnvOf, hne, ↓reduceIte]; exact hevs)
      exact hseq.seq_left _ rfl
  exact hm1 hstk hstk64 hs0 hok hfit_m1
    (fun s st_r code hs ⟨hcode, _, htr, hfs⟩ => hexit s st_r code hs ⟨hcode, htr, hfs⟩)
    (fun s buf ps p0 hne hps hs1 => by
      have hseq : FitsEnv M lim st
          (SeqEnv (· = rustAllocEvents (16 * i.argv.length) 8)
            (M2PreDeallocEnv (i.argv.map bytesOfString))) :=
        fun evs hevs => hfit evs (by simp only [ParseFailEnvOf, hne, ↓reduceIte]; exact hevs)
      exact hm2 (p0 := p0) hstk hstk64 hok hne hps (hseq.seq_right rfl) hs1
        (fun s' st_r code hs' ⟨hcode, _, htr, hfs⟩ => hexit s' st_r code hs' ⟨hcode, htr, hfs⟩)
        (fun _ _ _ _ hparse _ => (nomatch hfail.symm.trans hparse)))

/-- `b2MainFrameFine` (`argvAtROP`) parse-failure composition on Block `617`, projecting
`((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ anyHeap` via
`RetPlacedBudget.main_ret_placed_needLocks_proof`. -/
theorem main_parseFail_b2NeedLocks_of_hops [LibsignalPlacement] {CodeOk : Memory → Prop}
    {M : AllocCostModel} {H : LibsignalHooks}
    {M2PreDeallocEnv : List (List (BitVec 8)) → List AllocEvent → Prop}
    {A : RustCliAllocBudget M} {libcAddr : BitVec 64} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 : State}
    {stk hookStack resStack : Nat} {Statics : SepProp} {Qp : State → SepProp → Prop}
    (hneed : ∀ (st' : M.σ) (sf : State),
      A.pool lim st' sf ⊢ ((libcAddr + 3#64) ↦₈ 0#8) ∗ anyHeap)
    (hm1 : ∀ {st : M.σ} {Q : State → SepProp → Prop},
      mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk →
      stk ≤ 2 ^ 63 →
      AtEntryPlaced CodeOk i s0 →
      CliInputsOk i →
      (i.argv ≠ [] → FitsEvents M lim st (rustAllocEvents (16 * i.argv.length) 8)) →
      ExitKPoolPlaced CodeOk H A lim s0 stk
        (fun code s => code = 2 ∧ i.argv = [] ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp →
      (∀ (s : State) (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) (p0 : BitVec 64),
        i.argv ≠ [] → ps.map (·.2) = i.argv.map bytesOfString →
        AtM1EndPlaced CodeOk s0 s i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
          (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim (M.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st) s ∗ Statics)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0 (b2MainFrameFine A lim st stk Statics i s0)
        Q Qp (mainOom s0))
    (hm2 : ∀ {st1 : M.σ} {s : State} {buf p0 : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {Q : State → SepProp → Prop},
      mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk →
      stk ≤ 2 ^ 63 →
      CliInputsOk i → i.argv ≠ [] →
      ps.map (·.2) = i.argv.map bytesOfString →
      FitsEnv M lim st1 (M2PreDeallocEnv (i.argv.map bytesOfString)) →
      AtM1EndPlaced CodeOk s0 s i.argv.length buf →
      ExitKPoolPlaced CodeOk H A lim s0 stk
        (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
          s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp →
      (∀ (s' : State) (st2 : M.σ) (w : CallW) (c : CallV),
        parseArgs uuidParse (i.argv.map bytesOfString) = some c →
        AtCallPlaced CodeOk s0 s' w i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st2 s' ∗ Statics)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtROP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st1 s ∗ Statics)
        Q Qp (mainOom s0))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtEntryPlaced CodeOk i s0) (hok : CliInputsOk i)
    (hfail : parseArgs uuidParse (i.argv.map bytesOfString) = none)
    (hfit : FitsEnv M lim st (ParseFailEnvOf M2PreDeallocEnv i)) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0 (b2MainFrameFine A lim st stk Statics i s0)
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 2 ∧ sf.trace = s0.trace ∧
        sf.fs = s0.fs ∧ (Pf ⊢ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ anyHeap))
      Qp (mainOom s0) :=
  main_parseFail_pool_placed_of_hops (EntryFrame := b2MainFrameFine) (ArgvP := argvAtROP)
    hm1 hm2
    (fun {_s} {st_r} {_code} hstk_ret hs =>
      sepWPp_mono_post_placed
        (fun _ _ ⟨hsp, hcs, hx0, htr, hfs, _, hPf⟩ => ⟨hsp, hcs, hx0, htr, hfs, hPf⟩)
        (main_ret_placed_needLocks_proof (st := st_r) hneed hstk_ret hs))
    hstk hstk64 hs0 hok hfail hfit

/-- `TopBudget.mainFrame` (`argvAtP`, `ExitKPlaced`) parse-failure composition on Block `617` using
`callCellsPlaced`. -/
theorem main_parseFail_placed_of_hops [LibsignalPlacement] {CodeOk : Memory → Prop}
    {M : AllocCostModel} {H : LibsignalHooks}
    {M2PreDeallocEnv : UuidParser → List (List (BitVec 8)) → List AllocEvent → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 : State}
    {stk hookStack resStack : Nat} {Statics : SepProp} {Qp : State → SepProp → Prop}
    (hm1 : ∀ {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
      {uuidParse : UuidParser} {i : Inputs} {s0 : State}
      {stk hookStack resStack : Nat} {Statics : SepProp} {Q Qp : State → SepProp → Prop},
      MainCalleesBlk617 A lim H uuidParse hookStack resStack →
      mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk →
      stk ≤ 2 ^ 63 →
      AtEntryPlaced CodeOk i s0 →
      CliInputsOk i →
      (i.argv ≠ [] → FitsEvents M lim st (rustAllocEvents (16 * i.argv.length) 8)) →
      ExitKPlaced CodeOk H A s0 stk
        (fun code s => code = 2 ∧ i.argv = [] ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp →
      (∀ (s : State) (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) (p0 : BitVec 64),
        i.argv ≠ [] → ps.map (·.2) = i.argv.map bytesOfString →
        AtM1EndPlaced CodeOk s0 s i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
          (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim (M.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st) s ∗ Statics)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0 (mainFrame A lim st stk Statics i s0)
        Q Qp (mainOom s0))
    (hm2 : ∀ {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
      {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
      {stk hookStack resStack : Nat} {buf p0 : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))}
      {Statics : SepProp} {Q Qp : State → SepProp → Prop},
      MainCalleesBlk617 A lim H uuidParse hookStack resStack →
      mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk →
      stk ≤ 2 ^ 63 →
      CliInputsOk i → i.argv ≠ [] →
      ps.map (·.2) = i.argv.map bytesOfString →
      FitsEnv M lim st (M2PreDeallocEnv uuidParse (i.argv.map bytesOfString)) →
      AtM1EndPlaced CodeOk s0 s i.argv.length buf →
      ExitKPlaced CodeOk H A s0 stk
        (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
          s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp →
      (∀ (s' : State) (st' : M.σ) (w : CallW) (c : CallV),
        parseArgs uuidParse (i.argv.map bytesOfString) = some c →
        AtCallPlaced CodeOk s0 s' w i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool lim st' s' ∗ Statics)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st s ∗ Statics)
        Q Qp (mainOom s0))
    (hret : ∀ {A : RustCliAllocBudget M} {s0 s : State} {stk code : Nat}
      {Qp : State → SepProp → Prop},
      mainFrameSize ≤ stk → AtRetPlaced CodeOk s0 s code →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s (retMem A s0 stk)
        (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code ∧ sf.trace = s.trace ∧
          sf.fs = s.fs ∧ (Pf ⊢ stackAt s0.sp stk ∗ A.repAlloc.pool ∗ anyHeap))
        Qp (mainOom s0))
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtEntryPlaced CodeOk i s0) (hok : CliInputsOk i)
    (hfail : parseArgs uuidParse (i.argv.map bytesOfString) = none)
    (hfit : FitsEnv M lim st (ParseFailEnvOf (M2PreDeallocEnv uuidParse) i)) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0 (mainFrame A lim st stk Statics i s0)
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 2 ∧ sf.trace = s0.trace ∧
        sf.fs = s0.fs ∧ (Pf ⊢ stackAt s0.sp stk ∗ A.repAlloc.pool ∗ anyHeap))
      Qp (mainOom s0) := by
  let Q : State → SepProp → Prop :=
    fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
      (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 2 ∧ sf.trace = s0.trace ∧
      sf.fs = s0.fs ∧ (Pf ⊢ stackAt s0.sp stk ∗ A.repAlloc.pool ∗ anyHeap)
  have hstk_ret : mainFrameSize ≤ stk :=
    Nat.le_trans (Nat.le_add_right mainFrameSize _) hstk
  have hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s => code = 2 ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp :=
    fun s code hs ⟨hcode, htr, hfs⟩ =>
      sepWPp_mono_post_placed
        (fun _ _ ⟨hsp, hcs, hx0, htr_f, hfs_f, hmem⟩ =>
          ⟨hsp, hcs, hx0.trans (congrArg (BitVec.ofNat 32) hcode),
            htr_f.trans htr, hfs_f.trans hfs, hmem⟩)
        (hret hstk_ret hs)
  have hfit_m1 : i.argv ≠ [] → FitsEvents M lim st (rustAllocEvents (16 * i.argv.length) 8) :=
    fun hne => by
      have hseq : FitsEnv M lim st
          (SeqEnv (· = rustAllocEvents (16 * i.argv.length) 8)
            (M2PreDeallocEnv uuidParse (i.argv.map bytesOfString))) :=
        fun evs hevs => hfit evs (by simp only [ParseFailEnvOf, hne, ↓reduceIte]; exact hevs)
      exact hseq.seq_left _ rfl
  exact hm1 hc hstk hstk64 hs0 hok hfit_m1
    (fun s code hs ⟨hcode, _, htr, hfs⟩ => hexit s code hs ⟨hcode, htr, hfs⟩)
    (fun s buf ps p0 hne hps hs1 => by
      have hseq : FitsEnv M lim st
          (SeqEnv (· = rustAllocEvents (16 * i.argv.length) 8)
            (M2PreDeallocEnv uuidParse (i.argv.map bytesOfString))) :=
        fun evs hevs => hfit evs (by simp only [ParseFailEnvOf, hne, ↓reduceIte]; exact hevs)
      exact hm2 (p0 := p0) hc hstk hstk64 hok hne hps (hseq.seq_right rfl) hs1
        (fun s' code hs' ⟨hcode, _, htr, hfs⟩ => hexit s' code hs' ⟨hcode, htr, hfs⟩)
        (fun _ _ _ _ hparse _ => (nomatch hfail.symm.trans hparse)))

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.ParseFailPlacedBudget
