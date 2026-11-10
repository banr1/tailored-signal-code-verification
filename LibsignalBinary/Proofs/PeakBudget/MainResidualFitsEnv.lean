/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1Frame

/-!
# Residual `FitsEnv` Cost-Model States Across `main` Hops `M1`..`M6`

Factors whole-`main` `FitsEnv fineCostModel lim fineCostModel.init` (`RealCliMainBinaryEnvOf E i`
on `CliPqxdhInputs WP i` paired with `SeqEnv (CliMainBoundedSetupEnv i.argv.length) FreeOnlyEvs` on
all `CliInputsOk i`) into residual cost-model state invariants `mainSt0`..`mainSt5` aligned with
`Block 617` hop boundaries (`M1 → M2 → M3 → M4 → M5 → M6`), with per-hop `FitsEnv` / `FitsEvents`
and `stepEvents` transition lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.MainResidualFitsEnv

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (CliPqxdhInputs Inputs pqInitInputs pqInputs pqRecvInputs pqSendInputs stdinCapBytes)
open CryptoVerification.SignalSession.Cli (CliInputsOk StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops
  (CallV RunCall argvFits_length_le cliIo inputOf parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs SeqEnv fitsEvents_append
   rustAllocEvents)
open LibsignalBinary.Heap.Fine (FineBudget fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDefaultStaticBytes cliDefaultStaticCount cliMaxAddrTextBytes
   cliMaxDirPathBytes cliMaxDirtyEntries cliOneGiB)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (M1PhaseEnv M2CollectEnv M2CollectStepEnv M5PhaseEnv M6Env)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs (mkExistentialRealCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv RealCliMainBinaryEnvOf realCliMainBinaryEnvOf_90pct_fitsEnv_concrete
   realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_concrete realCliMainBinaryEnvOf_fitsEnv_concrete)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal (cliRealNinetyPctOneGiB)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
  (AddrOptBoundedEnv BundleOptBoundedEnv CliMainBoundedSetupEnv M2CollectFullEnv
   M3BoundedSetupEnv ValidPostSetupWitness addrOptBoundedEnv_nil
   bundleOptBoundedEnv_nil cliMainSetupEarlyExit_90pct_fitsEnv_le1820
   cliMainSetupEarlyExit_fitsEnv_cliBudgetLimits_le1820)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (IterSeqEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)

/-! ## 1. Sequential Envelope Algebra and Residual Sub-Envelopes -/

private theorem seqEnv_mono_local {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) :
    SeqEnv E₁' E₂' evs := by
  rcases h with hE1 | ⟨evs₁, evs₂, rfl, hE1, hE2⟩
  · exact Or.inl (h1 evs hE1)
  · exact Or.inr ⟨evs₁, evs₂, rfl, h1 evs₁ hE1, h2 evs₂ hE2⟩

private theorem seqEnv_assoc_left_local {E₁ E₂ E₃ : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv E₁ (SeqEnv E₂ E₃) evs) :
    SeqEnv (SeqEnv E₁ E₂) E₃ evs := by
  rcases h with h1 | ⟨evs₁, evs₂₃, rfl, h1, h23⟩
  · exact Or.inl (Or.inl h1)
  · rcases h23 with h2 | ⟨evs₂, evs₃, rfl, h2, h3⟩
    · exact Or.inl (Or.inr ⟨evs₁, evs₂₃, rfl, h1, h2⟩)
    · exact Or.inr ⟨evs₁ ++ evs₂, evs₃, (List.append_assoc evs₁ evs₂ evs₃).symm,
        Or.inr ⟨evs₁, evs₂, rfl, h1, h2⟩, h3⟩

private theorem seqEnv_assoc_right_of_nil {E₁ E₂ E₃ : List AllocEvent → Prop}
    (hnil : E₂ []) {evs : List AllocEvent}
    (h : SeqEnv (SeqEnv E₁ E₂) E₃ evs) :
    SeqEnv E₁ (SeqEnv E₂ E₃) evs := by
  rcases h with (h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩) | ⟨evs₁₂, evs₃, rfl, h12, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨evs₁, evs₂, rfl, h1, Or.inl h2⟩
  · rcases h12 with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
    · exact Or.inr ⟨evs₁₂, evs₃, rfl, h1, Or.inr ⟨[], evs₃, rfl, hnil, h3⟩⟩
    · exact Or.inr ⟨evs₁, evs₂ ++ evs₃, List.append_assoc evs₁ evs₂ evs₃, h1,
        Or.inr ⟨evs₂, evs₃, rfl, h2, h3⟩⟩

theorem fitsEnv_left_of_seqEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E₁ E₂ : List AllocEvent → Prop}
    (h : FitsEnv M lim st (SeqEnv E₁ E₂)) :
    FitsEnv M lim st E₁ :=
  fun evs he1 => h evs (Or.inl he1)

theorem fitsEvents_and_fitsEnv_stepEvents_of_seqEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {E₁ E₂ : List AllocEvent → Prop}
    (h : FitsEnv M lim st (SeqEnv E₁ E₂)) {evs₁ : List AllocEvent} (he1 : E₁ evs₁) :
    FitsEvents M lim st evs₁ ∧ FitsEnv M lim (M.stepEvents evs₁ st) E₂ :=
  ⟨h evs₁ (Or.inl he1), fun evs₂ he2 =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp
      (h (evs₁ ++ evs₂) (Or.inr ⟨evs₁, evs₂, rfl, he1, he2⟩))).2⟩

private theorem freeOnlyEvs_nil : FreeOnlyEvs [] :=
  fun _ h => nomatch h

private theorem iterSeqEnv_m2CollectStep_nil :
    ∀ xs : List Nat, IterSeqEnv M2CollectStepEnv xs []
  | [] => rfl
  | _ :: _ => Or.inl (Or.inl rfl)

theorem m2CollectEnv_nil (argvLen : Nat) : M2CollectEnv argvLen [] :=
  iterSeqEnv_m2CollectStep_nil (List.range argvLen)

theorem m2CollectFullEnv_nil (argvLen : Nat) : M2CollectFullEnv argvLen [] :=
  Or.inl (m2CollectEnv_nil argvLen)

theorem m3BoundedSetupEnv_nil : M3BoundedSetupEnv [] :=
  Or.inl (Or.inl rfl)

/-- Post-`M1` setup sub-envelope (`M2` collect + `Address`/`Bundle` + `M3`). -/
def PostM1SetupEnv (argvLen : Nat) (evs : List AllocEvent) : Prop :=
  SeqEnv (M2CollectFullEnv argvLen)
    (SeqEnv AddrOptBoundedEnv
      (SeqEnv BundleOptBoundedEnv
        (SeqEnv FreeOnlyEvs M3BoundedSetupEnv))) evs

/-- Phase-`M2` envelope (`M2CollectFullEnv` + `AddrOptBoundedEnv` + `BundleOptBoundedEnv` +
`FreeOnlyEvs`), closed under prefix early exits. -/
def M2PhaseEnv (argvLen : Nat) (evs : List AllocEvent) : Prop :=
  SeqEnv (M2CollectFullEnv argvLen)
    (SeqEnv AddrOptBoundedEnv
      (SeqEnv BundleOptBoundedEnv FreeOnlyEvs)) evs

/-- Post-setup (`M4`–`M6` or early-exit `FreeOnlyEvs`) tail of `RealCliMainBinaryEnvOf E i`. -/
def PostSetupTailEnv (E : RunCall → CliRunCalleeEnvs) (i : Inputs)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
    SeqEnv (CliRunBinaryEnv cliIo.rd (E w.g) sessionCapBytes w.g)
      (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs

theorem realCliMainBinaryEnvOf_eq_seqEnv (E : RunCall → CliRunCalleeEnvs) (i : Inputs) :
    RealCliMainBinaryEnvOf E i = SeqEnv (CliMainBoundedSetupEnv i.argv.length) (PostSetupTailEnv E i) :=
  rfl

theorem postM1SetupEnv_nil (argvLen : Nat) : PostM1SetupEnv argvLen [] :=
  Or.inl (m2CollectFullEnv_nil argvLen)

theorem m2PhaseEnv_nil (argvLen : Nat) : M2PhaseEnv argvLen [] :=
  Or.inl (m2CollectFullEnv_nil argvLen)

theorem postM1SetupEnv_of_seq_m2Phase_m3 {argvLen : Nat} {evs : List AllocEvent}
    (h : SeqEnv (M2PhaseEnv argvLen) M3BoundedSetupEnv evs) :
    PostM1SetupEnv argvLen evs := by
  have h1 : SeqEnv (M2CollectFullEnv argvLen)
      (SeqEnv (SeqEnv AddrOptBoundedEnv (SeqEnv BundleOptBoundedEnv FreeOnlyEvs))
        M3BoundedSetupEnv) evs :=
    seqEnv_assoc_right_of_nil (Or.inl addrOptBoundedEnv_nil) h
  refine seqEnv_mono_local (fun _ hx => hx) (fun _ hy => ?_) h1
  have h2 : SeqEnv AddrOptBoundedEnv
      (SeqEnv (SeqEnv BundleOptBoundedEnv FreeOnlyEvs) M3BoundedSetupEnv) _ :=
    seqEnv_assoc_right_of_nil (Or.inl bundleOptBoundedEnv_nil) hy
  exact seqEnv_mono_local (fun _ hx => hx)
    (fun _ hz => seqEnv_assoc_right_of_nil freeOnlyEvs_nil hz) h2

theorem postM1SetupEnv_of_m2Phase {argvLen : Nat} {evs : List AllocEvent}
    (h : M2PhaseEnv argvLen evs) :
    PostM1SetupEnv argvLen evs :=
  postM1SetupEnv_of_seq_m2Phase_m3 (Or.inl h)

/-! ## 2. Residual Cost-Model State Predicates `mainSt0`..`mainSt5` -/

/-- Entry cost-model invariant at `M0`/`M1` (`Block 617` entry): unconditional setup + early-exit
`FitsEnv` paired with domain-guarded whole-`main` `RealCliMainBinaryEnvOf E i` `FitsEnv`. -/
def mainSt0 (WP : PEParams) (E : RunCall → CliRunCalleeEnvs) (lim : BudgetLimits)
    (i : Inputs) (st0 : FineBudget) : Prop :=
  FitsEnv fineCostModel lim st0 (SeqEnv (CliMainBoundedSetupEnv i.argv.length) FreeOnlyEvs) ∧
  (CliPqxdhInputs WP i → FitsEnv fineCostModel lim st0 (RealCliMainBinaryEnvOf E i))

/-- Post-`M1` (`argv` buffer allocated) residual cost-model invariant. -/
def mainSt1 (WP : PEParams) (E : RunCall → CliRunCalleeEnvs) (lim : BudgetLimits)
    (i : Inputs) (st1 : FineBudget) : Prop :=
  FitsEnv fineCostModel lim st1 (SeqEnv (PostM1SetupEnv i.argv.length) FreeOnlyEvs) ∧
  (CliPqxdhInputs WP i →
    FitsEnv fineCostModel lim st1 (SeqEnv (PostM1SetupEnv i.argv.length) (PostSetupTailEnv E i)))

/-- Post-`M2` (`parseArgs = some c`) residual cost-model invariant entering `M3`. -/
def mainSt2 (WP : PEParams) (E : RunCall → CliRunCalleeEnvs) (lim : BudgetLimits)
    (i : Inputs) (c : CallV) (st2 : FineBudget) : Prop :=
  parseArgs uuidTryParse (i.argv.map bytesOfString) = some c ∧
  FitsEnv fineCostModel lim st2 (SeqEnv M3BoundedSetupEnv FreeOnlyEvs) ∧
  (CliPqxdhInputs WP i →
    FitsEnv fineCostModel lim st2 (SeqEnv M3BoundedSetupEnv (PostSetupTailEnv E i)))

/-- Post-`M3` (`read_stdin` + `"coins"` `read_file` completed) residual cost-model invariant
entering `M4` (`step4_overCap` or `step4_call`). -/
def mainSt3 (WP : PEParams) (E : RunCall → CliRunCalleeEnvs) (lim : BudgetLimits)
    (i : Inputs) (c : CallV) (st3 : FineBudget) : Prop :=
  parseArgs uuidTryParse (i.argv.map bytesOfString) = some c ∧
  FitsEnv fineCostModel lim st3 FreeOnlyEvs ∧
  (CliPqxdhInputs WP i → FitsEnv fineCostModel lim st3 (PostSetupTailEnv E i))

/-- Post-`M4` (`signal_session::run` returned `Ok`) residual cost-model invariant entering `M5`. -/
def mainSt4 (lim : BudgetLimits) (i : Inputs) (c : CallV) (_g : StoresGhost)
    (st4 : FineBudget) : Prop :=
  parseArgs uuidTryParse (i.argv.map bytesOfString) = some c ∧
  i.stdin.length ≤ msgCapBytes ∧
  FitsEnv fineCostModel lim st4 FreeOnlyEvs ∧
  (∀ (dirs : List (List (BitVec 8) × List (List (BitVec 8)))) (ok : Bool),
    (dirs.map (fun dn => dn.2.length)).sum ≤ cliMaxDirtyEntries →
    (∀ dn ∈ dirs,
      dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) →
    FitsEnv fineCostModel lim st4 (SeqEnv (M5PhaseEnv dirs) (M6Env ok)))

/-- Post-`M5` (`commitFiles` / store drops completed) residual cost-model invariant entering `M6`. -/
def mainSt5 (lim : BudgetLimits) (_i : Inputs) (_c : CallV) (_g : StoresGhost) (ok : Bool)
    (st5 : FineBudget) : Prop :=
  FitsEnv fineCostModel lim st5 FreeOnlyEvs ∧
  FitsEnv fineCostModel lim st5 (M6Env ok)

/-! ## 3. `mainSt0` Initializers and `M1` Transition -/

/-- Generic `hSt0` constructor from setup early-exit `FitsEnv` and `RealCliMainBinaryEnvOf` `FitsEnv`. -/
theorem mainSt0_init_of_fitsEnv {WP : PEParams} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits}
    (hEarly : ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel lim fineCostModel.init
        (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs))
    (hMain : ∀ i : Inputs, CliPqxdhInputs WP i →
      FitsEnv fineCostModel lim fineCostModel.init (RealCliMainBinaryEnvOf E i))
    {i : Inputs} (hok : CliInputsOk i) :
    mainSt0 WP E lim i fineCostModel.init :=
  ⟨hEarly i.argv.length (argvFits_length_le hok.2), hMain i⟩

/-- Concrete `< 90%` (`cliRealNinetyPctOneGiB ≤ lim.physCap`) `hSt0` at
`mkExistentialRealCalleeEnvs img S WP`. -/
theorem mainSt0_init_90pct_concrete [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap)
    (img : Image) (S : RunSem) (WP : PEParams)
    (i : Inputs) (hok : CliInputsOk i) :
    mainSt0 WP (mkExistentialRealCalleeEnvs img S WP) lim i fineCostModel.init :=
  mainSt0_init_of_fitsEnv
    (fun _ hargv => cliMainSetupEarlyExit_90pct_fitsEnv_le1820 henf hsb hsc hcap90 hargv)
    (realCliMainBinaryEnvOf_90pct_fitsEnv_concrete henf hsb hsc hcap90 img S WP)
    hok

/-- Concrete `≤ 1 GiB` (`cliOneGiB ≤ lim.physCap`) `hSt0` at `mkExistentialRealCalleeEnvs img S WP`. -/
theorem mainSt0_init_concrete [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap1G : cliOneGiB ≤ lim.physCap)
    (img : Image) (S : RunSem) (WP : PEParams)
    (i : Inputs) (hok : CliInputsOk i) :
    mainSt0 WP (mkExistentialRealCalleeEnvs img S WP) lim i fineCostModel.init :=
  mainSt0_init_of_fitsEnv
    (fun _ hargv =>
      cliMainSetupEarlyExit_90pct_fitsEnv_le1820 henf hsb hsc
        (Nat.le_trans (by unfold cliRealNinetyPctOneGiB cliOneGiB; decide) hcap1G) hargv)
    (realCliMainBinaryEnvOf_fitsEnv_concrete henf hsb hsc hcap1G img S WP)
    hok

/-- `cliBudgetLimits` (`1 GiB`) `mainSt0` initializer at `mkExistentialRealCalleeEnvs img S WP`. -/
theorem mainSt0_init_cliBudgetLimits_concrete [LibsignalPlacement]
    (img : Image) (S : RunSem) (WP : PEParams)
    (i : Inputs) (hok : CliInputsOk i) :
    mainSt0 WP (mkExistentialRealCalleeEnvs img S WP) cliBudgetLimits i fineCostModel.init :=
  mainSt0_init_of_fitsEnv
    cliMainSetupEarlyExit_fitsEnv_cliBudgetLimits_le1820
    (realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_concrete img S WP)
    hok

/-- `M1` transition (`st0 → st1`): any `M1PhaseEnv i.argv.length` event trace fits `lim` from
`st0` and advances `mainSt0` to `mainSt1`. -/
theorem fitsEvents_and_st1_of_st0 {WP : PEParams} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {st0 : FineBudget}
    (hst0 : mainSt0 WP E lim i st0)
    {evs₁ : List AllocEvent} (hm1 : M1PhaseEnv i.argv.length evs₁) :
    FitsEvents fineCostModel lim st0 evs₁ ∧
      mainSt1 WP E lim i (fineCostModel.stepEvents evs₁ st0) := by
  have hEarlySeq : FitsEnv fineCostModel lim st0
      (SeqEnv (M1PhaseEnv i.argv.length)
        (SeqEnv (PostM1SetupEnv i.argv.length) FreeOnlyEvs)) :=
    fun evs h => hst0.1 evs
      (seqEnv_mono_local (fun _ => Or.inr) (fun _ hf => hf) (seqEnv_assoc_left_local h))
  obtain ⟨hfits₁, hEarly₁⟩ := fitsEvents_and_fitsEnv_stepEvents_of_seqEnv hEarlySeq hm1
  refine ⟨hfits₁, hEarly₁, fun hi => ?_⟩
  have hMainSeq : FitsEnv fineCostModel lim st0
      (SeqEnv (M1PhaseEnv i.argv.length)
        (SeqEnv (PostM1SetupEnv i.argv.length) (PostSetupTailEnv E i))) :=
    fun evs h => hst0.2 hi evs
      (seqEnv_mono_local (fun _ => Or.inr) (fun _ ht => ht) (seqEnv_assoc_left_local h))
  exact (fitsEvents_and_fitsEnv_stepEvents_of_seqEnv hMainSeq hm1).2

/-- Non-empty `argv` `M1` transition (`rustAllocEvents (16 * i.argv.length) 8`) from `mainSt0` to `mainSt1`. -/
theorem mainSt01_of_st0 {WP : PEParams} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {st0 : FineBudget}
    (_hok : CliInputsOk i) (hst0 : mainSt0 WP E lim i st0) (_hne : i.argv ≠ []) :
    FitsEvents fineCostModel lim st0 (rustAllocEvents (16 * i.argv.length) 8) ∧
      mainSt1 WP E lim i
        (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st0) :=
  fitsEvents_and_st1_of_st0 hst0 (Or.inr rfl)

/-! ## 4. Per-Hop Extractors and State Transitions (`M2`..`M6`) -/

theorem fitsEnv_freeOnly_of_st0 {WP : PEParams} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {st0 : FineBudget}
    (hst0 : mainSt0 WP E lim i st0) :
    FitsEnv fineCostModel lim st0 FreeOnlyEvs :=
  fun evs hf => hst0.1 evs (Or.inl (Or.inl hf))

theorem fitsEnv_freeOnly_of_st1 {WP : PEParams} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {st1 : FineBudget}
    (hst1 : mainSt1 WP E lim i st1) :
    FitsEnv fineCostModel lim st1 FreeOnlyEvs :=
  fun evs hf => hst1.1 evs (Or.inr ⟨[], evs, rfl, postM1SetupEnv_nil i.argv.length, hf⟩)

/-- `M2` (`parseArgs = none`) early-exit `FitsEnv` from `mainSt1`. -/
theorem fitsEnv_m2EarlyExit_of_st1 {WP : PEParams} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {st1 : FineBudget}
    (hst1 : mainSt1 WP E lim i st1) :
    FitsEnv fineCostModel lim st1 (SeqEnv (M2PhaseEnv i.argv.length) FreeOnlyEvs) :=
  fun evs h => hst1.1 evs
    (seqEnv_mono_local (fun _ => postM1SetupEnv_of_m2Phase) (fun _ hf => hf) h)

/-- `M2` transition (`st1 → st2`): any `M2PhaseEnv i.argv.length` event trace fits `lim` from
`st1` and advances `mainSt1` to `mainSt2` when `parseArgs` succeeds with `some c`. -/
theorem fitsEvents_and_st2_of_st1 {WP : PEParams} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {c : CallV} {st1 : FineBudget}
    (hst1 : mainSt1 WP E lim i st1)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some c)
    {evs₂ : List AllocEvent} (hm2 : M2PhaseEnv i.argv.length evs₂) :
    FitsEvents fineCostModel lim st1 evs₂ ∧
      mainSt2 WP E lim i c (fineCostModel.stepEvents evs₂ st1) := by
  have hEarlySeq : FitsEnv fineCostModel lim st1
      (SeqEnv (M2PhaseEnv i.argv.length) (SeqEnv M3BoundedSetupEnv FreeOnlyEvs)) :=
    fun evs h => hst1.1 evs
      (seqEnv_mono_local (fun _ => postM1SetupEnv_of_seq_m2Phase_m3) (fun _ hf => hf)
        (seqEnv_assoc_left_local h))
  obtain ⟨hfits₂, hEarly₂⟩ := fitsEvents_and_fitsEnv_stepEvents_of_seqEnv hEarlySeq hm2
  refine ⟨hfits₂, hparse, hEarly₂, fun hi => ?_⟩
  have hMainSeq : FitsEnv fineCostModel lim st1
      (SeqEnv (M2PhaseEnv i.argv.length)
        (SeqEnv M3BoundedSetupEnv (PostSetupTailEnv E i))) :=
    fun evs h => hst1.2 hi evs
      (seqEnv_mono_local (fun _ => postM1SetupEnv_of_seq_m2Phase_m3) (fun _ ht => ht)
        (seqEnv_assoc_left_local h))
  exact (fitsEvents_and_fitsEnv_stepEvents_of_seqEnv hMainSeq hm2).2

theorem fitsEnv_freeOnly_of_st2 {WP : PEParams} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {c : CallV} {st2 : FineBudget}
    (hst2 : mainSt2 WP E lim i c st2) :
    FitsEnv fineCostModel lim st2 FreeOnlyEvs :=
  fun evs hf => hst2.2.1 evs (Or.inr ⟨[], evs, rfl, m3BoundedSetupEnv_nil, hf⟩)

/-- `M3` (`¬ CoinsReadable i` or `stdin > 1 MiB`) early-exit `FitsEnv` from `mainSt2`. -/
theorem fitsEnv_m3EarlyExit_of_st2 {WP : PEParams} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {c : CallV} {st2 : FineBudget}
    (hst2 : mainSt2 WP E lim i c st2) :
    FitsEnv fineCostModel lim st2 (SeqEnv M3BoundedSetupEnv FreeOnlyEvs) :=
  hst2.2.1

/-- `M3` transition (`st2 → st3`): any `M3BoundedSetupEnv` event trace fits `lim` from `st2`
and advances `mainSt2` to `mainSt3`. -/
theorem fitsEvents_and_st3_of_st2 {WP : PEParams} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {c : CallV} {st2 : FineBudget}
    (hst2 : mainSt2 WP E lim i c st2)
    {evs₃ : List AllocEvent} (hm3 : M3BoundedSetupEnv evs₃) :
    FitsEvents fineCostModel lim st2 evs₃ ∧
      mainSt3 WP E lim i c (fineCostModel.stepEvents evs₃ st2) := by
  obtain ⟨hfits₃, hFree₃⟩ := fitsEvents_and_fitsEnv_stepEvents_of_seqEnv hst2.2.1 hm3
  exact ⟨hfits₃, hst2.1, hFree₃, fun hi =>
    (fitsEvents_and_fitsEnv_stepEvents_of_seqEnv (hst2.2.2 hi) hm3).2⟩

/-- `M4` `IsSendOverCap` early-exit `FreeOnlyEvs` `FitsEnv` from `mainSt3` (`step4_overCap`). -/
theorem fitsEnv_freeOnly_of_st3 {WP : PEParams} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {c : CallV} {st3 : FineBudget}
    (hst3 : mainSt3 WP E lim i c st3) :
    FitsEnv fineCostModel lim st3 FreeOnlyEvs :=
  hst3.2.1

/-- `M4` `run` precondition and transition (`st3 → st4`): under `CliPqxdhInputs WP i` and
`i.stdin.length ≤ msgCapBytes`, `CliRunBinaryEnv` fits `lim` at `st3`, and every `evs₄` in
`CliRunBinaryEnv` advances `st3` to a state satisfying both `FreeOnlyEvs` and `mainSt4`. -/
theorem fitsEnv_run_and_st4_of_st3 {WP : PEParams} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {c : CallV} {st3 : FineBudget}
    (hst3 : mainSt3 WP E lim i c st3)
    (hi : CliPqxdhInputs WP i)
    (hstdin : i.stdin.length ≤ msgCapBytes)
    (rc : RunCall) (hrc_i : rc.i = i) (hrc_c : rc.c = c) :
    FitsEnv fineCostModel lim st3 (CliRunBinaryEnv cliIo.rd (E rc) sessionCapBytes rc) ∧
      ∀ evs₄ : List AllocEvent,
        CliRunBinaryEnv cliIo.rd (E rc) sessionCapBytes rc evs₄ →
        FitsEnv fineCostModel lim (fineCostModel.stepEvents evs₄ st3) FreeOnlyEvs ∧
          ∀ g : StoresGhost, mainSt4 lim i c g (fineCostModel.stepEvents evs₄ st3) := by
  have hTail := hst3.2.2 hi
  have hparse_rc : parseArgs uuidTryParse (rc.i.argv.map bytesOfString) = some rc.c := by
    rw [hrc_i, hrc_c]; exact hst3.1
  have hstdin_rc : rc.i.stdin.length ≤ msgCapBytes := by
    rw [hrc_i]; exact hstdin
  let w0 : ValidPostSetupWitness i :=
    { g := rc
      g_i := hrc_i
      parse_ok := hparse_rc
      stdin_le := hstdin_rc
      dirs := []
      dirs_sum_le := Nat.zero_le _
      dirs_bounds := fun _ hm => nomatch hm
      ok := false }
  have hRunFits : FitsEnv fineCostModel lim st3
      (CliRunBinaryEnv cliIo.rd (E rc) sessionCapBytes rc) :=
    fun evs hrun => hTail evs (Or.inr ⟨w0, hrc_i, Or.inl hrun⟩)
  refine ⟨hRunFits, fun evs₄ hrun₄ => ?_⟩
  have hFree₄ : FitsEnv fineCostModel lim (fineCostModel.stepEvents evs₄ st3) FreeOnlyEvs := by
    intro evs_f hf
    have hm5 : M5PhaseEnv [] evs_f := Or.inr ⟨[], evs_f, rfl, rfl, hf⟩
    exact ((fitsEvents_append fineCostModel lim evs₄ evs_f st3).mp
      (hTail (evs₄ ++ evs_f)
        (Or.inr ⟨w0, hrc_i, Or.inr ⟨evs₄, evs_f, rfl, hrun₄, Or.inl hm5⟩⟩))).2
  refine ⟨hFree₄, fun _g => ⟨hst3.1, hstdin, hFree₄, fun dirs ok hsum hbounds => ?_⟩⟩
  let w : ValidPostSetupWitness i :=
    { g := rc
      g_i := hrc_i
      parse_ok := hparse_rc
      stdin_le := hstdin_rc
      dirs := dirs
      dirs_sum_le := hsum
      dirs_bounds := hbounds
      ok := ok }
  intro evs₅₆ hm56
  exact ((fitsEvents_append fineCostModel lim evs₄ evs₅₆ st3).mp
    (hTail (evs₄ ++ evs₅₆)
      (Or.inr ⟨w, hrc_i, Or.inr ⟨evs₄, evs₅₆, rfl, hrun₄, hm56⟩⟩))).2

theorem fitsEnv_freeOnly_of_st4 {lim : BudgetLimits} {i : Inputs} {c : CallV} {g : StoresGhost}
    {st4 : FineBudget} (hst4 : mainSt4 lim i c g st4) :
    FitsEnv fineCostModel lim st4 FreeOnlyEvs :=
  hst4.2.2.1

theorem fitsEnv_m5_of_st4 {lim : BudgetLimits} {i : Inputs} {c : CallV} {g : StoresGhost}
    {st4 : FineBudget} (hst4 : mainSt4 lim i c g st4)
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))}
    (hsum : (dirs.map (fun dn => dn.2.length)).sum ≤ cliMaxDirtyEntries)
    (hbounds : ∀ dn ∈ dirs,
      dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel lim st4 (M5PhaseEnv dirs) :=
  fitsEnv_left_of_seqEnv (hst4.2.2.2 dirs false hsum hbounds)

/-- `M5` transition (`st4 → st5`): any `M5PhaseEnv dirs` event trace under bounded `dirs` fits
`lim` from `st4` and advances `mainSt4` to `mainSt5`. -/
theorem fitsEvents_and_st5_of_st4 {lim : BudgetLimits} {i : Inputs} {c : CallV} {g : StoresGhost}
    {st4 : FineBudget} (hst4 : mainSt4 lim i c g st4)
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))}
    (hsum : (dirs.map (fun dn => dn.2.length)).sum ≤ cliMaxDirtyEntries)
    (hbounds : ∀ dn ∈ dirs,
      dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    (ok : Bool) {evs₅ : List AllocEvent} (hm5 : M5PhaseEnv dirs evs₅) :
    FitsEvents fineCostModel lim st4 evs₅ ∧
      mainSt5 lim i c g ok (fineCostModel.stepEvents evs₅ st4) := by
  obtain ⟨hfits₅, hM6⟩ :=
    fitsEvents_and_fitsEnv_stepEvents_of_seqEnv (hst4.2.2.2 dirs ok hsum hbounds) hm5
  have hM6False :=
    (fitsEvents_and_fitsEnv_stepEvents_of_seqEnv (hst4.2.2.2 dirs false hsum hbounds) hm5).2
  have hFree₅ : FitsEnv fineCostModel lim (fineCostModel.stepEvents evs₅ st4) FreeOnlyEvs :=
    fun evs_f hf => hM6False evs_f (Or.inr ⟨[], evs_f, rfl, rfl, hf⟩)
  exact ⟨hfits₅, hFree₅, hM6⟩

theorem fitsEnv_freeOnly_of_st5 {lim : BudgetLimits} {i : Inputs} {c : CallV} {g : StoresGhost}
    {ok : Bool} {st5 : FineBudget} (hst5 : mainSt5 lim i c g ok st5) :
    FitsEnv fineCostModel lim st5 FreeOnlyEvs :=
  hst5.1

/-- `M6` (`LineWriter` / `write_stdout` + final buffer deallocations) `FitsEnv` from `mainSt5`
(`step6`). -/
theorem fitsEnv_m6_of_st5 {lim : BudgetLimits} {i : Inputs} {c : CallV} {g : StoresGhost}
    {ok : Bool} {st5 : FineBudget} (hst5 : mainSt5 lim i c g ok st5) :
    FitsEnv fineCostModel lim st5 (M6Env ok) :=
  hst5.2

end LibsignalBinary.Proofs.PeakBudget.MainResidualFitsEnv
