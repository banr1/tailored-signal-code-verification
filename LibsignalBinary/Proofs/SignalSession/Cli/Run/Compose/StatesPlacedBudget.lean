/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Placed Machine-Level Hop States for `signal_session::run`

Extends `StatesPlaced` to `RustCliAllocBudget M` on Block `579` (`lsProg_579`), providing
`runNeed_bounds_placed` for `SemPlacedBudget.slotsOfPlaced`, state-indexed spatial footprints
(`A.atState lim st s`), and envelope-constrained (`runPostPlaced`) / envelope-erased
(`runPostAnyPlaced`) normal-return bridge lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack finishGrowStackX lsLogOff smallRootStack)
open CryptoVerification.SignalSession.Cli (RunAnswer StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV CallW RunCall addrWords callAt callHeap cliWrOk inputOf ownedBytes runResAt storesAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton
  (RunBudgets pathNeed runFrame runNeed
   splitIdNeed splitSignedNeed)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRunEntryPlaced Bytes Init1Data Init2Data MeAtDispatch RunHistOk RunNeeds RunSem
   runFiles runFsp runPanicProp runPcPlaced_zero runRel)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (runSpecAnyPlaced runSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)

/-! ## 1. Callee Stack-Budget Bounds from `runNeed` (`SemPlacedBudget.slotsOfPlaced`) -/

theorem runNeed_bounds_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {envs : RunSlotEnvs}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hres : runNeed B (slotsOfPlaced A lim envs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63) :
    let sub := resStack - runFrame
    runFrame ≤ resStack ∧
      sub ≤ 2 ^ 63 ∧
      sub ≤ 2 ^ 64 ∧
      0xB0 + extHookStack ≤ sub ∧
      finishGrowStackX ≤ sub ∧
      B.readFile ≤ sub ∧
      pathNeed ≤ sub ∧
      B.dirGetNeed ≤ sub ∧
      B.bundleReadNeed ≤ sub ∧
      splitIdNeed ≤ sub ∧
      splitSignedNeed ≤ sub ∧
      0x60 ≤ sub ∧
      smallRootStack ≤ sub ∧
      CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack ≤ sub ∧
      32 + extHookStack ≤ sub ∧
      96 + extHookStack ≤ sub ∧
      extHookStack ≤ sub ∧
      needs.encrypt ≤ sub ∧
      needs.decryptSignal ≤ sub ∧
      needs.initiate ≤ sub ∧
      needs.decryptPrekey ≤ sub ∧
      48 + extHookStack ≤ sub := by
  have hres' :
      runNeed B (CryptoVerification.SignalSession.Cli.RunCompose.slotsOfPlaced A.repAlloc S needs) ≤
        resStack := hres
  exact CryptoVerification.SignalSession.Cli.RunCompose.runNeed_bounds_placed hres' hres64

/-! ## 2. Budget-Threaded Spatial Footprints at Named Boundary States -/

/-- Entry spatial footprint of `run` under `[LibsignalPlacement]` at cost state `st`. -/
abbrev runEntryMemPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (g : RunCall) (s0 : State) (resStack : Nat) : SepProp :=
  CryptoVerification.SignalSession.Cli.RunCompose.runEntryMemPlaced
    (A.atState lim st s0) g s0 resStack

/-- Spatial footprint at `AtDispatchPlaced` (`R + 0x214`) at cost state `st` and machine state `s`. -/
abbrev dispatchMemPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (g : RunCall) (me : MeAtDispatch) (s0 s : State) (resStack : Nat) : SepProp :=
  CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced
    (A.atState lim st s) g me s0 resStack

/-- Spatial footprint at `AtInit1Placed` (`R + 0x74c`) at cost state `st` and machine state `s`. -/
abbrev init1MemPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (g : RunCall) (d : Init1Data) (s0 s : State) (resStack : Nat) : SepProp :=
  CryptoVerification.SignalSession.Cli.RunCompose.init1MemPlaced
    (A.atState lim st s) g d s0 resStack

/-- Spatial footprint at `AtInit2Placed` (`R + 0x28f0`) at cost state `st` and machine state `s`. -/
abbrev init2MemPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (g : RunCall) (d : Init2Data) (s0 s : State) (resStack : Nat) : SepProp :=
  CryptoVerification.SignalSession.Cli.RunCompose.init2MemPlaced
    (A.atState lim st s) g d s0 resStack

/-! ## 3. Normal-Return Postconditions (`runPostPlaced` & `runPostAnyPlaced`) -/

/-- Envelope-constrained normal-return postcondition at `s0.readReg64 .lr`, matching
`SpecsPlacedBudget.runSpecPlaced`. -/
def runPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (RunEnv : RunCall → List AllocEvent → Prop)
    (g : RunCall) (st : M.σ) (resStack : Nat) (s0 sf : State) (Pf : SepProp) : Prop :=
  CodeOk sf.mem ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    s0.trace <+: sf.trace ∧ RunHistOk g.i s0 sf ∧
    ∃ (evs : List AllocEvent) (a' : RunAnswer),
      RunEnv g evs ∧ a' ≠ none ∧ a' = g.a ∧
      (Pf ⊢ memRegion g.call 56 ∗ memRegion g.stores 320 ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp resStack ∗
        runResAt A.repAlloc cliWrOk g.res a' ∗ anyHeap)

/-- Envelope-erased normal-return postcondition at `s0.readReg64 .lr`, matching
`SpecsPlacedBudget.runSpecAnyPlaced`. -/
def runPostAnyPlaced [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (g : RunCall) (resStack : Nat) (s0 sf : State) (Pf : SepProp) : Prop :=
  CodeOk sf.mem ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    s0.trace <+: sf.trace ∧ RunHistOk g.i s0 sf ∧
    ∃ (st' : M.σ) (a' : RunAnswer),
      a' ≠ none ∧ a' = g.a ∧
      (Pf ⊢ memRegion g.call 56 ∗ memRegion g.stores 320 ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ A.pool lim st' sf ∗
        stackAt s0.sp resStack ∗
        runResAt A.repAlloc cliWrOk g.res a' ∗ anyHeap)

/-! ## 4. Entry / Exit `runSpecPlaced` & `runSpecAnyPlaced` Bridge Lemmas -/

theorem ownedBytes_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (cap ptr len : BitVec 64) (bs : List (BitVec 8)) :
    ownedBytes A₁ cap ptr len bs = ownedBytes A₂ cap ptr len bs := by
  simp only [ownedBytes, h]

theorem addrWords_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (a : AddrV) (cap ptr len dev : BitVec 64) :
    addrWords A₁ a cap ptr len dev = addrWords A₂ a cap ptr len dev := by
  simp only [addrWords, ownedBytes_congr_live h]

theorem callHeap_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (w : CallW) (c : CallV) :
    callHeap A₁ w c = callHeap A₂ w c := by
  cases c <;> simp only [callHeap, addrWords_congr_live h, ownedBytes_congr_live h]

theorem callAt_congr_live {A₁ A₂ : RustAlloc} (h : A₁.live = A₂.live)
    (a : BitVec 64) (c : CallV) :
    callAt A₁ a c = callAt A₂ a c := by
  unfold callAt
  congr 1; funext w
  rw [callHeap_congr_live h]

theorem callAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (a : BitVec 64) (c : CallV) :
    callAt (A.atState lim st s) a c = callAt A.repAlloc a c :=
  callAt_congr_live rfl a c

theorem storesAt_opened_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (a : BitVec 64) :
    storesAt (A.atState lim st s) a StoresGhost.opened =
      storesAt A.repAlloc a StoresGhost.opened := rfl

private theorem fromRecord_lsLogOff_eq [LibsignalPlacement] :
    CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff = lsLogOff := rfl

theorem runEntry_of_placed_pre [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall} {st : M.σ} {resStack : Nat} {R : SepProp} {s0 : State}
    (hpc : s0.pc = lsmpl.base 579)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨
      (runSpecPlaced CodeOk A lim RunEnv uuidTryParse (runRel S) cliWrOk resStack).pre (g, st) s0 ∗
        R)
    (hsp : s0.spAligned = true) :
    AtRunEntryPlaced CodeOk S g s0 ∧ FitsEnv M lim st (RunEnv g) ∧
      (s0.mem ⊨ runEntryMemPlaced A lim st g s0 resStack ∗ R) := by
  simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with
    ⟨⟨hinv, hrel, hparse, hx0, hx1, hx2, hx3, hx4, hfs, hout, _hspb, hfits, _hlr⟩, hmem⟩
  refine ⟨⟨?_, hrun, hinv, hsp, hrel, hparse, hx0, hx1, hx2, hx3, hx4, hfs, hout⟩, hfits, ?_⟩
  · rw [runPcPlaced_zero, hpc]
  · simpa only [runEntryMemPlaced, CryptoVerification.SignalSession.Cli.RunCompose.runEntryMemPlaced,
      callAt_atState, storesAt_opened_atState, fromRecord_lsLogOff_eq,
      RustCliAllocBudget.atState_pool, sepConj_assoc] using hmem

theorem placed_post_of_runPost [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall} {st : M.σ} {resStack : Nat} {R Pf : SepProp} {s0 sf : State}
    (hfs0 : s0.fs.files = runFiles g.i)
    (hout0 : ProcessOutcome.traceStreamBytes .stdout s0.trace = [])
    (hp : runPostPlaced CodeOk A lim RunEnv g st resStack s0 sf Pf)
    (hmf : sf.mem ⊨ Pf ∗ R) :
    (sf.mem ⊨
      (runSpecPlaced CodeOk A lim RunEnv uuidTryParse (runRel S) cliWrOk resStack).post
        (g, st) s0 sf ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
  rcases hp with ⟨_, hsp, hcs, htr, ⟨hf, ho⟩, evs, a', hevs, ha_ne, ha_eq, hent⟩
  refine ⟨?_, hsp, hcs⟩
  have hex :
      runResAt A.repAlloc cliWrOk g.res a' ⊢
        ∃∗ a'', ⌜a'' ≠ none ∧ a'' = g.a⌝ ∗
          runResAt A.repAlloc cliWrOk g.res a'' :=
    Entails.sepExists_right a' (Entails.pure_right ⟨ha_ne, ha_eq⟩ (Entails.refl _))
  have hent' :
      Pf ⊢ memRegion g.call 56 ∗ memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp resStack ∗
        (∃∗ a'', ⌜a'' ≠ none ∧ a'' = g.a⌝ ∗
          runResAt A.repAlloc cliWrOk g.res a'') ∗
        anyHeap :=
    Entails.trans hent
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hex))))))
  have hmem1 := Satisfies.mono (sepConj_mono_left hent') hmf
  dsimp only [runSpecPlaced]
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hevs, htr, hf.trans hfs0.symm, ho.trans hout0.symm⟩,
    by simpa only [sepConj_assoc] using hmem1⟩

theorem placed_onPanic_of_runPanic [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall} {st : M.σ} {resStack : Nat} {R Pf : SepProp} {s0 sf : State}
    (hpan : runPanicProp g s0 sf) (hmf : sf.mem ⊨ Pf ∗ R) :
    sf.mem ⊨
      (runSpecPlaced CodeOk A lim RunEnv uuidTryParse (runRel S) cliWrOk resStack).onPanic
        (g, st) s0 sf ∗ R := by
  simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpan, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmf⟩

theorem placed_onOom_eq [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RunEnv : RunCall → List AllocEvent → Prop}
    (g : RunCall) (st : M.σ) (resStack : Nat) (s0 sf : State) :
    (runSpecPlaced CodeOk A lim RunEnv uuidTryParse (runRel S) cliWrOk resStack).onOom
        (g, st) s0 sf =
      ⌜False⌝ := rfl

theorem runEntry_of_any_placed_pre [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {g : RunCall} {st : M.σ} {resStack : Nat} {R : SepProp} {s0 : State}
    (hpc : s0.pc = lsmpl.base 579)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨
      (runSpecAnyPlaced CodeOk A lim uuidTryParse (runRel S) cliWrOk resStack).pre (g, st) s0 ∗ R)
    (hsp : s0.spAligned = true) :
    AtRunEntryPlaced CodeOk S g s0 ∧
      (s0.mem ⊨ runEntryMemPlaced A lim st g s0 resStack ∗ R) := by
  simp only [runSpecAnyPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hinv, hrel, hparse, hx0, hx1, hx2, hx3, hx4, hfs, hout, _hspb, _hlr⟩, hmem⟩
  refine ⟨⟨?_, hrun, hinv, hsp, hrel, hparse, hx0, hx1, hx2, hx3, hx4, hfs, hout⟩, ?_⟩
  · rw [runPcPlaced_zero, hpc]
  · simpa only [runEntryMemPlaced, CryptoVerification.SignalSession.Cli.RunCompose.runEntryMemPlaced,
      callAt_atState, storesAt_opened_atState, fromRecord_lsLogOff_eq,
      RustCliAllocBudget.atState_pool, sepConj_assoc] using hmem

theorem any_placed_post_of_runPost [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {g : RunCall} {st : M.σ} {resStack : Nat} {R Pf : SepProp} {s0 sf : State}
    (hfs0 : s0.fs.files = runFiles g.i)
    (hout0 : ProcessOutcome.traceStreamBytes .stdout s0.trace = [])
    (hp : runPostAnyPlaced CodeOk A lim g resStack s0 sf Pf)
    (hmf : sf.mem ⊨ Pf ∗ R) :
    (sf.mem ⊨
      (runSpecAnyPlaced CodeOk A lim uuidTryParse (runRel S) cliWrOk resStack).post
        (g, st) s0 sf ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
  rcases hp with ⟨_, hsp, hcs, htr, ⟨hf, ho⟩, st', a', ha_ne, ha_eq, hent⟩
  refine ⟨?_, hsp, hcs⟩
  have hex :
      runResAt A.repAlloc cliWrOk g.res a' ⊢
        ∃∗ a'', ⌜a'' ≠ none ∧ a'' = g.a⌝ ∗
          runResAt A.repAlloc cliWrOk g.res a'' :=
    Entails.sepExists_right a' (Entails.pure_right ⟨ha_ne, ha_eq⟩ (Entails.refl _))
  have hent' :
      Pf ⊢ memRegion g.call 56 ∗ memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        A.pool lim st' sf ∗ stackAt s0.sp resStack ∗
        (∃∗ a'', ⌜a'' ≠ none ∧ a'' = g.a⌝ ∗
          runResAt A.repAlloc cliWrOk g.res a'') ∗
        anyHeap :=
    Entails.trans hent
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hex))))))
  have hmem1 := Satisfies.mono (sepConj_mono_left hent') hmf
  dsimp only [runSpecAnyPlaced]
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨st', ?_⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htr, hf.trans hfs0.symm, ho.trans hout0.symm⟩,
    by simpa only [sepConj_assoc] using hmem1⟩

theorem any_placed_onPanic_of_runPanic [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {g : RunCall} {st : M.σ} {resStack : Nat} {R Pf : SepProp} {s0 sf : State}
    (hpan : runPanicProp g s0 sf) (hmf : sf.mem ⊨ Pf ∗ R) :
    sf.mem ⊨
      (runSpecAnyPlaced CodeOk A lim uuidTryParse (runRel S) cliWrOk resStack).onPanic
        (g, st) s0 sf ∗ R := by
  simp only [runSpecAnyPlaced, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpan, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmf⟩

theorem any_placed_onOom_eq [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (g : RunCall) (st : M.σ) (resStack : Nat) (s0 sf : State) :
    (runSpecAnyPlaced CodeOk A lim uuidTryParse (runRel S) cliWrOk resStack).onOom
        (g, st) s0 sf =
      ⌜False⌝ := rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
