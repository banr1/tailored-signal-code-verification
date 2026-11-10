/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux

/-!
# Whole-`main` `FitsTrace` / `FitsEnv` Arithmetic

Closed-form physical RAM and 48-bit virtual-address budget expressions for `fineCostModel`
(both `cumB`-coupled and `GroupCreditKit` decoupled-group formulations), sequential 6-phase
`main` composition (`M1 → M2 → M3 → (FreeOnlyEvs ∨ M4Run → M5 → M6)`), and concrete `1 GiB`
(`2 ^ 30`) RAM and `2 ^ 48` VA bounds under reachable CLI, PQXDH, and SPQR domain caps.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith

open _root_.Arm64 ProofLib
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsTrace FreeOnlyEvs SeqEnv
  rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.Fine (FineScale FineStepBound fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (
  FineStepBound_mono fineCostModel_baseFine_eq fineCostModel_largeCost_eq
  fineCostModel_largeMetaCost_eq fineCostModel_smallMaxReq_eq
  fineDynIvsOfCum fineMaxGroupsOfCum fineMaxMetaAreasOfCum fineStepReserveOfCum
)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (
  HasFineGroupCredit PhaseGroupSpec
  fineDynIvsOfGroups fineDynIvsOfGroups_mono
  fineMaxGroupsOfGroups fineMaxMetaAreasOfGroups
  fineStepReserveOfGroups fineStepReserveOfGroups_mono
  fitsEnv_fineCostModel_of_phaseCredit_groups
  fitsTrace_fineCostModel_of_phaseCredit_groups
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (
  ConcatEnv ModelHyps PhaseCreditSpec
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (
  fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit
  fitsTrace_fineCostModel_of_phaseCredit
)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (
  msgCapBytes sessionCapBytes spqrStateTightCapBytes
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
)

/-! ## Concrete CLI `BudgetLimits` and Domain Caps -/

/-- `1 GiB` (`1,073,741,824` B) physical RAM cap for the placed CLI binary. -/
def cliOneGiB : Nat := 2 ^ 30

/-- Conservative upper bound on ELF static `LOAD` + initial stack/auxv interval count (`64`). -/
def cliDefaultStaticCount : Nat := 64

/-- Conservative upper bound on ELF static `LOAD` + initial stack/auxv bytes (`16 MiB`). -/
def cliDefaultStaticBytes : Nat := 16 * 1024 * 1024

/-- Default enforced `1 GiB` `BudgetLimits` for placed CLI whole-`main` budget discharge. -/
def cliBudgetLimits : BudgetLimits where
  staticCount := cliDefaultStaticCount
  staticBytes := cliDefaultStaticBytes
  physCap := cliOneGiB
  enforced := true

/-- Constant `fineCostModel` root/base credit (`18,686,152` B). -/
def cliBaseFine : Nat := 18686152

/-- Constant `fineCostModel` small-allocation threshold (`135,167` B). -/
def cliSmallMaxReq : Nat := 135167

/-- Constant `fineCostModel` per-large-allocation `meta_area` charge (`122` B). -/
def cliLargeMetaCost : Nat := 122

/-- Tight reachable SPQR encoder point byte cap (`K = 640`, at most `40` chunks per message). -/
def spqrTightPtsCap : Nat := 640

/-- Protocol `ChainParams.maxJump` bound (`25,000`). -/
def spqrMaxJumpCap : Nat := 25000

/-- Protocol `ChainParams.maxOooKeys` bound (`2,000`). -/
def spqrMaxOooKeysCap : Nat := 2000

/-- Reachable PQXDH public pre-key bundle file cap (`1,637` B). -/
def cliBundleCapBytes : Nat := 1637

/-- Reachable CLI peer name length cap (`40` B). -/
def cliMaxPeerNameBytes : Nat := 40

/-- Reachable formatted `ProtocolAddress` / key-id filename cap (`64` B). -/
def cliMaxAddrTextBytes : Nat := 64

/-- Reachable CLI store directory path length cap (`64` B; `StoresGhost.opened` uses `≤ 26` B). -/
def cliMaxDirPathBytes : Nat := 64

/-- Reachable dirty store entry count per CLI command (`≤ 4` in `init` / `recv_prekey`). -/
def cliMaxDirtyEntries : Nat := 4

theorem cliBaseFine_eq : HasFineReallocCredit.baseFine fineCostModel = cliBaseFine :=
  fineCostModel_baseFine_eq

theorem cliSmallMaxReq_eq : HasFineReallocCredit.smallMaxReq fineCostModel = cliSmallMaxReq :=
  fineCostModel_smallMaxReq_eq

theorem cliLargeMetaCost_eq : HasFineReallocCredit.largeMetaCost fineCostModel = cliLargeMetaCost :=
  fineCostModel_largeMetaCost_eq

theorem sessionCapBytes_val : sessionCapBytes = 2097152 := rfl

theorem spqrStateTightCapBytes_val : spqrStateTightCapBytes = 286196 := rfl

theorem msgCapBytes_val : msgCapBytes = 1048576 := rfl

/-! ## Closed-Form RAM and VA Budget Functions -/

/-- Closed-form upper bound on `fineCostModel.footprint b` given `(cumB, peakB)`. -/
def cliFootprintBound (cumB peakB : Nat) : Nat :=
  cliBaseFine + cumB + peakB

/-- Physical RAM bound required by `fitsTrace_fineCostModel_of_phaseCredit`. -/
def cliRamNeed (staticBytes cumB peakB maxReq : Nat) : Nat :=
  staticBytes + cliFootprintBound cumB peakB + 2 * fineStepReserveOfCum maxReq 16 cumB

/-- 48-bit virtual-address bound required by `fitsTrace_fineCostModel_of_phaseCredit`. -/
def cliVaNeed (staticBytes staticCount cumB peakB maxReq : Nat) : Nat :=
  MMAP_MIN_ADDR + staticBytes + cliFootprintBound cumB peakB +
    fineStepReserveOfCum maxReq 16 cumB +
    (staticCount + fineDynIvsOfCum cumB + 16) *
      (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
    fineStepReserveOfCum maxReq 16 cumB

theorem fineMaxGroupsOfCum_mono {c₁ c₂ : Nat} (hc : c₁ ≤ c₂) :
    fineMaxGroupsOfCum c₁ ≤ fineMaxGroupsOfCum c₂ := by
  unfold fineMaxGroupsOfCum
  omega

theorem fineMaxMetaAreasOfCum_mono {c₁ c₂ : Nat} (hc : c₁ ≤ c₂) :
    fineMaxMetaAreasOfCum c₁ ≤ fineMaxMetaAreasOfCum c₂ := by
  unfold fineMaxMetaAreasOfCum
  omega

theorem fineDynIvsOfCum_mono {c₁ c₂ : Nat} (hc : c₁ ≤ c₂) :
    fineDynIvsOfCum c₁ ≤ fineDynIvsOfCum c₂ := by
  have hg := fineMaxGroupsOfCum_mono hc
  have hm := fineMaxMetaAreasOfCum_mono hc
  unfold fineDynIvsOfCum
  omega

theorem fineStepReserveOfCum_mono {r₁ r₂ c₁ c₂ : Nat}
    (hr : r₁ ≤ r₂) (hc : c₁ ≤ c₂) :
    fineStepReserveOfCum r₁ 16 c₁ ≤ fineStepReserveOfCum r₂ 16 c₂ := by
  unfold fineStepReserveOfCum
  exact FineStepBound_mono hr (Nat.le_refl _) (fineMaxMetaAreasOfCum_mono hc)

theorem cliFootprintBound_mono {c₁ c₂ p₁ p₂ : Nat} (hc : c₁ ≤ c₂) (hp : p₁ ≤ p₂) :
    cliFootprintBound c₁ p₁ ≤ cliFootprintBound c₂ p₂ := by
  unfold cliFootprintBound
  omega

theorem cliRamNeed_mono {sb₁ sb₂ c₁ c₂ p₁ p₂ r₁ r₂ : Nat}
    (hsb : sb₁ ≤ sb₂) (hc : c₁ ≤ c₂) (hp : p₁ ≤ p₂) (hr : r₁ ≤ r₂) :
    cliRamNeed sb₁ c₁ p₁ r₁ ≤ cliRamNeed sb₂ c₂ p₂ r₂ := by
  have hfp := cliFootprintBound_mono hc hp
  have hst := fineStepReserveOfCum_mono hr hc
  unfold cliRamNeed
  omega

theorem cliVaNeed_mono {sb₁ sb₂ sc₁ sc₂ c₁ c₂ p₁ p₂ r₁ r₂ : Nat}
    (hsb : sb₁ ≤ sb₂) (hsc : sc₁ ≤ sc₂) (hc : c₁ ≤ c₂) (hp : p₁ ≤ p₂) (hr : r₁ ≤ r₂) :
    cliVaNeed sb₁ sc₁ c₁ p₁ r₁ ≤ cliVaNeed sb₂ sc₂ c₂ p₂ r₂ := by
  have hfp := cliFootprintBound_mono hc hp
  have hst := fineStepReserveOfCum_mono hr hc
  have hdyn := fineDynIvsOfCum_mono hc
  have hmul :
      (sc₁ + fineDynIvsOfCum c₁ + 16) * (fineStepReserveOfCum r₁ 16 c₁ + PAGE_SIZE) ≤
        (sc₂ + fineDynIvsOfCum c₂ + 16) * (fineStepReserveOfCum r₂ 16 c₂ + PAGE_SIZE) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold cliVaNeed
  omega

/-- Weakens `PhaseCreditSpec fineCostModel` to literal caps `(cumCap, peakCap, reqCap)` and
discharges `FitsTrace fineCostModel` from `cliRamNeed ≤ lim.physCap` and `cliVaNeed ≤ 2 ^ 48`. -/
theorem fitsTrace_fineCostModel_of_literal_bounds
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {cumB liveB peakB maxReq cumCap peakCap reqCap : Nat}
    (hSpec : PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq)
    (hcum : cumB ≤ cumCap)
    (hlive : liveB ≤ peakCap)
    (hpeak : peakB ≤ peakCap)
    (hreq : maxReq ≤ reqCap)
    (henf : lim.enforced = true)
    (hram : cliRamNeed lim.staticBytes cumCap peakCap reqCap ≤ lim.physCap)
    (hva : cliVaNeed lim.staticBytes lim.staticCount cumCap peakCap reqCap ≤ 2 ^ 48)
    {fullLog : List AllocEvent} (hEnv : Env fullLog) :
    FitsTrace fineCostModel lim (fineStepReserveOfCum reqCap 16 cumCap) fullLog := by
  have hCapSpec : PhaseCreditSpec fineCostModel Env cumCap peakCap peakCap reqCap :=
    hSpec.mono hcum hlive hpeak hreq
  exact fitsTrace_fineCostModel_of_phaseCredit hCapSpec (Nat.le_refl peakCap) henf
    (by simpa only [cliRamNeed, cliFootprintBound, cliBaseFine] using hram)
    (by simpa only [cliVaNeed, cliFootprintBound, cliBaseFine] using hva)
    hEnv

/-- Discharges `FitsEnv fineCostModel` at `fineCostModel.init` from literal credit caps. -/
theorem fitsEnv_fineCostModel_of_literal_bounds
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {cumB liveB peakB maxReq cumCap peakCap reqCap : Nat}
    (hSpec : PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq)
    (hcum : cumB ≤ cumCap)
    (hlive : liveB ≤ peakCap)
    (hpeak : peakB ≤ peakCap)
    (hreq : maxReq ≤ reqCap)
    (henf : lim.enforced = true)
    (hram : cliRamNeed lim.staticBytes cumCap peakCap reqCap ≤ lim.physCap)
    (hva : cliVaNeed lim.staticBytes lim.staticCount cumCap peakCap reqCap ≤ 2 ^ 48) :
    FitsEnv fineCostModel lim fineCostModel.init Env := by
  have hCapSpec : PhaseCreditSpec fineCostModel Env cumCap peakCap peakCap reqCap :=
    hSpec.mono hcum hlive hpeak hreq
  exact fitsEnv_fineCostModel_of_phaseCredit hCapSpec (Nat.le_refl peakCap) henf
    (by simpa only [cliRamNeed, cliFootprintBound, cliBaseFine] using hram)
    (by simpa only [cliVaNeed, cliFootprintBound, cliBaseFine] using hva)

/-- Physical RAM bound required by `fitsTrace_fineCostModel_of_phaseCredit_groups` when
group creation `(fineGroupsScaled + FineScale - 1) / FineScale` is bounded by `grpB`. -/
def cliDecoupledRamNeed (staticBytes cumB peakB maxReq grpB : Nat) : Nat :=
  staticBytes + cliFootprintBound cumB peakB + 2 * fineStepReserveOfGroups maxReq 16 grpB

/-- 48-bit virtual-address bound required by `fitsTrace_fineCostModel_of_phaseCredit_groups`
under decoupled group bound `grpB`. -/
def cliDecoupledVaNeed (staticBytes staticCount cumB peakB maxReq grpB : Nat) : Nat :=
  MMAP_MIN_ADDR + staticBytes + cliFootprintBound cumB peakB +
    fineStepReserveOfGroups maxReq 16 grpB +
    (staticCount + fineDynIvsOfGroups grpB + 16) *
      (fineStepReserveOfGroups maxReq 16 grpB + PAGE_SIZE) +
    fineStepReserveOfGroups maxReq 16 grpB

theorem cliDecoupledRamNeed_mono {sb₁ sb₂ c₁ c₂ p₁ p₂ r₁ r₂ g₁ g₂ : Nat}
    (hsb : sb₁ ≤ sb₂) (hc : c₁ ≤ c₂) (hp : p₁ ≤ p₂) (hr : r₁ ≤ r₂) (hg : g₁ ≤ g₂) :
    cliDecoupledRamNeed sb₁ c₁ p₁ r₁ g₁ ≤ cliDecoupledRamNeed sb₂ c₂ p₂ r₂ g₂ := by
  have hfp := cliFootprintBound_mono hc hp
  have hst : fineStepReserveOfGroups r₁ 16 g₁ ≤ fineStepReserveOfGroups r₂ 16 g₂ :=
    fineStepReserveOfGroups_mono hr (Nat.le_refl _) hg
  unfold cliDecoupledRamNeed
  omega

theorem cliDecoupledVaNeed_mono {sb₁ sb₂ sc₁ sc₂ c₁ c₂ p₁ p₂ r₁ r₂ g₁ g₂ : Nat}
    (hsb : sb₁ ≤ sb₂) (hsc : sc₁ ≤ sc₂) (hc : c₁ ≤ c₂) (hp : p₁ ≤ p₂)
    (hr : r₁ ≤ r₂) (hg : g₁ ≤ g₂) :
    cliDecoupledVaNeed sb₁ sc₁ c₁ p₁ r₁ g₁ ≤ cliDecoupledVaNeed sb₂ sc₂ c₂ p₂ r₂ g₂ := by
  have hfp := cliFootprintBound_mono hc hp
  have hst : fineStepReserveOfGroups r₁ 16 g₁ ≤ fineStepReserveOfGroups r₂ 16 g₂ :=
    fineStepReserveOfGroups_mono hr (Nat.le_refl _) hg
  have hdyn := fineDynIvsOfGroups_mono hg
  have hmul :
      (sc₁ + fineDynIvsOfGroups g₁ + 16) * (fineStepReserveOfGroups r₁ 16 g₁ + PAGE_SIZE) ≤
        (sc₂ + fineDynIvsOfGroups g₂ + 16) * (fineStepReserveOfGroups r₂ 16 g₂ + PAGE_SIZE) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold cliDecoupledVaNeed
  omega

/-- Weakens `(PhaseCreditSpec, PhaseGroupSpec)` bounds to literal caps
`(cumCap, peakCap, reqCap, grpCap)` and discharges `FitsTrace fineCostModel`. -/
theorem fitsTrace_fineCostModel_of_group_literal_bounds
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {cumB liveB peakB maxReq grpS cumCap peakCap reqCap grpCap : Nat}
    (hSpec : PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq)
    (hGrp : PhaseGroupSpec fineCostModel Env grpS)
    (hcum : cumB ≤ cumCap)
    (hlive : liveB ≤ peakCap)
    (hpeak : peakB ≤ peakCap)
    (hreq : maxReq ≤ reqCap)
    (hgrp : (grpS + FineScale - 1) / FineScale ≤ grpCap)
    (henf : lim.enforced = true)
    (hram : cliDecoupledRamNeed lim.staticBytes cumCap peakCap reqCap grpCap ≤ lim.physCap)
    (hva : cliDecoupledVaNeed lim.staticBytes lim.staticCount cumCap peakCap reqCap grpCap ≤ 2 ^ 48)
    {fullLog : List AllocEvent} (hEnv : Env fullLog) :
    FitsTrace fineCostModel lim (fineStepReserveOfGroups reqCap 16 grpCap) fullLog := by
  have hCapSpec : PhaseCreditSpec fineCostModel Env cumCap peakCap peakCap reqCap :=
    hSpec.mono hcum hlive hpeak hreq
  exact fitsTrace_fineCostModel_of_phaseCredit_groups
    hCapSpec hGrp (Nat.le_refl peakCap) hgrp henf
    (by simpa only [cliDecoupledRamNeed, cliFootprintBound, cliBaseFine] using hram)
    (by simpa only [cliDecoupledVaNeed, cliFootprintBound, cliBaseFine] using hva)
    hEnv

/-- Discharges `FitsEnv fineCostModel` at `fineCostModel.init` from literal credit and group caps. -/
theorem fitsEnv_fineCostModel_of_group_literal_bounds
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {cumB liveB peakB maxReq grpS cumCap peakCap reqCap grpCap : Nat}
    (hSpec : PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq)
    (hGrp : PhaseGroupSpec fineCostModel Env grpS)
    (hcum : cumB ≤ cumCap)
    (hlive : liveB ≤ peakCap)
    (hpeak : peakB ≤ peakCap)
    (hreq : maxReq ≤ reqCap)
    (hgrp : (grpS + FineScale - 1) / FineScale ≤ grpCap)
    (henf : lim.enforced = true)
    (hram : cliDecoupledRamNeed lim.staticBytes cumCap peakCap reqCap grpCap ≤ lim.physCap)
    (hva : cliDecoupledVaNeed lim.staticBytes lim.staticCount cumCap peakCap reqCap grpCap ≤ 2 ^ 48) :
    FitsEnv fineCostModel lim fineCostModel.init Env := by
  have hCapSpec : PhaseCreditSpec fineCostModel Env cumCap peakCap peakCap reqCap :=
    hSpec.mono hcum hlive hpeak hreq
  exact fitsEnv_fineCostModel_of_phaseCredit_groups
    hCapSpec hGrp (Nat.le_refl peakCap) hgrp henf
    (by simpa only [cliDecoupledRamNeed, cliFootprintBound, cliBaseFine] using hram)
    (by simpa only [cliDecoupledVaNeed, cliFootprintBound, cliBaseFine] using hva)

/-! ## Sequential 6-Phase `main` Composition -/

/-- Whole-`main` 6-phase envelope: setup phases `M1 → M2 → M3` followed either by early-exit
`FreeOnlyEvs` or by `M4Run → M5 → M6`. -/
def CliMainSixPhaseEnv
    (M1 M2 M3 M4Run M5 M6 : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (SeqEnv M1 (SeqEnv M2 M3))
    (fun evs' => FreeOnlyEvs evs' ∨ SeqEnv M4Run (SeqEnv M5 M6) evs')
    evs

/-- Per-phase `(Δcum, Δlive, Δpeak, maxReq)` tuple bundle for the 6 sequential phases of `main`. -/
structure CliMainPhaseBounds where
  c1 : Nat
  l1 : Nat
  p1 : Nat
  r1 : Nat
  c2 : Nat
  l2 : Nat
  p2 : Nat
  r2 : Nat
  c3 : Nat
  l3 : Nat
  p3 : Nat
  r3 : Nat
  c4 : Nat
  l4 : Nat
  p4 : Nat
  r4 : Nat
  c5 : Nat
  l5 : Nat
  p5 : Nat
  r5 : Nat
  c6 : Nat
  l6 : Nat
  p6 : Nat
  r6 : Nat

namespace CliMainPhaseBounds

def setupCum (B : CliMainPhaseBounds) : Nat := B.c1 + B.c2 + B.c3

def setupLive (B : CliMainPhaseBounds) : Nat := B.l1 + B.l2 + B.l3

def setupPeak (B : CliMainPhaseBounds) : Nat :=
  max B.p1 (B.l1 + max B.p2 (B.l2 + B.p3))

def setupMaxReq (B : CliMainPhaseBounds) : Nat :=
  max B.r1 (max B.r2 B.r3)

def bodyCum (B : CliMainPhaseBounds) : Nat := B.c4 + B.c5 + B.c6

def bodyLive (B : CliMainPhaseBounds) : Nat := B.l4 + B.l5 + B.l6

def bodyPeak (B : CliMainPhaseBounds) : Nat :=
  max B.p4 (B.l4 + max B.p5 (B.l5 + B.p6))

def bodyMaxReq (B : CliMainPhaseBounds) : Nat :=
  max B.r4 (max B.r5 B.r6)

def totalCum (B : CliMainPhaseBounds) : Nat := B.setupCum + B.bodyCum

def totalLive (B : CliMainPhaseBounds) : Nat := B.setupLive + B.bodyLive

def totalPeak (B : CliMainPhaseBounds) : Nat :=
  max B.setupPeak (B.setupLive + B.bodyPeak)

def totalMaxReq (B : CliMainPhaseBounds) : Nat :=
  max B.setupMaxReq B.bodyMaxReq

theorem totalLive_le_totalPeak (B : CliMainPhaseBounds)
    (hl6 : B.l6 ≤ B.p6) :
    B.totalLive ≤ B.totalPeak := by
  unfold totalLive totalPeak setupLive bodyLive bodyPeak
  omega

end CliMainPhaseBounds

/-- Composes per-phase `PhaseCreditSpec M` bounds for `M1..M6` across `CliMainSixPhaseEnv`. -/
theorem cliMainSixPhase_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    {M1 M2 M3 M4Run M5 M6 : List AllocEvent → Prop}
    (B : CliMainPhaseBounds)
    (h1 : PhaseCreditSpec M M1 B.c1 B.l1 B.p1 B.r1)
    (h2 : PhaseCreditSpec M M2 B.c2 B.l2 B.p2 B.r2)
    (h3 : PhaseCreditSpec M M3 B.c3 B.l3 B.p3 B.r3)
    (h4 : PhaseCreditSpec M M4Run B.c4 B.l4 B.p4 B.r4)
    (h5 : PhaseCreditSpec M M5 B.c5 B.l5 B.p5 B.r5)
    (h6 : PhaseCreditSpec M M6 B.c6 B.l6 B.p6 B.r6) :
    PhaseCreditSpec M (CliMainSixPhaseEnv M1 M2 M3 M4Run M5 M6)
      B.totalCum B.totalLive B.totalPeak B.totalMaxReq := by
  unfold CliMainSixPhaseEnv
  have h23 := h2.seq h3
  have h123 : PhaseCreditSpec M (SeqEnv M1 (SeqEnv M2 M3))
      B.setupCum B.setupLive B.setupPeak B.setupMaxReq :=
    (h1.seq h23).mono
      (by unfold CliMainPhaseBounds.setupCum; omega)
      (by unfold CliMainPhaseBounds.setupLive; omega)
      (by unfold CliMainPhaseBounds.setupPeak; omega)
      (by unfold CliMainPhaseBounds.setupMaxReq; omega)
  have h56 := h5.seq h6
  have h456 : PhaseCreditSpec M (SeqEnv M4Run (SeqEnv M5 M6))
      B.bodyCum B.bodyLive B.bodyPeak B.bodyMaxReq :=
    (h4.seq h56).mono
      (by unfold CliMainPhaseBounds.bodyCum; omega)
      (by unfold CliMainPhaseBounds.bodyLive; omega)
      (by unfold CliMainPhaseBounds.bodyPeak; omega)
      (by unfold CliMainPhaseBounds.bodyMaxReq; omega)
  have hTail : PhaseCreditSpec M
      (fun evs' => FreeOnlyEvs evs' ∨ SeqEnv M4Run (SeqEnv M5 M6) evs')
      B.bodyCum B.bodyLive B.bodyPeak B.bodyMaxReq :=
    ((PhaseCreditSpec.freeOnly hM.freeNonInc).or h456).mono
      (by omega) (by omega) (by omega) (by omega)
  exact (h123.seq hTail).mono
    (by unfold CliMainPhaseBounds.totalCum; omega)
    (by unfold CliMainPhaseBounds.totalLive; omega)
    (by unfold CliMainPhaseBounds.totalPeak; omega)
    (by unfold CliMainPhaseBounds.totalMaxReq; omega)

/-- Whole-`main` `FitsTrace fineCostModel` from per-phase `PhaseCreditSpec` bounds (`M1..M6`)
and literal budget caps `(cumCap, peakCap, reqCap)`. -/
theorem cliMain_fitsTrace_fineCostModel_interface
    {lim : BudgetLimits}
    {M1 M2 M3 M4Run M5 M6 : List AllocEvent → Prop}
    (B : CliMainPhaseBounds)
    {cumCap peakCap reqCap : Nat}
    (h1 : PhaseCreditSpec fineCostModel M1 B.c1 B.l1 B.p1 B.r1)
    (h2 : PhaseCreditSpec fineCostModel M2 B.c2 B.l2 B.p2 B.r2)
    (h3 : PhaseCreditSpec fineCostModel M3 B.c3 B.l3 B.p3 B.r3)
    (h4 : PhaseCreditSpec fineCostModel M4Run B.c4 B.l4 B.p4 B.r4)
    (h5 : PhaseCreditSpec fineCostModel M5 B.c5 B.l5 B.p5 B.r5)
    (h6 : PhaseCreditSpec fineCostModel M6 B.c6 B.l6 B.p6 B.r6)
    (hcum : B.totalCum ≤ cumCap)
    (hlive : B.totalLive ≤ peakCap)
    (hpeak : B.totalPeak ≤ peakCap)
    (hreq : B.totalMaxReq ≤ reqCap)
    (henf : lim.enforced = true)
    (hram : cliRamNeed lim.staticBytes cumCap peakCap reqCap ≤ lim.physCap)
    (hva : cliVaNeed lim.staticBytes lim.staticCount cumCap peakCap reqCap ≤ 2 ^ 48)
    {fullLog : List AllocEvent}
    (hEnv : CliMainSixPhaseEnv M1 M2 M3 M4Run M5 M6 fullLog) :
    FitsTrace fineCostModel lim (fineStepReserveOfCum reqCap 16 cumCap) fullLog :=
  fitsTrace_fineCostModel_of_literal_bounds
    (cliMainSixPhase_phaseCredit fineCostModel_modelHyps B h1 h2 h3 h4 h5 h6)
    hcum hlive hpeak hreq henf hram hva hEnv

/-- Whole-`main` `FitsEnv fineCostModel` at `fineCostModel.init` from per-phase
`PhaseCreditSpec` bounds (`M1..M6`) and literal budget caps. -/
theorem cliMain_fitsEnv_fineCostModel_interface
    {lim : BudgetLimits}
    {M1 M2 M3 M4Run M5 M6 : List AllocEvent → Prop}
    (B : CliMainPhaseBounds)
    {cumCap peakCap reqCap : Nat}
    (h1 : PhaseCreditSpec fineCostModel M1 B.c1 B.l1 B.p1 B.r1)
    (h2 : PhaseCreditSpec fineCostModel M2 B.c2 B.l2 B.p2 B.r2)
    (h3 : PhaseCreditSpec fineCostModel M3 B.c3 B.l3 B.p3 B.r3)
    (h4 : PhaseCreditSpec fineCostModel M4Run B.c4 B.l4 B.p4 B.r4)
    (h5 : PhaseCreditSpec fineCostModel M5 B.c5 B.l5 B.p5 B.r5)
    (h6 : PhaseCreditSpec fineCostModel M6 B.c6 B.l6 B.p6 B.r6)
    (hcum : B.totalCum ≤ cumCap)
    (hlive : B.totalLive ≤ peakCap)
    (hpeak : B.totalPeak ≤ peakCap)
    (hreq : B.totalMaxReq ≤ reqCap)
    (henf : lim.enforced = true)
    (hram : cliRamNeed lim.staticBytes cumCap peakCap reqCap ≤ lim.physCap)
    (hva : cliVaNeed lim.staticBytes lim.staticCount cumCap peakCap reqCap ≤ 2 ^ 48) :
    FitsEnv fineCostModel lim fineCostModel.init (CliMainSixPhaseEnv M1 M2 M3 M4Run M5 M6) :=
  fitsEnv_fineCostModel_of_literal_bounds
    (cliMainSixPhase_phaseCredit fineCostModel_modelHyps B h1 h2 h3 h4 h5 h6)
    hcum hlive hpeak hreq henf hram hva

/-- Per-phase `FineScale`-scaled group delta bundle (`g1..g6`) for the 6 sequential phases of `main`. -/
structure CliMainGroupBounds where
  g1 : Nat
  g2 : Nat
  g3 : Nat
  g4 : Nat
  g5 : Nat
  g6 : Nat

namespace CliMainGroupBounds

def setupGrpS (G : CliMainGroupBounds) : Nat := G.g1 + G.g2 + G.g3

def bodyGrpS (G : CliMainGroupBounds) : Nat := G.g4 + G.g5 + G.g6

def totalGrpS (G : CliMainGroupBounds) : Nat := G.setupGrpS + G.bodyGrpS

def totalGroups (G : CliMainGroupBounds) : Nat :=
  (G.totalGrpS + FineScale - 1) / FineScale

end CliMainGroupBounds

/-- Composes per-phase `PhaseGroupSpec M` bounds for `M1..M6` across `CliMainSixPhaseEnv`. -/
theorem cliMainSixPhase_phaseGroups {M : AllocCostModel} [HasFineGroupCredit M]
    {M1 M2 M3 M4Run M5 M6 : List AllocEvent → Prop}
    (G : CliMainGroupBounds)
    (hg1 : PhaseGroupSpec M M1 G.g1)
    (hg2 : PhaseGroupSpec M M2 G.g2)
    (hg3 : PhaseGroupSpec M M3 G.g3)
    (hg4 : PhaseGroupSpec M M4Run G.g4)
    (hg5 : PhaseGroupSpec M M5 G.g5)
    (hg6 : PhaseGroupSpec M M6 G.g6) :
    PhaseGroupSpec M (CliMainSixPhaseEnv M1 M2 M3 M4Run M5 M6) G.totalGrpS := by
  unfold CliMainSixPhaseEnv
  have h23 := hg2.seq hg3
  have h123 : PhaseGroupSpec M (SeqEnv M1 (SeqEnv M2 M3)) G.setupGrpS :=
    (hg1.seq h23).mono (by unfold CliMainGroupBounds.setupGrpS; omega)
  have h56 := hg5.seq hg6
  have h456 : PhaseGroupSpec M (SeqEnv M4Run (SeqEnv M5 M6)) G.bodyGrpS :=
    (hg4.seq h56).mono (by unfold CliMainGroupBounds.bodyGrpS; omega)
  have hTail : PhaseGroupSpec M
      (fun evs' => FreeOnlyEvs evs' ∨ SeqEnv M4Run (SeqEnv M5 M6) evs')
      G.bodyGrpS :=
    ((PhaseGroupSpec.freeOnly M).or h456).mono (by omega)
  exact (h123.seq hTail).mono (by unfold CliMainGroupBounds.totalGrpS; omega)

/-- Decoupled-group whole-`main` `FitsTrace fineCostModel` from per-phase
`PhaseCreditSpec` and `PhaseGroupSpec` bounds (`M1..M6`) and literal caps. -/
theorem cliMain_fitsTrace_fineCostModel_groups_interface
    {lim : BudgetLimits}
    {M1 M2 M3 M4Run M5 M6 : List AllocEvent → Prop}
    (B : CliMainPhaseBounds)
    (G : CliMainGroupBounds)
    {cumCap peakCap reqCap grpCap : Nat}
    (h1 : PhaseCreditSpec fineCostModel M1 B.c1 B.l1 B.p1 B.r1)
    (h2 : PhaseCreditSpec fineCostModel M2 B.c2 B.l2 B.p2 B.r2)
    (h3 : PhaseCreditSpec fineCostModel M3 B.c3 B.l3 B.p3 B.r3)
    (h4 : PhaseCreditSpec fineCostModel M4Run B.c4 B.l4 B.p4 B.r4)
    (h5 : PhaseCreditSpec fineCostModel M5 B.c5 B.l5 B.p5 B.r5)
    (h6 : PhaseCreditSpec fineCostModel M6 B.c6 B.l6 B.p6 B.r6)
    (hg1 : PhaseGroupSpec fineCostModel M1 G.g1)
    (hg2 : PhaseGroupSpec fineCostModel M2 G.g2)
    (hg3 : PhaseGroupSpec fineCostModel M3 G.g3)
    (hg4 : PhaseGroupSpec fineCostModel M4Run G.g4)
    (hg5 : PhaseGroupSpec fineCostModel M5 G.g5)
    (hg6 : PhaseGroupSpec fineCostModel M6 G.g6)
    (hcum : B.totalCum ≤ cumCap)
    (hlive : B.totalLive ≤ peakCap)
    (hpeak : B.totalPeak ≤ peakCap)
    (hreq : B.totalMaxReq ≤ reqCap)
    (hgrp : G.totalGroups ≤ grpCap)
    (henf : lim.enforced = true)
    (hram : cliDecoupledRamNeed lim.staticBytes cumCap peakCap reqCap grpCap ≤ lim.physCap)
    (hva : cliDecoupledVaNeed lim.staticBytes lim.staticCount cumCap peakCap reqCap grpCap ≤ 2 ^ 48)
    {fullLog : List AllocEvent}
    (hEnv : CliMainSixPhaseEnv M1 M2 M3 M4Run M5 M6 fullLog) :
    FitsTrace fineCostModel lim (fineStepReserveOfGroups reqCap 16 grpCap) fullLog :=
  fitsTrace_fineCostModel_of_group_literal_bounds
    (cliMainSixPhase_phaseCredit fineCostModel_modelHyps B h1 h2 h3 h4 h5 h6)
    (cliMainSixPhase_phaseGroups G hg1 hg2 hg3 hg4 hg5 hg6)
    hcum hlive hpeak hreq hgrp henf hram hva hEnv

/-- Decoupled-group whole-`main` `FitsEnv fineCostModel` at `fineCostModel.init` from
per-phase `PhaseCreditSpec` and `PhaseGroupSpec` bounds (`M1..M6`) and literal caps. -/
theorem cliMain_fitsEnv_fineCostModel_groups_interface
    {lim : BudgetLimits}
    {M1 M2 M3 M4Run M5 M6 : List AllocEvent → Prop}
    (B : CliMainPhaseBounds)
    (G : CliMainGroupBounds)
    {cumCap peakCap reqCap grpCap : Nat}
    (h1 : PhaseCreditSpec fineCostModel M1 B.c1 B.l1 B.p1 B.r1)
    (h2 : PhaseCreditSpec fineCostModel M2 B.c2 B.l2 B.p2 B.r2)
    (h3 : PhaseCreditSpec fineCostModel M3 B.c3 B.l3 B.p3 B.r3)
    (h4 : PhaseCreditSpec fineCostModel M4Run B.c4 B.l4 B.p4 B.r4)
    (h5 : PhaseCreditSpec fineCostModel M5 B.c5 B.l5 B.p5 B.r5)
    (h6 : PhaseCreditSpec fineCostModel M6 B.c6 B.l6 B.p6 B.r6)
    (hg1 : PhaseGroupSpec fineCostModel M1 G.g1)
    (hg2 : PhaseGroupSpec fineCostModel M2 G.g2)
    (hg3 : PhaseGroupSpec fineCostModel M3 G.g3)
    (hg4 : PhaseGroupSpec fineCostModel M4Run G.g4)
    (hg5 : PhaseGroupSpec fineCostModel M5 G.g5)
    (hg6 : PhaseGroupSpec fineCostModel M6 G.g6)
    (hcum : B.totalCum ≤ cumCap)
    (hlive : B.totalLive ≤ peakCap)
    (hpeak : B.totalPeak ≤ peakCap)
    (hreq : B.totalMaxReq ≤ reqCap)
    (hgrp : G.totalGroups ≤ grpCap)
    (henf : lim.enforced = true)
    (hram : cliDecoupledRamNeed lim.staticBytes cumCap peakCap reqCap grpCap ≤ lim.physCap)
    (hva : cliDecoupledVaNeed lim.staticBytes lim.staticCount cumCap peakCap reqCap grpCap ≤ 2 ^ 48) :
    FitsEnv fineCostModel lim fineCostModel.init (CliMainSixPhaseEnv M1 M2 M3 M4Run M5 M6) :=
  fitsEnv_fineCostModel_of_group_literal_bounds
    (cliMainSixPhase_phaseCredit fineCostModel_modelHyps B h1 h2 h3 h4 h5 h6)
    (cliMainSixPhase_phaseGroups G hg1 hg2 hg3 hg4 hg5 hg6)
    hcum hlive hpeak hreq hgrp henf hram hva

/-! ## Concrete `1 GiB` RAM and `2 ^ 48` VA Closure Bounds -/

theorem fineStepReserveOfCum_tight_34M_eq :
    fineStepReserveOfCum 4200000 16 34000000 = 387334144 := by
  decide

theorem fineDynIvsOfCum_tight_34M_eq :
    fineDynIvsOfCum 34000000 = 287252 := by
  decide

/-- Physical RAM bound `< 1 GiB` (`2 ^ 30`) at `staticBytes = 16 MiB`, `cumB ≤ 34,000,000`,
`peakB ≤ 200,000,000`, and `maxReq ≤ 4,200,000` (`1,044,131,656 ≤ 2 ^ 30`). -/
theorem cliRamNeed_le_oneGiB_of_tight_34M :
    cliRamNeed cliDefaultStaticBytes 34000000 200000000 4200000 ≤ cliOneGiB := by
  decide

/-- Virtual-address bound `≤ 2 ^ 48` at `(34,000,000, 200,000,000, 4,200,000)`. -/
theorem cliVaNeed_le_2_48_of_tight_34M :
    cliVaNeed cliDefaultStaticBytes cliDefaultStaticCount 34000000 200000000 4200000 ≤ 2 ^ 48 := by
  decide

/-- `1 GiB` `FitsTrace fineCostModel` bound for any envelope with `cumB ≤ 34,000,000`,
`liveB ≤ 200,000,000`, `peakB ≤ 200,000,000`, and `maxReq ≤ 4,200,000`. -/
theorem fitsTrace_oneGiB_of_phaseCredit_34M
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {cumB liveB peakB maxReq : Nat}
    (hSpec : PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq)
    (hcum : cumB ≤ 34000000)
    (hlive : liveB ≤ 200000000)
    (hpeak : peakB ≤ 200000000)
    (hreq : maxReq ≤ 4200000)
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {fullLog : List AllocEvent} (hEnv : Env fullLog) :
    FitsTrace fineCostModel lim (fineStepReserveOfCum 4200000 16 34000000) fullLog := by
  have hram : cliRamNeed lim.staticBytes 34000000 200000000 4200000 ≤ lim.physCap :=
    Nat.le_trans
      (cliRamNeed_mono hsb (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans cliRamNeed_le_oneGiB_of_tight_34M hcap)
  have hva : cliVaNeed lim.staticBytes lim.staticCount 34000000 200000000 4200000 ≤ 2 ^ 48 :=
    Nat.le_trans
      (cliVaNeed_mono hsb hsc (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      cliVaNeed_le_2_48_of_tight_34M
  exact fitsTrace_fineCostModel_of_literal_bounds hSpec hcum hlive hpeak hreq henf hram hva hEnv

/-- `1 GiB` `FitsEnv fineCostModel` bound at `fineCostModel.init` under the `34M` cap profile. -/
theorem fitsEnv_oneGiB_of_phaseCredit_34M
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {cumB liveB peakB maxReq : Nat}
    (hSpec : PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq)
    (hcum : cumB ≤ 34000000)
    (hlive : liveB ≤ 200000000)
    (hpeak : peakB ≤ 200000000)
    (hreq : maxReq ≤ 4200000)
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap) :
    FitsEnv fineCostModel lim fineCostModel.init Env := by
  have hram : cliRamNeed lim.staticBytes 34000000 200000000 4200000 ≤ lim.physCap :=
    Nat.le_trans
      (cliRamNeed_mono hsb (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans cliRamNeed_le_oneGiB_of_tight_34M hcap)
  have hva : cliVaNeed lim.staticBytes lim.staticCount 34000000 200000000 4200000 ≤ 2 ^ 48 :=
    Nat.le_trans
      (cliVaNeed_mono hsb hsc (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      cliVaNeed_le_2_48_of_tight_34M
  exact fitsEnv_fineCostModel_of_literal_bounds hSpec hcum hlive hpeak hreq henf hram hva

/-- Concrete 6-phase `main` budget profile summing to `totalCum = 24,000,000` B,
`totalPeak ≤ 45,000,000` B, and `totalMaxReq = 2,101,248` B. -/
def tightenedCliMainBounds : CliMainPhaseBounds where
  c1 := 30000
  l1 := 0
  p1 := 0
  r1 := 48
  c2 := 30000
  l2 := 0
  p2 := 0
  r2 := 64
  c3 := 1147514
  l3 := 3162112
  p3 := 5267456
  r3 := 2097152
  c4 := 22618300
  l4 := 16000000
  p4 := 39000000
  r4 := 2101248
  c5 := 162599
  l5 := 0
  p5 := 25593
  r5 := 336
  c6 := 11587
  l6 := 0
  p6 := 0
  r6 := 1024

theorem tightenedCliMainBounds_closes_34M :
    tightenedCliMainBounds.totalCum ≤ 34000000 ∧
    tightenedCliMainBounds.totalLive ≤ 200000000 ∧
    tightenedCliMainBounds.totalPeak ≤ 200000000 ∧
    tightenedCliMainBounds.totalMaxReq ≤ 4200000 := by
  decide

theorem fineOfGroups_4096_eq :
    fineMaxGroupsOfGroups 4096 = 4368 ∧
    fineMaxMetaAreasOfGroups 4096 = 44 ∧
    fineDynIvsOfGroups 4096 = 4502 := by
  decide

/-- At `grpB = 4,096`, `(cumB, peakB, maxReq) = (200,000,000, 120,000,000, 4,200,000)` requires
`417,362,120 ≤ 2 ^ 30` B RAM and `142,246,236,360 ≤ 2 ^ 48` VA. -/
theorem decoupledGroups_200M_closes_oneGiB_and_va :
    cliDecoupledRamNeed cliDefaultStaticBytes 200000000 120000000 4200000 4096 = 417362120 ∧
    cliDecoupledRamNeed cliDefaultStaticBytes 200000000 120000000 4200000 4096 ≤ cliOneGiB ∧
    cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
      200000000 120000000 4200000 4096 = 142246236360 ∧
    cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
      200000000 120000000 4200000 4096 ≤ 2 ^ 48 := by
  decide

/-- Physical RAM bound `≤ 1 GiB` under decoupled-group caps
`(760,000,000, 60,000,000, 4,200,000, 50,000)` (`1,036,375,496 ≤ 2 ^ 30`). -/
theorem cliDecoupledRamNeed_le_oneGiB_of_S4 :
    cliDecoupledRamNeed cliDefaultStaticBytes 760000000 60000000 4200000 50000 ≤ cliOneGiB := by
  decide

/-- Virtual-address bound `≤ 2 ^ 48` under decoupled-group caps `(760,000,000, 60,000,000, 4,200,000, 50,000)`. -/
theorem cliDecoupledVaNeed_le_2_48_of_S4 :
    cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
      760000000 60000000 4200000 50000 ≤ 2 ^ 48 := by
  decide

/-- `1 GiB` decoupled-group `FitsTrace fineCostModel` bound for any envelope within
`(760,000,000, 60,000,000, 60,000,000, 4,200,000)` and `≤ 50,000` groups. -/
theorem fitsTrace_oneGiB_of_group_bounds_S4
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {cumB liveB peakB maxReq grpS : Nat}
    (hSpec : PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq)
    (hGrp : PhaseGroupSpec fineCostModel Env grpS)
    (hcum : cumB ≤ 760000000)
    (hlive : liveB ≤ 60000000)
    (hpeak : peakB ≤ 60000000)
    (hreq : maxReq ≤ 4200000)
    (hgrp : (grpS + FineScale - 1) / FineScale ≤ 50000)
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {fullLog : List AllocEvent} (hEnv : Env fullLog) :
    FitsTrace fineCostModel lim (fineStepReserveOfGroups 4200000 16 50000) fullLog := by
  have hram : cliDecoupledRamNeed lim.staticBytes 760000000 60000000 4200000 50000 ≤ lim.physCap :=
    Nat.le_trans
      (cliDecoupledRamNeed_mono hsb (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans cliDecoupledRamNeed_le_oneGiB_of_S4 hcap)
  have hva : cliDecoupledVaNeed lim.staticBytes lim.staticCount
      760000000 60000000 4200000 50000 ≤ 2 ^ 48 :=
    Nat.le_trans
      (cliDecoupledVaNeed_mono hsb hsc (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      cliDecoupledVaNeed_le_2_48_of_S4
  exact fitsTrace_fineCostModel_of_group_literal_bounds
    hSpec hGrp hcum hlive hpeak hreq hgrp henf hram hva hEnv

/-- `1 GiB` decoupled-group `FitsEnv fineCostModel` bound at `fineCostModel.init`. -/
theorem fitsEnv_oneGiB_of_group_bounds_S4
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {cumB liveB peakB maxReq grpS : Nat}
    (hSpec : PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq)
    (hGrp : PhaseGroupSpec fineCostModel Env grpS)
    (hcum : cumB ≤ 760000000)
    (hlive : liveB ≤ 60000000)
    (hpeak : peakB ≤ 60000000)
    (hreq : maxReq ≤ 4200000)
    (hgrp : (grpS + FineScale - 1) / FineScale ≤ 50000)
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap) :
    FitsEnv fineCostModel lim fineCostModel.init Env := by
  have hram : cliDecoupledRamNeed lim.staticBytes 760000000 60000000 4200000 50000 ≤ lim.physCap :=
    Nat.le_trans
      (cliDecoupledRamNeed_mono hsb (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans cliDecoupledRamNeed_le_oneGiB_of_S4 hcap)
  have hva : cliDecoupledVaNeed lim.staticBytes lim.staticCount
      760000000 60000000 4200000 50000 ≤ 2 ^ 48 :=
    Nat.le_trans
      (cliDecoupledVaNeed_mono hsb hsc (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      cliDecoupledVaNeed_le_2_48_of_S4
  exact fitsEnv_fineCostModel_of_group_literal_bounds
    hSpec hGrp hcum hlive hpeak hreq hgrp henf hram hva

/-- Non-vacuity 6-phase trace witness for `CliMainSixPhaseEnv` under `cliBudgetLimits` (`1 GiB`),
exercising `stdin` + session load, temporary `sc = 63` encryption/writeback buffers, and `LineWriter`. -/
def CliMainWitnessEnv : List AllocEvent → Prop :=
  CliMainSixPhaseEnv
    (· = rustAllocEvents 48 8)
    (· = rustAllocEvents 64 8)
    (ConcatEnv (· = rustAllocEvents msgCapBytes 1) (· = rustAllocEvents sessionCapBytes 1))
    (ConcatEnv (· = rustAllocEvents sessionCapBytes 1) (· = rustDeallocEvents sessionCapBytes 1))
    (ConcatEnv (· = rustAllocEvents 512 1) (· = rustDeallocEvents 512 1))
    (· = rustAllocEvents 1024 1)

theorem cliMainWitnessEnv_inhabited :
    ∃ evs : List AllocEvent, CliMainWitnessEnv evs ∧ evs.length = 9 := by
  refine ⟨rustAllocEvents 48 8 ++
      (rustAllocEvents 64 8 ++
        (rustAllocEvents msgCapBytes 1 ++ rustAllocEvents sessionCapBytes 1)) ++
      (rustAllocEvents sessionCapBytes 1 ++ rustDeallocEvents sessionCapBytes 1 ++
        ((rustAllocEvents 512 1 ++ rustDeallocEvents 512 1) ++ rustAllocEvents 1024 1)),
    ?_, ?_⟩
  · unfold CliMainWitnessEnv CliMainSixPhaseEnv
    exact SeqEnv.append
      (SeqEnv.append rfl (SeqEnv.append rfl (ConcatEnv.append rfl rfl)))
      (Or.inr (SeqEnv.append (ConcatEnv.append rfl rfl)
        (SeqEnv.append (ConcatEnv.append rfl rfl) rfl)))
  · decide

theorem cliMainWitnessEnv_fitsEnv :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init CliMainWitnessEnv := by
  have hM := fineCostModel_modelHyps
  have h1 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 48 8)
      (2 * 48 + 9539) (48 + 8195) (48 + 8195) 48 :=
    PhaseCreditSpec.rustAlloc_aff hM (by decide)
  have h2 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 64 8)
      (2 * 64 + 9539) (64 + 8195) (64 + 8195) 64 :=
    PhaseCreditSpec.rustAlloc_aff hM (by decide)
  have h3a : PhaseCreditSpec fineCostModel (· = rustAllocEvents msgCapBytes 1)
      (2 * msgCapBytes + 9539) (msgCapBytes + 8195) (msgCapBytes + 8195) msgCapBytes :=
    PhaseCreditSpec.rustAlloc_aff hM (by decide)
  have h3b : PhaseCreditSpec fineCostModel (· = rustAllocEvents sessionCapBytes 1)
      (2 * sessionCapBytes + 9539) (sessionCapBytes + 8195) (sessionCapBytes + 8195) sessionCapBytes :=
    PhaseCreditSpec.rustAlloc_aff hM (by decide)
  have h3 := h3a.concat h3b
  have hgt2m : HasFineReallocCredit.smallMaxReq fineCostModel < sessionCapBytes := by
    rw [fineCostModel_smallMaxReq_eq, sessionCapBytes_val]
    decide
  have h4_raw := PhaseCreditSpec.largeAllocFree_cancel fineCostModel
    (req := sessionCapBytes) (al := 1) (by decide) hgt2m
  have h4 : PhaseCreditSpec fineCostModel
      (ConcatEnv (· = rustAllocEvents sessionCapBytes 1) (· = rustDeallocEvents sessionCapBytes 1))
      122 0 (sessionCapBytes + 8195) sessionCapBytes := by
    refine h4_raw.mono ?_ (Nat.le_refl 0) ?_ (Nat.le_refl _)
    · rw [fineCostModel_largeMetaCost_eq]
    · rw [fineCostModel_largeCost_eq]
  have h5 := PhaseCreditSpec.tempAllocFree_aff hM (req := 512) (al := 1) (by decide)
  have h6 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 1024 1)
      (2 * 1024 + 9539) (1024 + 8195) (1024 + 8195) 1024 :=
    PhaseCreditSpec.rustAlloc_aff hM (by decide)
  let B : CliMainPhaseBounds :=
    { c1 := 2 * 48 + 9539, l1 := 48 + 8195, p1 := 48 + 8195, r1 := 48
      c2 := 2 * 64 + 9539, l2 := 64 + 8195, p2 := 64 + 8195, r2 := 64
      c3 := (2 * msgCapBytes + 9539) + (2 * sessionCapBytes + 9539)
      l3 := (msgCapBytes + 8195) + (sessionCapBytes + 8195)
      p3 := max (msgCapBytes + 8195) ((msgCapBytes + 8195) + (sessionCapBytes + 8195))
      r3 := max msgCapBytes sessionCapBytes
      c4 := 122, l4 := 0, p4 := sessionCapBytes + 8195, r4 := sessionCapBytes
      c5 := 2 * 512 + 9539, l5 := 0, p5 := 512 + 8195, r5 := 512
      c6 := 2 * 1024 + 9539, l6 := 1024 + 8195, p6 := 1024 + 8195, r6 := 1024 }
  have hAll := cliMainSixPhase_phaseCredit hM B h1 h2 h3 h4 h5 h6
  exact fitsEnv_oneGiB_of_phaseCredit_34M hAll
    (by decide) (by decide) (by decide) (by decide)
    rfl (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

theorem cliMainWitnessEnv_fitsEnv_groups :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init CliMainWitnessEnv := by
  have hM := fineCostModel_modelHyps
  have h1 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 48 8)
      (2 * 48 + 9539) (48 + 8195) (48 + 8195) 48 :=
    PhaseCreditSpec.rustAlloc_aff hM (by decide)
  have h2 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 64 8)
      (2 * 64 + 9539) (64 + 8195) (64 + 8195) 64 :=
    PhaseCreditSpec.rustAlloc_aff hM (by decide)
  have h3a : PhaseCreditSpec fineCostModel (· = rustAllocEvents msgCapBytes 1)
      (2 * msgCapBytes + 9539) (msgCapBytes + 8195) (msgCapBytes + 8195) msgCapBytes :=
    PhaseCreditSpec.rustAlloc_aff hM (by decide)
  have h3b : PhaseCreditSpec fineCostModel (· = rustAllocEvents sessionCapBytes 1)
      (2 * sessionCapBytes + 9539) (sessionCapBytes + 8195) (sessionCapBytes + 8195) sessionCapBytes :=
    PhaseCreditSpec.rustAlloc_aff hM (by decide)
  have h3 := h3a.concat h3b
  have hgt2m : HasFineReallocCredit.smallMaxReq fineCostModel < sessionCapBytes := by
    rw [fineCostModel_smallMaxReq_eq, sessionCapBytes_val]
    decide
  have h4_raw := PhaseCreditSpec.largeAllocFree_cancel fineCostModel
    (req := sessionCapBytes) (al := 1) (by decide) hgt2m
  have h4 : PhaseCreditSpec fineCostModel
      (ConcatEnv (· = rustAllocEvents sessionCapBytes 1) (· = rustDeallocEvents sessionCapBytes 1))
      122 0 (sessionCapBytes + 8195) sessionCapBytes := by
    refine h4_raw.mono ?_ (Nat.le_refl 0) ?_ (Nat.le_refl _)
    · rw [fineCostModel_largeMetaCost_eq]
    · rw [fineCostModel_largeCost_eq]
  have h5 := PhaseCreditSpec.tempAllocFree_aff hM (req := 512) (al := 1) (by decide)
  have h6 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 1024 1)
      (2 * 1024 + 9539) (1024 + 8195) (1024 + 8195) 1024 :=
    PhaseCreditSpec.rustAlloc_aff hM (by decide)
  have hg1 := PhaseGroupSpec.rustAlloc_any fineCostModel 48 8
  have hg2 := PhaseGroupSpec.rustAlloc_any fineCostModel 64 8
  have hg3 := (PhaseGroupSpec.rustAlloc_any fineCostModel msgCapBytes 1).concat
    (PhaseGroupSpec.rustAlloc_any fineCostModel sessionCapBytes 1)
  have hg4 := (PhaseGroupSpec.rustAlloc_any fineCostModel sessionCapBytes 1).concat
    (PhaseGroupSpec.rustDealloc fineCostModel sessionCapBytes 1)
  have hg5 := (PhaseGroupSpec.rustAlloc_any fineCostModel 512 1).concat
    (PhaseGroupSpec.rustDealloc fineCostModel 512 1)
  have hg6 := PhaseGroupSpec.rustAlloc_any fineCostModel 1024 1
  let B : CliMainPhaseBounds :=
    { c1 := 2 * 48 + 9539, l1 := 48 + 8195, p1 := 48 + 8195, r1 := 48
      c2 := 2 * 64 + 9539, l2 := 64 + 8195, p2 := 64 + 8195, r2 := 64
      c3 := (2 * msgCapBytes + 9539) + (2 * sessionCapBytes + 9539)
      l3 := (msgCapBytes + 8195) + (sessionCapBytes + 8195)
      p3 := max (msgCapBytes + 8195) ((msgCapBytes + 8195) + (sessionCapBytes + 8195))
      r3 := max msgCapBytes sessionCapBytes
      c4 := 122, l4 := 0, p4 := sessionCapBytes + 8195, r4 := sessionCapBytes
      c5 := 2 * 512 + 9539, l5 := 0, p5 := 512 + 8195, r5 := 512
      c6 := 2 * 1024 + 9539, l6 := 1024 + 8195, p6 := 1024 + 8195, r6 := 1024 }
  let G : CliMainGroupBounds :=
    { g1 := 3 * FineScale
      g2 := 3 * FineScale
      g3 := 3 * FineScale + 3 * FineScale
      g4 := 3 * FineScale + 0
      g5 := 3 * FineScale + 0
      g6 := 3 * FineScale }
  exact cliMain_fitsEnv_fineCostModel_groups_interface
    B G h1 h2 h3 h4 h5 h6 hg1 hg2 hg3 hg4 hg5 hg6
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    cliDecoupledRamNeed_le_oneGiB_of_S4 cliDecoupledVaNeed_le_2_48_of_S4

end LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
