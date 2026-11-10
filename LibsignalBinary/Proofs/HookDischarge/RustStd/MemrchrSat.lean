/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.RustStd.Memrchr -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.SpecBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.IfaceBudgetLemmas -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import ProofLib.SepLogic.WP.StepsProcess

/-!
# `MainHops.memrchrSpec` & `HookSat` Real-Bytes Bridges (`MemrchrSat`)

Bridges `CliExt.memrchrSpec` / `Memrchr.cliMemrchrSpec hookStack` (targeted by
`HookDischarge.RustStd.Memrchr`) to `Cli.MainHops.memrchrSpec hookStack` (consumed by
`AddressA1PlacedSat`, `AddressA1PlacedBudgetSat`, `SkeletonPlacedSat`,
`MainEntryBudgetFitsInstSat`, `CliNoOomOfFitsEnvSat`, and `ElfSlicesPqOomH2KMainEntryFitsSat`),
at `SpecSimulates`, `subroutine_ok`, and `HookSat` levels (both plain and `withVmPreserved`),
plus the placement-generic real-bytes `coreMultiLib` block-`2` discharge
`coreMemrchr_placed_mainHops_memrchrSpec_ok` (`16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64`).

Honesty notes:
- `memrchrSpecRO`: no real-bytes `coreMultiLib` proof over read-only slice ownership `↦ᵣ`
  (`CalleesRO.memrchrSpecRO`) exists yet in `VerifiedLibraries.RustStd`.
- Real-bytes `withVmPreserved` lift: deferred (`coreMemrchr_ok` wraps all `coreMultiLib` blocks
  in `withCodeLoaded` and `ExecSegSym.sepWP_seg_rebase_pure` tracks `NonSyscallPreserved` without
  `tpidrEl0`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.RustStd.MemrchrSat

open Arm64 ProofLib
open Arm64.Obj (MultiPlacement MultiPlacedLib)
open VerifiedLibraries.RustStd (coreMultiLib coreMemrchrSym coreMemrchrSpec coreMemrchr_ok)
open CryptoVerification (LibsignalHooks)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession (lsMemrchrSym)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Memrchr
  (cliMemrchrSpec coreMemrchr_placed_cliMemrchrSpec_ok)

/-! ## 1. `CliExt` ↔ `Cli.MainHops` `memrchrSpec` Equivalence Bridges -/

/-- `CliExt.memrchrIdx` and `Cli.MainHops.memrchrIdx` are definitionally equal. -/
theorem cliExt_memrchrIdx_eq_mainHops (c : BitVec 8) (bs : List (BitVec 8)) :
    CryptoVerification.SignalSession.CliExt.memrchrIdx c bs =
      CryptoVerification.SignalSession.Cli.MainHops.memrchrIdx c bs :=
  rfl

/-- Forward simulation `cliMemrchrSpec hookStack → MainHops.memrchrSpec hookStack`. -/
theorem cliMemrchrSpec_simulates_mainHops (hookStack : Nat) :
    SpecSimulates (cliMemrchrSpec hookStack)
      (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec hookStack) :=
  SpecSimulates.of_map fun x R _s0 hpre =>
    ⟨⟨x.c, x.p, x.bs⟩, R, hpre, fun _sf _hret _hcc hpost => hpost⟩

/-- Backward simulation `MainHops.memrchrSpec hookStack → cliMemrchrSpec hookStack`. -/
theorem mainHops_simulates_cliMemrchrSpec (hookStack : Nat) :
    SpecSimulates (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec hookStack)
      (cliMemrchrSpec hookStack) :=
  SpecSimulates.of_map fun x R _s0 hpre =>
    ⟨⟨x.c, x.p, x.bs⟩, R, hpre, fun _sf _hret _hcc hpost => hpost⟩

/-- Forward simulation under `withVmPreserved`:
    `withVmPreserved (cliMemrchrSpec hookStack) → withVmPreserved (MainHops.memrchrSpec hookStack)`. -/
theorem cliMemrchrSpec_withVmPreserved_simulates_mainHops (hookStack : Nat) :
    SpecSimulates (withVmPreserved (cliMemrchrSpec hookStack))
      (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec hookStack)) :=
  SpecSimulates.of_map fun x R _s0 hpre =>
    ⟨⟨x.c, x.p, x.bs⟩, R, hpre, fun _sf _hret _hcc hpost => hpost⟩

/-- Backward simulation under `withVmPreserved`:
    `withVmPreserved (MainHops.memrchrSpec hookStack) → withVmPreserved (cliMemrchrSpec hookStack)`. -/
theorem mainHops_withVmPreserved_simulates_cliMemrchrSpec (hookStack : Nat) :
    SpecSimulates
      (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec hookStack))
      (withVmPreserved (cliMemrchrSpec hookStack)) :=
  SpecSimulates.of_map fun x R _s0 hpre =>
    ⟨⟨x.c, x.p, x.bs⟩, R, hpre, fun _sf _hret _hcc hpost => hpost⟩

private theorem specSimulates_hookSat {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) {H : LibsignalHooks} {sym : String}
    (h : HookSat H sym spec₁) : HookSat H sym spec₂ := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun y R s0 hrun hpre hsp => ?_⟩
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre
  obtain ⟨hkf, hsym, hout⟩ := hok x R₁ s0 hrun hpre₁ hsp
  exact ⟨hkf, hsym, hm (f s0) hout⟩

/-- `HookSat` transport from `CliExt.memrchrSpec` to `MainHops.memrchrSpec extHookStack`. -/
theorem hookSat_mainHops_of_cliExt {H : LibsignalHooks}
    (h : HookSat H lsMemrchrSym CryptoVerification.SignalSession.CliExt.memrchrSpec) :
    HookSat H lsMemrchrSym
      (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec extHookStack) :=
  specSimulates_hookSat (cliMemrchrSpec_simulates_mainHops extHookStack) h

/-- `HookSat` transport under `withVmPreserved` from `CliExt.memrchrSpec` to
    `MainHops.memrchrSpec extHookStack`. -/
theorem hookSat_withVmPreserved_mainHops_of_cliExt {H : LibsignalHooks}
    (h : HookSat H lsMemrchrSym
      (withVmPreserved CryptoVerification.SignalSession.CliExt.memrchrSpec)) :
    HookSat H lsMemrchrSym
      (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec extHookStack)) :=
  specSimulates_hookSat (cliMemrchrSpec_withVmPreserved_simulates_mainHops extHookStack) h

/-- Placement-generic real-code discharge for `MainHops.memrchrSpec hookStack` (`16 ≤ hookStack`). -/
theorem coreMemrchr_placed_mainHops_memrchrSpec_ok {mpl : MultiPlacement}
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ pc, P.externAt? pc = none)
    {hookStack : Nat} (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreMemrchrSym)
      (coreMultiLib.withCodeLoaded mpl
        (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec hookStack)) :=
  ((cliMemrchrSpec_simulates_mainHops hookStack).withCodeLoaded coreMultiLib mpl).subroutine_ok
    (coreMemrchr_placed_cliMemrchrSpec_ok hpl hext hstk)

end LibsignalBinary.Proofs.HookDischarge.RustStd.MemrchrSat
