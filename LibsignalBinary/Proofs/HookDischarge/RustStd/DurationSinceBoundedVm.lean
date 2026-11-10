/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.Wave1.TimeDurationSince
public import ProofLib.Placed.OpcodeExclusion
public import LibsignalBinary.Proofs.HookDischarge.RustStd.TimeDurationSince -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.DurationSinceVm -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.Bridge -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.ObjectLoad

/-!
# Bounded-Path `VmPreserved` & Explicit `.rodata` Real-Code Bridges for `<std::time::SystemTime>::duration_since`

Real-bytes de-hook bridges (D2) for `<std::time::SystemTime>::duration_since`
(`VerifiedLibraries.RustStd.timeMultiLib`, `rustc 1.98.1` `aarch64-unknown-linux-musl` `libstd`
prebuilt bytes pinned in the engine) against every bounded consumer contract
(`durationSinceBoundedAtSpec`, `durationSinceBoundedSpec`, `durationSinceBoundedBudgetAtSpec`,
`durationSinceBoundedBudgetSpec`, plus `allocHookStack`, `keepsFs`, separating `withRoDataSep`,
`withRoOk`, and fixed-`Obj.Image` `.inImage` variants).

## Honest Premise Audit vs. Consumer Specs (`durationSinceBounded{,Budget}Spec`)

- **Extra `.rodata` premise (`TimeRodataCst16Ok mpl` / `withRoData` / `withRoOk`)**:
  When `self < earlier` (`t1 < t2`, reachable under clock skew), `SystemTime::duration_since`
  invokes `Timespec::sub_timespec`, which executes a 16-byte SIMD `LDR q0` from
  `mpl.ρ timeRodataCst16Sym` (`"rust_time:.rodata.cst16+0x0"`) expecting the constant
  `timePlacedData0 = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]` (`1#64` in lanes `0..7`,
  `0#64` in lanes `8..15`, used to flip the `Result` tag via `EOR`).
  The consumer contracts `durationSinceBoundedSpec` (body-identical / defeq to
  `Slots.durationSinceBoundedSpec` and `MessageEncrypt.PlacedDefs.durationSinceBoundedSpec`) and
  `durationSinceBoundedBudgetSpec` (`= withVmPreserved durationSinceBoundedSpec`, body-identical /
  defeq to `MessageEncrypt.PlacedDefsBudgetAux.durationSinceBoundedBudgetSpec`,
  `SegFromPlacedBudget.TempTwins.durationSinceBoundedBudgetSpec`, and
  `CliHookSatPlacedBudget`'s `withVmPreserved durationSinceBoundedSpec`) omit this 16-byte
  `.rodata` constant from `pre`.
- **How the extra premise is carried and discharged**:
  Every bounded real-code theorem below wraps the consumer contract in
  `withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0` (definitionally
  `withRoOk (TimeRodataCst16Ok mpl)`), adjoining the pure entry predicate
  `⌜RoDataAt s0.mem (mpl.ρ timeRodataCst16Sym) timePlacedData0⌝` (`m.RO addr 16 ∧ m.readBytes addr 16 = timePlacedData0`).
  On today's `translation.toml`, `rust_time:.rodata.cst16+0x0` is not yet in
  `libsignalSessionLib.data` (pending STOCK-PLAN's `std` root). At ghost dispatch (`ActiveRealRun` /
  `InvS`), `TimeRodataCst16Ok mpl m` is discharged once from `fromLoad` + `KeepsFrozen` via
  `timeRodataCst16Ok_of_holdsBytes_keepsFrozen` (or via `roDataAt_of_libsignalRoLoaded_lsroCheck`
  once placed in `libsignalSessionLib.data`), without threading `.rodata` hypotheses through
  downstream `MessageEncrypt` callers.
- **Stack requirement**: `208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64` (`80` B in `duration_since` +
  `64` B in `sub_timespec` + `64` B in its recursive call on `self < earlier`), satisfied by both
  `allocHookStack = 4096` and `extHookStack = 16384`.
- **Externs & layout-genericity**: all 3 `timeMultiLib` blocks share only the hooked panic-tail
  extern `core::option::expect_failed` (`sub_timespec+236`, unreachable for `tv_nsec < 10 ^ 9`),
  placed outside every block's code range by `Placeable.externs_ok`; theorems hold at arbitrary
  `MultiPlacement` (`timeMultiLib.Placeable mpl`) and any external hook table `externs`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.RustStd.DurationSinceBoundedVm

open Arm64 ProofLib
open Arm64.Obj (HoldsBytes Image MultiPlacement)
open VerifiedLibraries.RustStd
  (timeDurationSinceSpec timeDurationSinceSym timeMultiLib timePlacedData0 timeRodataCst16Sym)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Proofs.Placed.Bridge (LibsignalRoLoaded lsroCheck lsro_read_chk)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common
  (RoDataAt SpecSimulates keepsFs_withRoData withRoData withRoDataSep)
open LibsignalBinary.Proofs.HookDischarge.RustStd.TimeDurationSince
  (durationSinceBoundedAtSpec durationSinceBoundedSpec timeDurationSince_boundedSpec_subroutineOk)
open LibsignalBinary.Proofs.HookDischarge.RustStd.DurationSinceVm
  (specSimulates_keepsFs_withVmPreserved specSimulates_lift_withVmPreserved
   timeDurationSince_vm_subroutineOk)

/-! ## 1. `withRoOk`, Consumer Budget Abbreviations, and `.rodata` Discharge Lemmas -/

/-- Adjoin an abstract pure read-only memory invariant `⌜RoOk s0.mem⌝` to `spec.pre`
    (generalizes `withRoData` to arbitrary frozen-memory predicates). -/
@[expose] def withRoOk {α : Type} (RoOk : Memory → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => ⌜RoOk s0.mem⌝ ∗ spec.pre x s0 }

/-- Placement-indexed 16-byte `.rodata.cst16` invariant required by `SystemTime::duration_since` on
    the `self < earlier` branch (`mpl.ρ "rust_time:.rodata.cst16+0x0"` holds `timePlacedData0` with
    `Perm.ro` and `isLazyFree = false`). -/
@[expose] def TimeRodataCst16Ok (mpl : MultiPlacement) (m : Memory) : Prop :=
  RoDataAt m (mpl.ρ timeRodataCst16Sym) timePlacedData0

/-- Stack-parameterized `VmPreserved` bounded `duration_since` contract (`0` allocations). -/
@[expose] def durationSinceBoundedBudgetAtSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64) :=
  withVmPreserved (durationSinceBoundedAtSpec hookStack)

/-- Mirror of `MessageEncrypt.PlacedDefsBudgetAux.durationSinceBoundedBudgetSpec`,
    `SegFromPlacedBudget.TempTwins.durationSinceBoundedBudgetSpec`, and
    `CliHookSatPlacedBudget`'s `withVmPreserved durationSinceBoundedSpec` (`rfl`-identical at
    `hookStack = extHookStack = 16384`). -/
abbrev durationSinceBoundedBudgetSpec : Spec (BitVec 64 × BitVec 64) :=
  durationSinceBoundedBudgetAtSpec extHookStack

/-- Bounded `duration_since` contract at `allocHookStack = 4096`. -/
abbrev durationSinceBoundedAllocSpec : Spec (BitVec 64 × BitVec 64) :=
  durationSinceBoundedAtSpec allocHookStack

/-- `VmPreserved` bounded `duration_since` contract at `allocHookStack = 4096`. -/
abbrev durationSinceBoundedAllocBudgetSpec : Spec (BitVec 64 × BitVec 64) :=
  durationSinceBoundedBudgetAtSpec allocHookStack

/-- `withRoData addr bytes spec` is definitionally `withRoOk (fun m => RoDataAt m addr bytes) spec`. -/
theorem withRoData_eq_withRoOk {α : Type} (addr : BitVec 64) (bytes : List (BitVec 8))
    (spec : Spec α) :
    withRoData addr bytes spec = withRoOk (fun m => RoDataAt m addr bytes) spec := rfl

/-- `withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0 spec` is definitionally
    `withRoOk (TimeRodataCst16Ok mpl) spec`. -/
theorem withRoData_cst16_eq_withRoOk {α : Type} (mpl : MultiPlacement) (spec : Spec α) :
    withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0 spec =
      withRoOk (TimeRodataCst16Ok mpl) spec := rfl

/-- `keepsFs` commutes with `withRoOk` by `rfl`. -/
theorem keepsFs_withRoOk {α : Type} (RoOk : Memory → Prop) (spec : Spec α) :
    keepsFs (withRoOk RoOk spec) = withRoOk RoOk (keepsFs spec) := rfl

/-- `withVmPreserved` commutes with `withRoOk` by `rfl`. -/
theorem withVmPreserved_withRoOk {α : Type} (RoOk : Memory → Prop) (spec : Spec α) :
    withVmPreserved (withRoOk RoOk spec) = withRoOk RoOk (withVmPreserved spec) := rfl

/-- `withVmPreserved` commutes with `withRoData` by `rfl`. -/
theorem withVmPreserved_withRoData {α : Type} (addr : BitVec 64) (bytes : List (BitVec 8))
    (spec : Spec α) :
    withVmPreserved (withRoData addr bytes spec) = withRoData addr bytes (withVmPreserved spec) :=
  rfl

/-- Contravariant monotonicity of `withRoOk` in the memory predicate `RoOk`. -/
theorem specSimulates_withRoOk_mono {α : Type} {RoOk₁ RoOk₂ : Memory → Prop} {spec : Spec α}
    (himp : ∀ m, RoOk₂ m → RoOk₁ m) :
    SpecSimulates (withRoOk RoOk₁ spec) (withRoOk RoOk₂ spec) := by
  intro x R s0 hpre
  dsimp only [withRoOk] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine ⟨x, R, ?_, fun _ hout => hout⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨himp s0.mem hpre.1, hpre.2⟩

/-- Lift `SpecSimulates spec₁ spec₂` across `withRoOk RoOk`. -/
theorem specSimulates_withRoOk_map {α β : Type} (RoOk : Memory → Prop)
    {spec₁ : Spec α} {spec₂ : Spec β} (hsim : SpecSimulates spec₁ spec₂) :
    SpecSimulates (withRoOk RoOk spec₁) (withRoOk RoOk spec₂) := by
  intro y R s0 hpre
  dsimp only [withRoOk] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hro, hpre₂⟩ := hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre₂
  refine ⟨x, R₁, ?_, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hro, hpre₁⟩

/-- Any proof of `spec` also satisfies `withRoOk RoOk spec` (weakening the precondition). -/
theorem specSimulates_withRoOk_of_spec {α : Type} (RoOk : Memory → Prop) (spec : Spec α) :
    SpecSimulates spec (withRoOk RoOk spec) := by
  intro x R s0 hpre
  dsimp only [withRoOk] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact ⟨x, R, hpre.2, fun _ hout => hout⟩

/-- Discharge `RoDataAt` directly from `Obj.HoldsBytes m addr bytes (fun _ => Perm.ro)`. -/
theorem roDataAt_of_holdsBytes_ro {m : Memory} {addr : BitVec 64} {bytes : List (BitVec 8)}
    (h : HoldsBytes m addr bytes (fun _ => Perm.ro)) :
    RoDataAt m addr bytes :=
  ProofLib.ObjectLoad.holdsBytes_ro h

/-- Discharge `RoDataAt` at runtime state `m` from load-time `Obj.HoldsBytes m₀ addr bytes (fun _ => Perm.ro)`
    and `m₀.KeepsFrozen m` (`fromLoad` + `KeepsFrozen` ghost-dispatch bridge). -/
theorem roDataAt_of_holdsBytes_ro_keepsFrozen {m₀ m : Memory} {addr : BitVec 64}
    {bytes : List (BitVec 8)}
    (h : HoldsBytes m₀ addr bytes (fun _ => Perm.ro)) (hkf : m₀.KeepsFrozen m) :
    RoDataAt m addr bytes :=
  ProofLib.ObjectLoad.holdsBytes_ro (ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen h hkf)

/-- `RoDataAt` is preserved across `Memory.KeepsFrozen` transitions whenever `bytes.length ≤ 2 ^ 64`. -/
theorem roDataAt_of_keepsFrozen {m₀ m : Memory} {addr : BitVec 64} {bytes : List (BitVec 8)}
    (hro : RoDataAt m₀ addr bytes) (hkf : m₀.KeepsFrozen m)
    (hlen : bytes.length ≤ 2 ^ 64 := by decide) :
    RoDataAt m addr bytes := by
  rcases hro with ⟨hperm0, hread0⟩
  have hhb0 : HoldsBytes m₀ addr bytes (fun _ => Perm.ro) := by
    intro k hk
    have hin : InRegion addr bytes.length (addr + BitVec.ofNat 64 k) := by
      unfold InRegion
      have hsub : (addr + BitVec.ofNat 64 k) - addr = BitVec.ofNat 64 k := by bv_omega
      rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hk
    have hp := hperm0 (addr + BitVec.ofNat 64 k) hin
    have hb : m₀.read8 (addr + BitVec.ofNat 64 k) = bytes[k] := by
      have hget := ProofLib.ObjectLoad.readBytes_getElem? m₀ addr bytes.length k hk
      rw [hread0, List.getElem?_eq_getElem hk] at hget
      exact Option.some.inj hget.symm
    exact ⟨hb, hp.1, hp.2⟩
  exact roDataAt_of_holdsBytes_ro_keepsFrozen hhb0 hkf

/-- Ghost-dispatch helper: load-time `HoldsBytes` of `timePlacedData0` at
    `mpl.ρ timeRodataCst16Sym` plus `m₀.KeepsFrozen m` yields `TimeRodataCst16Ok mpl m`. -/
theorem timeRodataCst16Ok_of_holdsBytes_keepsFrozen {mpl : MultiPlacement} {m₀ m : Memory}
    (h : HoldsBytes m₀ (mpl.ρ timeRodataCst16Sym) timePlacedData0 (fun _ => Perm.ro))
    (hkf : m₀.KeepsFrozen m) :
    TimeRodataCst16Ok mpl m :=
  roDataAt_of_holdsBytes_ro_keepsFrozen h hkf

/-- Placed-library helper: once `sym` is present in `libsignalSessionLib.data` (`lsroCheck sym bytes`),
    `LibsignalRoLoaded pl m` (and hence `LibsignalCodeRoLoaded pl m`) discharges `RoDataAt`. -/
theorem roDataAt_of_libsignalRoLoaded_lsroCheck {pl : MultiPlacement} {m : Memory}
    (hro : LibsignalRoLoaded pl m) {sym : String} {bytes : List (BitVec 8)}
    (hchk : lsroCheck sym bytes = true) :
    RoDataAt m (pl.ρ sym) bytes :=
  lsro_read_chk hro hchk

/-! ## 2. Spec-Level Bounded Simulations & `subroutine_ok` Bridges -/

private theorem timePlacedData0_length_le : timePlacedData0.length ≤ 2 ^ 64 := by
  have h : timePlacedData0.length = 16 := rfl
  rw [h]; decide

private theorem systemTime_entails_memRegion16 (p s1 : BitVec 64) (n1 : BitVec 32) :
    ((p ↦₆₄ s1) ∗ ((p + 8#64) ↦₃₂ n1) ∗ memRegion (p + 12#64) 4) ⊢ memRegion p 16 := by
  rw [memRegion_split3_ord p 16 8 4 (by decide) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion p s1)
    (sepConj_mono (pointsTo32_entails_memRegion (p + 8#64) n1) (Entails.refl _))

private theorem sret_entails_memRegion24 (ret w0 w1 : BitVec 64) (r16 b20 : BitVec 32) :
    ((ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₃₂ r16) ∗ ((ret + 20#64) ↦₃₂ b20)) ⊢
      memRegion ret 24 := by
  rw [memRegion_split3_ord ret 24 8 8 (by decide) (by decide),
    memRegion_split (ret + 16#64) 4 4 (by decide)]
  have hoff : (ret + 16#64) + 4#64 = ret + 20#64 := by rw [BitVec.add_assoc]; rfl
  rw [hoff]
  exact sepConj_mono (pointsTo64_entails_memRegion ret w0)
    (sepConj_mono (pointsTo64_entails_memRegion (ret + 8#64) w1)
      (sepConj_mono (pointsTo32_entails_memRegion (ret + 16#64) r16)
        (pointsTo32_entails_memRegion (ret + 20#64) b20)))

/-- Forward simulation from `timeDurationSinceSpec c16` (`208` B stack) to
    `withRoDataSep c16 timePlacedData0 (keepsFs (durationSinceBoundedAtSpec hookStack))` whenever
    `208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64`. -/
theorem timeDurationSince_simulates_bounded_roSep_keepsFs (c16 : BitVec 64)
    {hookStack : Nat} (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    SpecSimulates (timeDurationSinceSpec c16)
      (withRoDataSep c16 timePlacedData0 (keepsFs (durationSinceBoundedAtSpec hookStack))) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨p, ret⟩ R s0 hpre
  dsimp only [withRoDataSep, keepsFs, durationSinceBoundedAtSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (c16 ↦ᵣ timePlacedData0) ⌜_⌝, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8, hn2_raw⟩, hpre⟩ := hpre
  rw [memRegion_split ret 20 4 (by decide), memRegion_four (ret + 20#64),
    stackAt_shrink s0.sp hookStack 208 hstk.1 hstk.2,
    stackAt_eq_stackFrameAt s0.sp 208 (by decide)] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  obtain ⟨b20, tvSec, tvNsec, hpre⟩ := hpre
  simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (c16 ↦ᵣ timePlacedData0) ⌜tvNsec.toNat < 1000000000⌝,
    satisfies_pure_sepConj] at hpre
  obtain ⟨hn1, hpre⟩ := hpre
  let s2 : BitVec 64 := s0.readReg64 .x1
  let n2 : BitVec 32 := (s0.readReg64 .x2).setWidth 32
  have hx2_32 : s0.readReg32 .x2 = n2 := by
    simp [n2, State.readReg32, State.readReg64]
  refine ⟨(p, s2, n2, ret, s0.sp, tvSec, tvNsec, b20),
    memRegion (p + 12#64) 4 ∗ memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - 208) ∗ R,
    ?_, ?_⟩
  · dsimp only [timeDurationSinceSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, rfl, hx2_32, hx8, rfl, hn1, hn2_raw⟩,
      Satisfies.mono (by sep_entail) hpre⟩
  · intro sf _hret _hcc hpost
    dsimp only [timeDurationSinceSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨htr, hfs⟩, hpost⟩ := hpost
    let t1 : Int := tvSec.toInt * 10 ^ 9 + tvNsec.toNat
    let t2 : Int := s2.toInt * 10 ^ 9 + n2.toNat
    let d : Nat := (t1 - t2).natAbs
    let tag : BitVec 64 := if t2 ≤ t1 then 0#64 else 1#64
    have hp16 := systemTime_entails_memRegion16 p tvSec tvNsec
    have hr24 := sret_entails_memRegion24 ret tag
      (BitVec.ofNat 64 (d / 10 ^ 9)) (BitVec.ofNat 32 (d % 10 ^ 9)) b20
    have hreord :
        sf.mem ⊨ ((p ↦₆₄ tvSec) ∗ ((p + 8#64) ↦₃₂ tvNsec) ∗ memRegion (p + 12#64) 4) ∗
          ((ret ↦₆₄ tag) ∗ ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 (d / 10 ^ 9)) ∗
            ((ret + 16#64) ↦₃₂ BitVec.ofNat 32 (d % 10 ^ 9)) ∗ ((ret + 20#64) ↦₃₂ b20)) ∗
          (c16 ↦ᵣ timePlacedData0) ∗
          memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - 208) ∗
          stackFrameAt s0.sp 208 ∗ R :=
      Satisfies.mono (by sep_entail) hpost
    have hfolded := Satisfies.mono
      (sepConj_mono hp16 (sepConj_mono hr24 (Entails.refl _))) hreord
    dsimp only [withRoDataSep, keepsFs, durationSinceBoundedAtSpec]
    rw [stackAt_shrink s0.sp hookStack 208 hstk.1 hstk.2,
      stackAt_eq_stackFrameAt s0.sp 208 (by decide)]
    simp only [sepConj_assoc]
    rw [sepConj_left_comm (c16 ↦ᵣ timePlacedData0) ⌜sf.fs = s0.fs⌝,
      satisfies_pure_sepConj]
    refine ⟨hfs, ?_⟩
    rw [sepConj_left_comm (c16 ↦ᵣ timePlacedData0) ⌜sf.trace = s0.trace⌝, satisfies_pure_sepConj]
    exact ⟨htr, Satisfies.mono (by sep_entail) hfolded⟩

/-- Pure `withRoData` + `withVmPreserved` + `keepsFs` simulation from
    `withVmPreserved (timeDurationSinceSpec c16)` to
    `withRoData c16 timePlacedData0 (keepsFs (durationSinceBoundedBudgetAtSpec hookStack))`. -/
theorem timeDurationSince_simulates_bounded_vm_roData_keepsFs (c16 : BitVec 64)
    {hookStack : Nat} (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    SpecSimulates (withVmPreserved (timeDurationSinceSpec c16))
      (withRoData c16 timePlacedData0 (keepsFs (durationSinceBoundedBudgetAtSpec hookStack))) := by
  have hbase :
      SpecSimulates (timeDurationSinceSpec c16)
        (withRoData c16 timePlacedData0 (keepsFs (durationSinceBoundedAtSpec hookStack))) :=
    (timeDurationSince_simulates_bounded_roSep_keepsFs c16 hstk).trans
      (SpecSimulates.withRoData_of_sep timePlacedData0_length_le)
  have hvm := specSimulates_lift_withVmPreserved hbase
  rw [withVmPreserved_withRoData, withRoData_eq_withRoOk] at hvm
  rw [withRoData_eq_withRoOk]
  exact hvm.trans (specSimulates_withRoOk_map _ specSimulates_keepsFs_withVmPreserved)

/-- Pure `withRoData` + `withVmPreserved` simulation from
    `withVmPreserved (timeDurationSinceSpec c16)` to
    `withRoData c16 timePlacedData0 (durationSinceBoundedBudgetAtSpec hookStack)`. -/
theorem timeDurationSince_simulates_bounded_vm_roData (c16 : BitVec 64)
    {hookStack : Nat} (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    SpecSimulates (withVmPreserved (timeDurationSinceSpec c16))
      (withRoData c16 timePlacedData0 (durationSinceBoundedBudgetAtSpec hookStack)) := by
  have hk := timeDurationSince_simulates_bounded_vm_roData_keepsFs c16 hstk
  rw [withRoData_eq_withRoOk] at hk ⊢
  exact hk.trans (specSimulates_withRoOk_map _ SpecSimulates.drop_keepsFs)

/-- Separating `withRoDataSep` + `withVmPreserved` + `keepsFs` simulation for
    `durationSinceBoundedBudgetAtSpec hookStack`. -/
theorem timeDurationSince_simulates_bounded_vm_roSep_keepsFs (c16 : BitVec 64)
    {hookStack : Nat} (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    SpecSimulates (withVmPreserved (timeDurationSinceSpec c16))
      (keepsFs (withRoDataSep c16 timePlacedData0
        (durationSinceBoundedBudgetAtSpec hookStack))) := by
  have hvm := specSimulates_lift_withVmPreserved
    (timeDurationSince_simulates_bounded_roSep_keepsFs c16 hstk)
  refine hvm.trans ?_
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hout_abn
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, withRoDataSep, keepsFs, durationSinceBoundedBudgetAtSpec] at hpost ⊢
    simp only [sepConj_assoc] at hpost ⊢
    exact Satisfies.mono (by sep_entail) hpost
  · exact Or.inr hout_abn

/-- Spec-level `subroutine_ok` bridge for
    `withRoData c16 timePlacedData0 (keepsFs (durationSinceBoundedBudgetAtSpec hookStack))`. -/
theorem timeDurationSince_boundedBudgetAtSpec_keepsFs_ok {prog : Program} {entry c16 : BitVec 64}
    {hookStack : Nat} (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (withVmPreserved (timeDurationSinceSpec c16))) :
    subroutine_ok prog entry
      (withRoData c16 timePlacedData0 (keepsFs (durationSinceBoundedBudgetAtSpec hookStack))) :=
  (timeDurationSince_simulates_bounded_vm_roData_keepsFs c16 hstk).subroutine_ok h

/-- Spec-level `subroutine_ok` bridge for
    `withRoData c16 timePlacedData0 (durationSinceBoundedBudgetAtSpec hookStack)`. -/
theorem timeDurationSince_boundedBudgetAtSpec_ok {prog : Program} {entry c16 : BitVec 64}
    {hookStack : Nat} (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (withVmPreserved (timeDurationSinceSpec c16))) :
    subroutine_ok prog entry
      (withRoData c16 timePlacedData0 (durationSinceBoundedBudgetAtSpec hookStack)) :=
  (timeDurationSince_simulates_bounded_vm_roData c16 hstk).subroutine_ok h

/-- Spec-level `subroutine_ok` bridge for `withRoData c16 timePlacedData0 durationSinceBoundedBudgetSpec`
    (`hookStack = extHookStack = 16384`). -/
theorem timeDurationSince_boundedBudgetSpec_ok {prog : Program} {entry c16 : BitVec 64}
    (h : subroutine_ok prog entry (withVmPreserved (timeDurationSinceSpec c16))) :
    subroutine_ok prog entry
      (withRoData c16 timePlacedData0 durationSinceBoundedBudgetSpec) :=
  timeDurationSince_boundedBudgetAtSpec_ok (by decide) h

/-! ## 3. Layout-Generic Real-Code `timeMultiLib.subroutineOk` Bridges -/

/-- Real-code `MultiPlacedLib.subroutineOk` for `durationSinceBoundedBudgetAtSpec hookStack`
    (`208 ≤ hookStack ≤ 2 ^ 64`) under explicit `.rodata` premise
    `withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0`, plus `keepsFs`. -/
theorem timeDurationSince_boundedBudgetAtSpec_keepsFs_subroutineOk {hookStack : Nat}
    (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0
        (keepsFs (durationSinceBoundedBudgetAtSpec hookStack)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => timeDurationSince_simulates_bounded_vm_roData_keepsFs (mpl.ρ timeRodataCst16Sym) hstk)
    (timeDurationSince_vm_subroutineOk externs)

/-- Real-code `MultiPlacedLib.subroutineOk` for `durationSinceBoundedBudgetAtSpec hookStack`
    (`208 ≤ hookStack ≤ 2 ^ 64`) under explicit `.rodata` premise
    `withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0`. -/
theorem timeDurationSince_boundedBudgetAtSpec_subroutineOk {hookStack : Nat}
    (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0
        (durationSinceBoundedBudgetAtSpec hookStack))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => timeDurationSince_simulates_bounded_vm_roData (mpl.ρ timeRodataCst16Sym) hstk)
    (timeDurationSince_vm_subroutineOk externs)

/-- Primary bounded budget real-code bridge: `timeMultiLib` satisfies
    `withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0 durationSinceBoundedBudgetSpec`
    (`= withRoOk (TimeRodataCst16Ok mpl) (withVmPreserved durationSinceBoundedSpec)`). -/
theorem timeDurationSince_boundedBudgetSpec_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0
        durationSinceBoundedBudgetSpec)
      externs :=
  timeDurationSince_boundedBudgetAtSpec_subroutineOk (by decide) externs

/-- `keepsFs` variant of `timeDurationSince_boundedBudgetSpec_subroutineOk`
    (`keepsFs (withRoData ...)` = `withRoData ... (keepsFs ...)` by `rfl`). -/
theorem timeDurationSince_boundedBudgetSpec_keepsFs_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => keepsFs (withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0
        durationSinceBoundedBudgetSpec))
      externs := by
  simp only [keepsFs_withRoData]
  exact timeDurationSince_boundedBudgetAtSpec_keepsFs_subroutineOk (by decide) externs

/-- `withRoOk`-parameterized bounded budget real-code bridge: for any placement-indexed
    frozen-memory invariant `RoOk` implying `TimeRodataCst16Ok mpl`, `timeMultiLib` satisfies
    `withRoOk (RoOk mpl) durationSinceBoundedBudgetSpec`. -/
theorem timeDurationSince_boundedBudgetSpec_withRoOk_subroutineOk
    (RoOk : MultiPlacement → Memory → Prop)
    (hro : ∀ mpl m, RoOk mpl m → TimeRodataCst16Ok mpl m)
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => withRoOk (RoOk mpl) durationSinceBoundedBudgetSpec)
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => by
      have h1 := timeDurationSince_simulates_bounded_vm_roData (hookStack := extHookStack)
        (mpl.ρ timeRodataCst16Sym) (by decide)
      rw [withRoData_cst16_eq_withRoOk mpl] at h1
      exact h1.trans (specSimulates_withRoOk_mono (hro mpl)))
    (timeDurationSince_vm_subroutineOk externs)

/-- Non-budget `withRoOk`-parameterized bounded real-code bridge (`durationSinceBoundedSpec`). -/
theorem timeDurationSince_boundedSpec_withRoOk_subroutineOk
    (RoOk : MultiPlacement → Memory → Prop)
    (hro : ∀ mpl m, RoOk mpl m → TimeRodataCst16Ok mpl m)
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => withRoOk (RoOk mpl) durationSinceBoundedSpec)
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => by
      rw [withRoData_cst16_eq_withRoOk mpl]
      exact specSimulates_withRoOk_mono (hro mpl))
    (timeDurationSince_boundedSpec_subroutineOk externs)

/-- Non-budget stack-parameterized bounded real-code bridge (`durationSinceBoundedAtSpec hookStack`,
    `208 ≤ hookStack ≤ 2 ^ 64`) + `keepsFs`. -/
theorem timeDurationSince_boundedAtSpec_keepsFs_subroutineOk {hookStack : Nat}
    (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0
        (keepsFs (durationSinceBoundedAtSpec hookStack)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (timeDurationSince_simulates_bounded_roSep_keepsFs (mpl.ρ timeRodataCst16Sym) hstk).trans
        (SpecSimulates.withRoData_of_sep timePlacedData0_length_le))
    (VerifiedLibraries.RustStd.timeDurationSince_subroutineOk externs)

/-- Non-budget stack-parameterized bounded real-code bridge (`durationSinceBoundedAtSpec hookStack`,
    `208 ≤ hookStack ≤ 2 ^ 64`). -/
theorem timeDurationSince_boundedAtSpec_subroutineOk {hookStack : Nat}
    (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0
        (durationSinceBoundedAtSpec hookStack))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => by
      rw [withRoData_eq_withRoOk]
      exact ((timeDurationSince_simulates_bounded_roSep_keepsFs (mpl.ρ timeRodataCst16Sym) hstk).trans
        (SpecSimulates.withRoData_of_sep timePlacedData0_length_le)).trans
        (by
          rw [withRoData_eq_withRoOk]
          exact specSimulates_withRoOk_map _ SpecSimulates.drop_keepsFs))
    (VerifiedLibraries.RustStd.timeDurationSince_subroutineOk externs)

/-- Bounded budget real-code bridge at `allocHookStack = 4096`. -/
theorem timeDurationSince_boundedAllocBudgetSpec_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0
        durationSinceBoundedAllocBudgetSpec)
      externs :=
  timeDurationSince_boundedBudgetAtSpec_subroutineOk (by decide) externs

/-- Non-budget bounded real-code bridge at `allocHookStack = 4096`. -/
theorem timeDurationSince_boundedAllocSpec_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0
        durationSinceBoundedAllocSpec)
      externs :=
  timeDurationSince_boundedAtSpec_subroutineOk (by decide) externs

/-- Separating `withRoDataSep` + `keepsFs` bounded budget real-code bridge (`208 ≤ hookStack`). -/
theorem timeDurationSince_boundedBudgetAtSpec_roSep_keepsFs_subroutineOk {hookStack : Nat}
    (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => keepsFs (withRoDataSep (mpl.ρ timeRodataCst16Sym) timePlacedData0
        (durationSinceBoundedBudgetAtSpec hookStack)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => timeDurationSince_simulates_bounded_vm_roSep_keepsFs (mpl.ρ timeRodataCst16Sym) hstk)
    (timeDurationSince_vm_subroutineOk externs)

/-- Separating `withRoDataSep` bounded budget real-code bridge (`durationSinceBoundedBudgetSpec`). -/
theorem timeDurationSince_boundedBudgetSpec_roSep_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => withRoDataSep (mpl.ρ timeRodataCst16Sym) timePlacedData0
        durationSinceBoundedBudgetSpec)
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (timeDurationSince_simulates_bounded_vm_roSep_keepsFs (mpl.ρ timeRodataCst16Sym)
        (by decide)).trans SpecSimulates.drop_keepsFs)
    (timeDurationSince_vm_subroutineOk externs)

/-- Any proof of `spec` also satisfies `spec.inImage img` (weakening `pre` with `img.CodeLoaded`). -/
theorem specSimulates_inImage {α : Type} (img : Image) (spec : Spec α) :
    SpecSimulates spec (spec.inImage img) := by
  intro x R s0 hpre
  dsimp only [Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact ⟨x, R, hpre.2, fun _ hout => hout⟩

/-- Real-code `MultiPlacedLib.subroutineOk` for
    `(withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0 durationSinceBoundedBudgetSpec).inImage img`. -/
theorem timeDurationSince_boundedBudgetSpec_inImage_subroutineOk (img : Image)
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => (withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0
        durationSinceBoundedBudgetSpec).inImage img)
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun _ => specSimulates_inImage img _)
    (timeDurationSince_boundedBudgetSpec_subroutineOk externs)

/-- Real-code `MultiPlacedLib.subroutineOk` for
    `(withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0 durationSinceBoundedSpec).inImage img`. -/
theorem timeDurationSince_boundedSpec_inImage_subroutineOk (img : Image)
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => (withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0
        durationSinceBoundedSpec).inImage img)
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun _ => specSimulates_inImage img _)
    (timeDurationSince_boundedSpec_subroutineOk externs)

end LibsignalBinary.Proofs.HookDischarge.RustStd.DurationSinceBoundedVm
