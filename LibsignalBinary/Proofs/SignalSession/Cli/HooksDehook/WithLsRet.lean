/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.SpecBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.IfaceSimp -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees -- proof-setup: allow-public-import

/-!
# `[LibsignalPlacement]`-Generic `withLsRet` Consumer & Master Wrapper (`HooksDehook.WithLsRet`)

Shared `K`-route return-address narrowing wrapper (Card **K1**, `r0_nonleaf_lr.md` §2.6, §4) for
non-leaf `cliHookTablePlaced` rows (`memrchr`, `duration_since`, `SystemTime::add`) whose real bytes
push/pop `lr` and `bl` to hooked panic stubs:

1. **`withLsRet spec`**:
   Conjoins `⌜LsRetAddr624 (s.readReg64 .lr)⌝` (`Placed/ElfLsRetAddr.lean:83`) to `spec.pre`,
   leaving `post`, `onPanic`, `onExit`, and `onOom` definitionally (`rfl`) unchanged.
   *Relation to existing combinators:* `withLsRet spec` uses the identical record-update shape
   `{ spec with pre := fun x s => ⌜P s⌝ ∗ spec.pre x s }` as `FdThreadKit.withPreGuard`
   (`Cli/F3/HRead/FdThreadKit.lean:70`) and `Block617TransferG.withEntryGuard`
   (`Cli/HooksDehook/Block617TransferG.lean:67`), so it is definitionally (`rfl`) equal to both at
   `P := fun s => LsRetAddr624 (s.readReg64 .lr)` (and `FdThreadKit.withLsRetAddr624AndFds spec` is
   `rfl`-equal to `withLsRet (withFdsGe3Closed spec)`), while keeping a lightweight import cone
   usable below `PlacedDefsBudgetAux`, `SkeletonPlacedBudget`, and `ElfSlicesPqOomH2KHooks`.
2. **One-way precondition weakening (`HookOk`, `HookSat`, `subroutine_ok`, `SpecSimulates`)**:
   `hookOk_withLsRet`, `hookSat_withLsRet`, and `subroutine_ok_withLsRet` weaken any unnarrowed
   contract (such as legacy idealized hooks in `cliHookTablePlaced`) to `withLsRet spec`.
3. **`bl`-site discharge helpers from `lsRetAddr624_base_add`**:
   One-line call-site discharge of `LsRetAddr624 (s.readReg64 .lr)` and `(withLsRet spec).pre`
   whenever `s.readReg64 .lr = lsmpl.base j + off` (or `(libsignalSessionLib.blockPlacement lsmpl j).base + off`)
   for `j < 624` and `off.toNat < lsLen j` (discharged automatically via `by decide`).
4. **Wrapper commutations**:
   Definitional (`rfl`) commutations with all post-only wrappers (`withVmPreserved`, `Spec.keepsFs`,
   `HookDischarge.Libc.Common.keepsFs`, `withOomPoolPreserved`, `timeAddBudgetSpec`,
   `durationSinceBudgetSpec`, `durationSinceEpochBudgetSpec`, and generic `withLsRet_withPost`), plus
   exact `Spec` equalities (`=`) with right- and left-framed wrappers (`withLsRet_frameRight`,
   `withLsRet_frameLeft`, `withLsRoCl`, `withLsCodeRoLoaded`, `withLsCodeLoaded`, `withRoData`,
   `withRoDataSep`, `MultiPlacedLib.withCodeLoaded`, `Spec.inImage`, and `withStack`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet

open Arm64 ProofLib
open Arm64.Obj (MultiPlacement MultiPlacedLib)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement libsignalSessionLib lsmpl withLsCodeLoaded
)
open CryptoVerification.LibsignalPublicApi (durationSinceSpec timeAddSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded withLsCodeRoLoaded withLsRoCl
)
open CryptoVerification.SignalSession.CliExt (durationSinceEpochSpec)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved)
open LibsignalBinary.Heap.SpecBudget (
  durationSinceBudgetSpec durationSinceEpochBudgetSpec timeAddBudgetSpec withVmPreserved
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (withStack)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (
  RoDataAt SpecSimulates withRoData withRoDataSep
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (
  LsRetAddr LsRetAddr624 lsLen lsRetAddr624_base_add lsRetAddr624_base_zero
  lsRetAddr624_blockPlacement_base_add lsRetAddr624_blockPlacement_base_zero
  lsRetAddr624_of_lsRetAddr
)

/-! ## 1. `withLsRet` Wrapper & Basic Structural Properties -/

/-- Narrow `spec.pre` with the `[LibsignalPlacement]`-generic caller return-address predicate
    `⌜LsRetAddr624 (s.readReg64 .lr)⌝`, keeping `post`, `onPanic`, `onExit`, and `onOom`
    definitionally (`rfl`) unchanged. -/
@[expose] def withLsRet [LibsignalPlacement] {α : Type} (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜LsRetAddr624 (s.readReg64 .lr)⌝ ∗ spec.pre x s }

theorem withLsRet_pre [LibsignalPlacement] {α : Type} (spec : Spec α) (x : α) (s : State) :
    (withLsRet spec).pre x s = (⌜LsRetAddr624 (s.readReg64 .lr)⌝ ∗ spec.pre x s) := rfl

theorem withLsRet_post [LibsignalPlacement] {α : Type} (spec : Spec α)
    (x : α) (s0 sf : State) :
    (withLsRet spec).post x s0 sf = spec.post x s0 sf := rfl

theorem withLsRet_onPanic [LibsignalPlacement] {α : Type} (spec : Spec α)
    (x : α) (s0 sf : State) :
    (withLsRet spec).onPanic x s0 sf = spec.onPanic x s0 sf := rfl

theorem withLsRet_onExit [LibsignalPlacement] {α : Type} (spec : Spec α)
    (x : α) (code : BitVec 64) (s0 sf : State) :
    (withLsRet spec).onExit x code s0 sf = spec.onExit x code s0 sf := rfl

theorem withLsRet_onOom [LibsignalPlacement] {α : Type} (spec : Spec α)
    (x : α) (s0 sf : State) :
    (withLsRet spec).onOom x s0 sf = spec.onOom x s0 sf := rfl

theorem withLsRet_outcome_eq [LibsignalPlacement] {α : Type} (spec : Spec α)
    (x : α) (R : SepProp) (s0 sf : State) :
    SubroutineOutcome (withLsRet spec) x R s0 sf = SubroutineOutcome spec x R s0 sf := rfl

/-- Extract `LsRetAddr624 (s0.readReg64 .lr)` and `s0.mem ⊨ spec.pre x s0 ∗ R` from
    `s0.mem ⊨ (withLsRet spec).pre x s0 ∗ R`. -/
theorem extract_withLsRet [LibsignalPlacement] {α : Type} {spec : Spec α}
    {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (withLsRet spec).pre x s0 ∗ R) :
    LsRetAddr624 (s0.readReg64 .lr) ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withLsRet] at hpre
  rwa [sepConj_assoc, satisfies_pure_sepConj] at hpre

/-- Introduce `s0.mem ⊨ (withLsRet spec).pre x s0 ∗ R` from `LsRetAddr624 (s0.readReg64 .lr)` and
    `s0.mem ⊨ spec.pre x s0 ∗ R`. -/
theorem intro_withLsRet [LibsignalPlacement] {α : Type} {spec : Spec α}
    {x : α} {s0 : State} {R : SepProp}
    (hlr : LsRetAddr624 (s0.readReg64 .lr))
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsRet spec).pre x s0 ∗ R := by
  dsimp only [withLsRet]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hlr, hpre⟩

/-- `withLsRet` preserves `State.setPC`-invariance of `pre` (since `(s.setPC pc).readReg64 .lr =
    s.readReg64 .lr` definitionally). -/
theorem withLsRet_pre_setPC [LibsignalPlacement] {α : Type} {spec : Spec α}
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (x : α) (s : State) (pc : BitVec 64) :
    (withLsRet spec).pre x (s.setPC pc) = (withLsRet spec).pre x s := by
  dsimp only [withLsRet]
  have hlr : (s.setPC pc).readReg64 .lr = s.readReg64 .lr := rfl
  rw [hlr, hPrePC x s pc]

/-- `withLsRet` preserves `State.setPC`-invariance of `SubroutineOutcome`. -/
theorem withLsRet_outcome_setPC [LibsignalPlacement] {α : Type} {spec : Spec α}
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    (x : α) (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (hout : SubroutineOutcome (withLsRet spec) x R (s0.setPC pc) sf) :
    SubroutineOutcome (withLsRet spec) x R s0 sf :=
  hOutPC x R s0 sf pc hout

/-! ## 2. Precondition Weakening (`HookOk`, `HookSat`, `subroutine_ok`, `SpecSimulates`) -/

/-- Any `HookOk f spec` weakens to `HookOk f (withLsRet spec)` (allowing legacy idealized hooks in
    `cliHookTablePlaced` to satisfy `withLsRet`-narrowed consumer obligations directly). -/
theorem hookOk_withLsRet [LibsignalPlacement] {α : Type} {f : State → State} {spec : Spec α}
    (h : HookOk f spec) :
    HookOk f (withLsRet spec) := by
  intro x R s0 hrun hpre hsp
  exact h x R s0 hrun (extract_withLsRet hpre).2 hsp

/-- Any `HookSat H n spec` weakens to `HookSat H n (withLsRet spec)`. -/
theorem hookSat_withLsRet [LibsignalPlacement] {α : Type}
    {H : String → Option (State → State)} {n : String} {spec : Spec α}
    (h : HookSat H n spec) :
    HookSat H n (withLsRet spec) := by
  rcases h with ⟨f, hfn, hok⟩
  exact ⟨f, hfn, hookOk_withLsRet hok⟩

/-- Any `subroutine_ok prog entry spec` weakens to `subroutine_ok prog entry (withLsRet spec)`. -/
theorem subroutine_ok_withLsRet [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsRet spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => (extract_withLsRet hp).2) (fun _ _ _ _ hq => hq)

/-- Drop `withLsRet` on `HookOk` when `spec.pre` already implies `LsRetAddr624 (s0.readReg64 .lr)`. -/
theorem hookOk_of_withLsRet [LibsignalPlacement] {α : Type} {f : State → State} {spec : Spec α}
    (hlr : ∀ x R s0, (s0.mem ⊨ spec.pre x s0 ∗ R) → LsRetAddr624 (s0.readReg64 .lr))
    (h : HookOk f (withLsRet spec)) :
    HookOk f spec := by
  intro x R s0 hrun hpre hsp
  exact h x R s0 hrun (intro_withLsRet (hlr x R s0 hpre) hpre) hsp

/-- Drop `withLsRet` on `HookSat` when `spec.pre` already implies `LsRetAddr624 (s0.readReg64 .lr)`. -/
theorem hookSat_of_withLsRet [LibsignalPlacement] {α : Type}
    {H : String → Option (State → State)} {n : String} {spec : Spec α}
    (hlr : ∀ x R s0, (s0.mem ⊨ spec.pre x s0 ∗ R) → LsRetAddr624 (s0.readReg64 .lr))
    (h : HookSat H n (withLsRet spec)) :
    HookSat H n spec := by
  rcases h with ⟨f, hfn, hok⟩
  exact ⟨f, hfn, hookOk_of_withLsRet hlr hok⟩

/-- Drop `withLsRet` on `subroutine_ok` when `spec.pre` already implies
    `LsRetAddr624 (s0.readReg64 .lr)`. -/
theorem subroutine_ok_of_withLsRet [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (hlr : ∀ x R s0, (s0.mem ⊨ spec.pre x s0 ∗ R) → LsRetAddr624 (s0.readReg64 .lr))
    (h : subroutine_ok prog entry (withLsRet spec)) :
    subroutine_ok prog entry spec :=
  subroutine_ok_mono h (fun x R s0 hp => intro_withLsRet (hlr x R s0 hp) hp) (fun _ _ _ _ hq => hq)

/-- Lift `SpecSimulates spec₁ spec₂` uniformly to `SpecSimulates (withLsRet spec₁) (withLsRet spec₂)`. -/
theorem specSimulates_withLsRet [LibsignalPlacement] {α β : Type}
    {spec₁ : Spec α} {spec₂ : Spec β} (hsim : SpecSimulates spec₁ spec₂) :
    SpecSimulates (withLsRet spec₁) (withLsRet spec₂) := by
  intro y R s0 hpre
  obtain ⟨hlr, hpre₂⟩ := extract_withLsRet hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre₂
  exact ⟨x, R₁, intro_withLsRet hlr hpre₁, hm⟩

/-! ## 3. `bl`-Site Discharge Helpers (`lsRetAddr624_base_add`) -/

/-- Discharge `LsRetAddr624 (s.readReg64 .lr)` at a `bl` call site whose return address is
    `lsmpl.base j + off` inside `libsignalSessionLib` block `j < 624` (`hj` and `ho` default to
    `by decide` over the depth-10 `lsLen` decision tree). -/
theorem lsRetAddr624_of_lr_eq_base_add [LibsignalPlacement] {s : State}
    (j : Nat) (off : BitVec 64)
    (hlr : s.readReg64 .lr = lsmpl.base j + off)
    (hj : j < 624 := by decide) (ho : off.toNat < lsLen j := by decide) :
    LsRetAddr624 (s.readReg64 .lr) :=
  hlr ▸ lsRetAddr624_base_add j off hj ho

/-- `(libsignalSessionLib.blockPlacement lsmpl j).base + off` variant of
    `lsRetAddr624_of_lr_eq_base_add` (covering `(blkPl_N).base + off` abbreviations). -/
theorem lsRetAddr624_of_lr_eq_blockPlacement_base_add [LibsignalPlacement] {s : State}
    (j : Nat) (off : BitVec 64)
    (hlr : s.readReg64 .lr = (libsignalSessionLib.blockPlacement lsmpl j).base + off)
    (hj : j < 624 := by decide) (ho : off.toNat < lsLen j := by decide) :
    LsRetAddr624 (s.readReg64 .lr) :=
  hlr ▸ lsRetAddr624_blockPlacement_base_add j off hj ho

/-- Zero-offset `lsmpl.base j` variant of `lsRetAddr624_of_lr_eq_base_add`. -/
theorem lsRetAddr624_of_lr_eq_base_zero [LibsignalPlacement] {s : State}
    (j : Nat) (hlr : s.readReg64 .lr = lsmpl.base j)
    (hj : j < 624 := by decide) (ho : 0 < lsLen j := by decide) :
    LsRetAddr624 (s.readReg64 .lr) :=
  hlr ▸ lsRetAddr624_base_zero j hj ho

/-- Zero-offset `(libsignalSessionLib.blockPlacement lsmpl j).base` variant of
    `lsRetAddr624_of_lr_eq_base_add`. -/
theorem lsRetAddr624_of_lr_eq_blockPlacement_base_zero [LibsignalPlacement] {s : State}
    (j : Nat) (hlr : s.readReg64 .lr = (libsignalSessionLib.blockPlacement lsmpl j).base)
    (hj : j < 624 := by decide) (ho : 0 < lsLen j := by decide) :
    LsRetAddr624 (s.readReg64 .lr) :=
  hlr ▸ lsRetAddr624_blockPlacement_base_zero j hj ho

/-- `LsRetAddr → LsRetAddr624` discharge when a caller already holds `LsRetAddr (s.readReg64 .lr)`. -/
theorem lsRetAddr624_of_lr_lsRetAddr [LibsignalPlacement] {s : State}
    (h : LsRetAddr (s.readReg64 .lr)) :
    LsRetAddr624 (s.readReg64 .lr) :=
  lsRetAddr624_of_lsRetAddr h

/-- One-line `bl`-site precondition discharge for `withLsRet spec` when
    `s.readReg64 .lr = lsmpl.base j + off`. -/
theorem satisfies_withLsRet_of_base_add [LibsignalPlacement] {α : Type}
    {spec : Spec α} {x : α} {s : State} {R : SepProp}
    (j : Nat) (off : BitVec 64)
    (hlr : s.readReg64 .lr = lsmpl.base j + off)
    (hpre : s.mem ⊨ spec.pre x s ∗ R)
    (hj : j < 624 := by decide) (ho : off.toNat < lsLen j := by decide) :
    s.mem ⊨ (withLsRet spec).pre x s ∗ R :=
  intro_withLsRet (lsRetAddr624_of_lr_eq_base_add j off hlr hj ho) hpre

/-- One-line `bl`-site precondition discharge for `withLsRet spec` when
    `s.readReg64 .lr = (libsignalSessionLib.blockPlacement lsmpl j).base + off`. -/
theorem satisfies_withLsRet_of_blockPlacement_base_add [LibsignalPlacement] {α : Type}
    {spec : Spec α} {x : α} {s : State} {R : SepProp}
    (j : Nat) (off : BitVec 64)
    (hlr : s.readReg64 .lr = (libsignalSessionLib.blockPlacement lsmpl j).base + off)
    (hpre : s.mem ⊨ spec.pre x s ∗ R)
    (hj : j < 624 := by decide) (ho : off.toNat < lsLen j := by decide) :
    s.mem ⊨ (withLsRet spec).pre x s ∗ R :=
  intro_withLsRet (lsRetAddr624_of_lr_eq_blockPlacement_base_add j off hlr hj ho) hpre

/-- Entailment form of `satisfies_withLsRet_of_base_add` (`spec.pre x s ⊢ (withLsRet spec).pre x s`). -/
theorem entails_withLsRet_of_base_add [LibsignalPlacement] {α : Type}
    {spec : Spec α} {x : α} {s : State}
    (j : Nat) (off : BitVec 64)
    (hlr : s.readReg64 .lr = lsmpl.base j + off)
    (hj : j < 624 := by decide) (ho : off.toNat < lsLen j := by decide) :
    spec.pre x s ⊢ (withLsRet spec).pre x s :=
  Entails.pure_right (lsRetAddr624_of_lr_eq_base_add j off hlr hj ho) (Entails.refl _)

/-- `(libsignalSessionLib.blockPlacement lsmpl j).base + off` variant of
    `entails_withLsRet_of_base_add`. -/
theorem entails_withLsRet_of_blockPlacement_base_add [LibsignalPlacement] {α : Type}
    {spec : Spec α} {x : α} {s : State}
    (j : Nat) (off : BitVec 64)
    (hlr : s.readReg64 .lr = (libsignalSessionLib.blockPlacement lsmpl j).base + off)
    (hj : j < 624 := by decide) (ho : off.toNat < lsLen j := by decide) :
    spec.pre x s ⊢ (withLsRet spec).pre x s :=
  Entails.pure_right (lsRetAddr624_of_lr_eq_blockPlacement_base_add j off hlr hj ho)
    (Entails.refl _)

/-! ## 4. Wrapper Commutations (`rfl` for Post-Only Wrappers, `=` for Pre/Post Framing Wrappers) -/

/-- Generic definitional commutation of `withLsRet` with any post-only update `{ spec with post := Q }`. -/
theorem withLsRet_withPost [LibsignalPlacement] {α : Type} (spec : Spec α)
    (Q : α → State → State → SepProp) :
    withLsRet { spec with post := Q } = { withLsRet spec with post := Q } := rfl

/-- Generic `Spec` equality commuting `withLsRet` with any right-framed `pre` wrapper
    `{ spec with pre := fun x s => spec.pre x s ∗ Fpre x s, post := Q }`. -/
theorem withLsRet_frameRight [LibsignalPlacement] {α : Type} (spec : Spec α)
    (Fpre : α → State → SepProp) (Q : α → State → State → SepProp) :
    withLsRet { spec with pre := fun x s => spec.pre x s ∗ Fpre x s, post := Q } =
      { withLsRet spec with pre := fun x s => (withLsRet spec).pre x s ∗ Fpre x s, post := Q } := by
  cases spec
  dsimp only [withLsRet]
  congr 1
  funext x s
  exact (sepConj_assoc _ _ _).symm

/-- Generic `Spec` equality commuting `withLsRet` with any left-framed `pre` wrapper
    `{ spec with pre := fun x s => Fpre x s ∗ spec.pre x s, post := Q }`. -/
theorem withLsRet_frameLeft [LibsignalPlacement] {α : Type} (spec : Spec α)
    (Fpre : α → State → SepProp) (Q : α → State → State → SepProp) :
    withLsRet { spec with pre := fun x s => Fpre x s ∗ spec.pre x s, post := Q } =
      { withLsRet spec with pre := fun x s => Fpre x s ∗ (withLsRet spec).pre x s, post := Q } := by
  cases spec
  dsimp only [withLsRet]
  congr 1
  funext x s
  exact sepConj_left_comm _ _ _

/-- `withLsRet` commutes definitionally (`rfl`) with `withVmPreserved`. -/
theorem withLsRet_withVmPreserved [LibsignalPlacement] {α : Type} (spec : Spec α) :
    withLsRet (withVmPreserved spec) = withVmPreserved (withLsRet spec) := rfl

/-- `withLsRet` unfolds `timeAddBudgetSpec` (`= withVmPreserved timeAddSpec`) by `rfl`. -/
theorem withLsRet_timeAddBudgetSpec [LibsignalPlacement] :
    withLsRet timeAddBudgetSpec = withVmPreserved (withLsRet timeAddSpec) := rfl

/-- `withLsRet` unfolds `durationSinceBudgetSpec` (`= withVmPreserved durationSinceSpec`) by `rfl`. -/
theorem withLsRet_durationSinceBudgetSpec [LibsignalPlacement] :
    withLsRet durationSinceBudgetSpec = withVmPreserved (withLsRet durationSinceSpec) := rfl

/-- `withLsRet` unfolds `durationSinceEpochBudgetSpec` (`= withVmPreserved durationSinceEpochSpec`)
    by `rfl`. -/
theorem withLsRet_durationSinceEpochBudgetSpec [LibsignalPlacement] :
    withLsRet durationSinceEpochBudgetSpec = withVmPreserved (withLsRet durationSinceEpochSpec) :=
  rfl

/-- `withLsRet` commutes definitionally (`rfl`) with `withOomPoolPreserved`. -/
theorem withLsRet_withOomPoolPreserved [LibsignalPlacement] {α : Type} (spec : Spec α) :
    withLsRet (withOomPoolPreserved spec) = withOomPoolPreserved (withLsRet spec) := rfl

/-- `withLsRet` commutes definitionally (`rfl`) with `Arm64.Spec.keepsFs`. -/
theorem withLsRet_keepsFs [LibsignalPlacement] {α : Type} (spec : Spec α) :
    withLsRet spec.keepsFs = (withLsRet spec).keepsFs := rfl

/-- `withLsRet` commutes definitionally (`rfl`) with `HookDischarge.Libc.Common.keepsFs`. -/
theorem withLsRet_libcKeepsFs [LibsignalPlacement] {α : Type} (spec : Spec α) :
    withLsRet (LibsignalBinary.Proofs.HookDischarge.Libc.Common.keepsFs spec) =
      LibsignalBinary.Proofs.HookDischarge.Libc.Common.keepsFs (withLsRet spec) := rfl

/-- `withLsRet` commutes with `StoreKit.withLsRoCl pl` (`Spec` equality via `sepConj_assoc`). -/
theorem withLsRet_withLsRoCl [LibsignalPlacement] {α : Type}
    (pl : MultiPlacement) (spec : Spec α) :
    withLsRet (withLsRoCl pl spec) = withLsRoCl pl (withLsRet spec) :=
  withLsRet_frameRight spec (fun _ s0 => ⌜LibsignalCodeRoLoaded pl s0.mem⌝)
    (fun x s0 sf => ⌜LibsignalCodeRoLoaded pl sf.mem⌝ ∗ spec.post x s0 sf)

/-- `withLsRet` commutes with `StoreKit.withLsCodeRoLoaded pl` (`Spec` equality via `sepConj_assoc`). -/
theorem withLsRet_withLsCodeRoLoaded [LibsignalPlacement] {α : Type}
    (pl : MultiPlacement) (spec : Spec α) :
    withLsRet (withLsCodeRoLoaded pl spec) = withLsCodeRoLoaded pl (withLsRet spec) :=
  withLsRet_frameRight spec (fun _ s0 => ⌜LibsignalCodeRoLoaded pl s0.mem⌝) spec.post

/-- `withLsRet` commutes with `CryptoVerification.withLsCodeLoaded pl` (`Spec` equality via
    `sepConj_assoc`). -/
theorem withLsRet_withLsCodeLoaded [LibsignalPlacement] {α : Type}
    (pl : MultiPlacement) (spec : Spec α) :
    withLsRet (withLsCodeLoaded pl spec) = withLsCodeLoaded pl (withLsRet spec) :=
  withLsRet_frameRight spec (fun _ s0 => ⌜LibsignalCodeLoaded pl s0.mem⌝) spec.post

/-- `withLsRet` commutes with `withRoData addr bytes` (`Spec` equality via `sepConj_left_comm`). -/
theorem withLsRet_withRoData [LibsignalPlacement] {α : Type}
    (addr : BitVec 64) (bytes : List (BitVec 8)) (spec : Spec α) :
    withLsRet (withRoData addr bytes spec) = withRoData addr bytes (withLsRet spec) :=
  withLsRet_frameLeft spec (fun _ s0 => ⌜RoDataAt s0.mem addr bytes⌝) spec.post

/-- `withLsRet` commutes with `withRoDataSep addr bytes` (`Spec` equality via `sepConj_left_comm`). -/
theorem withLsRet_withRoDataSep [LibsignalPlacement] {α : Type}
    (addr : BitVec 64) (bytes : List (BitVec 8)) (spec : Spec α) :
    withLsRet (withRoDataSep addr bytes spec) = withRoDataSep addr bytes (withLsRet spec) :=
  withLsRet_frameLeft spec (fun _ _ => addr ↦ᵣ bytes)
    (fun x s0 sf => (addr ↦ᵣ bytes) ∗ spec.post x s0 sf)

/-- `withLsRet` commutes with `MultiPlacedLib.withCodeLoaded mpl` (`Spec` equality via
    `sepConj_assoc`). -/
theorem withLsRet_withCodeLoaded [LibsignalPlacement] {α : Type}
    (lib : MultiPlacedLib) (mpl : MultiPlacement) (spec : Spec α) :
    withLsRet (lib.withCodeLoaded mpl spec) = lib.withCodeLoaded mpl (withLsRet spec) :=
  withLsRet_frameRight spec (fun _ s0 => ⌜lib.CodeLoaded mpl s0.mem⌝) spec.post

/-- `withLsRet` commutes with `Spec.inImage img` (`Spec` equality via `sepConj_left_comm`). -/
theorem withLsRet_inImage [LibsignalPlacement] {α : Type}
    (spec : Spec α) (img : Obj.Image) :
    withLsRet (spec.inImage img) = (withLsRet spec).inImage img :=
  withLsRet_frameLeft spec (fun _ s => ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝) spec.post

/-- `withLsRet` commutes with `withStack · hookStack` (`Spec` equality via `sepConj_assoc`). -/
theorem withLsRet_withStack [LibsignalPlacement] {α : Type}
    (spec : Spec α) (hookStack : Nat) :
    withLsRet (withStack spec hookStack) = withStack (withLsRet spec) hookStack :=
  withLsRet_frameRight spec (fun _ s => stackAt s.sp hookStack)
    (fun x s0 sf => spec.post x s0 sf ∗ stackAt s0.sp hookStack)

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
