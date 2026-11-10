/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.Wave1.TimeAdd
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
import ProofLib.SepLogic.WP.Structural

/-!
# `<SystemTime as Add<Duration>>::add` CLI hook discharge

Bridges `VerifiedLibraries.RustStd.timeAddSpec` (`timeMultiLib` block `2`, 96 bytes, 16-byte
overflow stack frame) to `LibsignalPublicApi.timeAddSpec`. On whole-second durations (`nanos = 0`)
with `tvNsec < 10 ^ 9`, `timespecCheckedAdd` agrees with `SystemTime.checkedAddSecs`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.RustStd.TimeAdd

open Arm64 ProofLib
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries.RustStd (timeMultiLib timeAddSym rustTimeExpectFailedSym timeExterns
  timespecCheckedAdd timeAdd_ok timeAdd_subroutineOk_of_panic)
open CryptoGames.LibsignalSessionApi (SystemTime)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi (timeAddHookName)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)

/-- Stack-parameterized `LibsignalPublicApi.timeAddSpec` (`cliTimeAddSpec extHookStack = timeAddSpec`). -/
def cliTimeAddSpec (hookStack : Nat := extHookStack) : Spec (SystemTime × Nat) where
  pre := fun (t, secs) s =>
    ⌜s.readReg64 .x0 = t.tvSec ∧ (s.readReg64 .x1).setWidth 32 = t.tvNsec ∧
      t.tvNsec.toNat < 10 ^ 9 ∧ (s.readReg64 .x2).toNat = secs ∧
      (s.readReg64 .x3).setWidth 32 = 0#32⌝ ∗ stackAt s.sp hookStack
  post := fun (t, secs) s0 sf =>
    ⌜t.checkedAddSecs secs = some ⟨sf.readReg64 .x0, (sf.readReg64 .x1).setWidth 32⟩ ∧
      sf.trace = s0.trace⌝ ∗ stackAt s0.sp hookStack
  onPanic := fun (t, secs) s0 sf => ⌜t.checkedAddSecs secs = none ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem cliTimeAddSpec_extHookStack :
    cliTimeAddSpec extHookStack = CryptoVerification.LibsignalPublicApi.timeAddSpec := rfl

theorem timeAddSym_eq_hookName : timeAddSym = timeAddHookName := rfl

/-- For whole-second durations (`nanos = 0#32`, `t.tvNsec.toNat < 10 ^ 9`), `timespecCheckedAdd`
agrees with `t.checkedAddSecs secs.toNat`. -/
theorem timespecCheckedAdd_zero_nanos_eq (t : SystemTime) (secs : BitVec 64)
    (hns : t.tvNsec.toNat < 10 ^ 9) :
    timespecCheckedAdd ⟨t.tvSec, t.tvNsec⟩ ⟨secs, 0#32⟩ =
      (t.checkedAddSecs secs.toNat).map (fun r => ⟨r.tvSec, r.tvNsec⟩) := by
  unfold timespecCheckedAdd SystemTime.checkedAddSecs
  dsimp only
  have hn : ¬ (10 ^ 9 ≤ t.tvNsec.toNat + (0#32).toNat) := by
    change ¬ (10 ^ 9 ≤ t.tvNsec.toNat + 0)
    omega
  have hbv : BitVec.ofNat 32 (t.tvNsec.toNat + (0#32).toNat) = t.tvNsec := by
    apply BitVec.eq_of_toNat_eq
    change (t.tvNsec.toNat + 0) % 2 ^ 32 = t.tvNsec.toNat
    rw [Nat.add_zero, Nat.mod_eq_of_lt t.tvNsec.isLt]
  by_cases hov : (2 ^ 63 - 1 : Int) < t.tvSec.toInt + (secs.toNat : Int)
  · have hnotle : ¬ (t.tvSec.toInt + (secs.toNat : Int) ≤ 2 ^ 63 - 1) := by omega
    simp only [hov, hnotle, ↓reduceIte, Option.map_none]
  · have hle : t.tvSec.toInt + (secs.toNat : Int) ≤ 2 ^ 63 - 1 := by omega
    simp only [hov, hle, hn, hbv, ↓reduceIte, Option.map_some]

private theorem rustStdTimeAdd_simulates_keepsFs {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    SpecSimulates VerifiedLibraries.RustStd.timeAddSpec (keepsFs (cliTimeAddSpec hookStack)) := by
  rintro ⟨t, secs⟩ R s0 hpre
  dsimp only [keepsFs, cliTimeAddSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hns, hx2, hx3⟩, hpre⟩ := hpre
  subst hx2
  rw [stackAt_shrink s0.sp hookStack 16 hstk.1 hstk.2,
    stackAt_eq_stackFrameAt s0.sp 16 (by decide)] at hpre
  have hx1_32 : s0.readReg32 .x1 = t.tvNsec := by
    have hsw : s0.readReg32 .x1 = (s0.readReg64 .x1).setWidth 32 := by
      simp [State.readReg32, State.readReg64]
    exact hsw.trans hx1
  have hx3_32 : s0.readReg32 .x3 = 0#32 := by
    have hsw : s0.readReg32 .x3 = (s0.readReg64 .x3).setWidth 32 := by
      simp [State.readReg32, State.readReg64]
    exact hsw.trans hx3
  let x2 : BitVec 64 := s0.readReg64 .x2
  refine ⟨(⟨t.tvSec, t.tvNsec⟩, ⟨x2, 0#32⟩),
    memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - 16) ∗ R, ?_, ?_⟩
  · dsimp only [VerifiedLibraries.RustStd.timeAddSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1_32, rfl, hx3_32, hns, by decide⟩,
      Satisfies.mono (by sep_entail) hpre⟩
  · intro sf hout
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [VerifiedLibraries.RustStd.timeAddSpec] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      obtain ⟨⟨⟨r, hr, hrx0, hrx1⟩, htr, hfs⟩, hpost⟩ := hpost
      rw [timespecCheckedAdd_zero_nanos_eq t x2 hns] at hr
      have hchk :
          t.checkedAddSecs x2.toNat =
            some ⟨sf.readReg64 .x0, (sf.readReg64 .x1).setWidth 32⟩ := by
        cases hc : t.checkedAddSecs x2.toNat with
        | none => simp [hc] at hr
        | some out =>
          simp only [hc, Option.map_some, Option.some.injEq] at hr
          have hsec : r.sec = out.tvSec := by cases hr; rfl
          have hnsec : r.nsec = out.tvNsec := by cases hr; rfl
          have hx1_f : (sf.readReg64 .x1).setWidth 32 = out.tvNsec := by
            rw [hrx1, hnsec]
            exact (BitVec.setWidth_setWidth_of_le out.tvNsec (by decide)).trans
              (BitVec.setWidth_eq out.tvNsec)
          rw [hrx0, hsec, hx1_f]
      dsimp only [keepsFs, cliTimeAddSpec]
      rw [stackAt_shrink s0.sp hookStack 16 hstk.1 hstk.2,
        stackAt_eq_stackFrameAt s0.sp 16 (by decide)]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hfs, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hchk, htr⟩, Satisfies.mono (by sep_entail) hpost⟩
    · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
      dsimp only [VerifiedLibraries.RustStd.timeAddSpec] at hpan
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
      obtain ⟨⟨hnone, htr, _hfs⟩, hpan⟩ := hpan
      rw [timespecCheckedAdd_zero_nanos_eq t x2 hns] at hnone
      have hchk_none : t.checkedAddSecs x2.toNat = none := by
        cases hc : t.checkedAddSecs x2.toNat with
        | none => rfl
        | some _ => simp [hc] at hnone
      dsimp only [keepsFs, cliTimeAddSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hchk_none, htr ▸ List.prefix_refl s0.trace⟩, ?_⟩
      rw [← sepConj_assoc] at hpan
      exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hpan
    · exact False.elim (not_satisfies_false_sepConj hex)
    · exact False.elim (not_satisfies_false_sepConj hoom)

/-! ## Spec-level bridges (`VerifiedLibraries.RustStd.timeAddSpec → LibsignalPublicApi.timeAddSpec`) -/

/-- Any subroutine satisfying `VerifiedLibraries.RustStd.timeAddSpec` satisfies
    `keepsFs (cliTimeAddSpec hookStack)` whenever `16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64`. -/
theorem rustStdTimeAdd_cliTimeAddSpec_keepsFs_ok {prog : Program} {entry : BitVec 64}
    {hookStack : Nat} (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (h : subroutine_ok prog entry VerifiedLibraries.RustStd.timeAddSpec) :
    subroutine_ok prog entry (keepsFs (cliTimeAddSpec hookStack)) :=
  (rustStdTimeAdd_simulates_keepsFs hstk).subroutine_ok h

/-- Any subroutine satisfying `VerifiedLibraries.RustStd.timeAddSpec` satisfies
    `cliTimeAddSpec hookStack` whenever `16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64`. -/
theorem rustStdTimeAdd_cliTimeAddSpec_ok {prog : Program} {entry : BitVec 64}
    {hookStack : Nat} (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (h : subroutine_ok prog entry VerifiedLibraries.RustStd.timeAddSpec) :
    subroutine_ok prog entry (cliTimeAddSpec hookStack) :=
  ((rustStdTimeAdd_simulates_keepsFs hstk).trans SpecSimulates.drop_keepsFs).subroutine_ok h

/-- `VerifiedLibraries.RustStd.timeAddSpec` implies `LibsignalPublicApi.timeAddSpec`. -/
theorem rustStdTimeAdd_timeAddSpec_ok {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry VerifiedLibraries.RustStd.timeAddSpec) :
    subroutine_ok prog entry CryptoVerification.LibsignalPublicApi.timeAddSpec :=
  rustStdTimeAdd_cliTimeAddSpec_ok (by decide) h

theorem rustStdTimeAdd_timeAddSpec_keepsFs_ok {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry VerifiedLibraries.RustStd.timeAddSpec) :
    subroutine_ok prog entry (keepsFs CryptoVerification.LibsignalPublicApi.timeAddSpec) :=
  rustStdTimeAdd_cliTimeAddSpec_keepsFs_ok (by decide) h

/-! ## Placed `timeMultiLib` bridges -/

/-- Program-generic real-code discharge: `timeMultiLib`'s `<SystemTime as Add<Duration>>::add`
    satisfies `timeMultiLib.withCodeLoaded mpl LibsignalPublicApi.timeAddSpec` on any program `P`
    that has no hooks inside the 96-byte body of `TimeAdd` and maps `rustTimeExpectFailedSym` to
    `Rust.panicked`. -/
theorem timeAdd_placed_timeAddSpec_ok {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 96 → P.externAt? (mpl.base 2 + BitVec.ofNat 64 off) = none)
    (hpanic : P.externAt? ((timeMultiLib.blockPlacement mpl 2).ρ rustTimeExpectFailedSym) =
      some Rust.panicked) :
    subroutine_ok P (timeMultiLib.fnAddr mpl timeAddSym)
      (timeMultiLib.withCodeLoaded mpl CryptoVerification.LibsignalPublicApi.timeAddSpec) :=
  (((rustStdTimeAdd_simulates_keepsFs (by decide)).trans SpecSimulates.drop_keepsFs).withCodeLoaded
    timeMultiLib mpl).subroutine_ok (timeAdd_ok hpl hext hpanic)

/-- `MultiPlacedLib.subroutineOk` for `timeAddSym` against
    `CryptoVerification.LibsignalPublicApi.timeAddSpec` under any extern table mapping
    `rustTimeExpectFailedSym` to `Rust.panicked`. -/
theorem timeAdd_timeAddSpec_subroutineOk_of_panic {externs : String → Option (State → State)}
    (hpanic : externs rustTimeExpectFailedSym = some Rust.panicked) :
    timeMultiLib.subroutineOk timeAddSym
      (fun _ => CryptoVerification.LibsignalPublicApi.timeAddSpec) externs :=
  SpecSimulates.multiSubroutineOk
    (fun _ => (rustStdTimeAdd_simulates_keepsFs (by decide)).trans SpecSimulates.drop_keepsFs)
    (timeAdd_subroutineOk_of_panic hpanic)

/-- Canonical `MultiPlacedLib.subroutineOk` for `timeAddSym` against
    `CryptoVerification.LibsignalPublicApi.timeAddSpec` under `timeExterns hooks`. -/
theorem timeAdd_timeAddSpec_subroutineOk
    (hooks : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeAddSym
      (fun _ => CryptoVerification.LibsignalPublicApi.timeAddSpec) (timeExterns hooks) :=
  timeAdd_timeAddSpec_subroutineOk_of_panic (VerifiedLibraries.RustStd.timeExterns_expectFailed hooks)

end LibsignalBinary.Proofs.HookDischarge.RustStd.TimeAdd
