/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.Wave1.TimeDurationSince
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common

/-!
# `<std::time::SystemTime>::duration_since` CLI hook discharge

Bridges `VerifiedLibraries.RustStd.timeDurationSinceSpec` (`timeMultiLib` blocks `0..1`, 208-byte
stack frame) to `CliExt.durationSinceEpochSpec` (`self = earlier = UNIX_EPOCH`) and the bounded
contract `durationSinceBoundedSpec` (`tv_nsec < 10 ^ 9`), under `withRoData` / `withRoDataSep` for
the 16-byte `.rodata` constant `timePlacedData0`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.HookDischarge.RustStd.TimeDurationSince

open Arm64 ProofLib
open VerifiedLibraries.RustStd (timeMultiLib timeDurationSinceSym timeRodataCst16Sym timePlacedData0
  timeDurationSinceSpec timeDurationSince_subroutineOk)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.CliExt (durationSinceEpochSpec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (withRoData withRoDataSep
  subroutine_ok_withRoData_of_sep SpecSimulates keepsFs_withRoData)

/-- Stack-parameterized `UNIX_EPOCH` `duration_since` contract (`durationSinceEpochAtSpec extHookStack = durationSinceEpochSpec`). -/
def durationSinceEpochAtSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64) where
  pre := fun (p, ret) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret ∧
      s.readReg64 .x1 = 0#64 ∧ (s.readReg64 .x2).setWidth 32 = 0#32⌝ ∗
      (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₃₂ 0#32) ∗ memRegion (p + 12#64) 4 ∗
      memRegion ret 24 ∗ stackAt s.sp hookStack
  post := fun (p, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion p 16 ∗
      ((∃∗ w2 : BitVec 64, ∃∗ w0 : BitVec 64,
        (ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗ ((ret + 16#64) ↦₆₄ w2))) ∗
      stackAt s0.sp hookStack

theorem durationSinceEpochAtSpec_extHookStack :
    durationSinceEpochAtSpec extHookStack = durationSinceEpochSpec := rfl

private theorem timePlacedData0_length_le : timePlacedData0.length ≤ 2 ^ 64 := by
  have h : timePlacedData0.length = 16 := rfl
  rw [h]
  decide

/-- Stack-parameterized bounded `duration_since` contract for valid `SystemTime` inputs (`tv_nsec < 10 ^ 9`). -/
def durationSinceBoundedAtSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64) where
  pre := fun (p, ret) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret ∧
      ((s.readReg64 .x2).setWidth 32).toNat < 1000000000⌝ ∗
      (∃∗ tvSec : BitVec 64, ∃∗ tvNsec : BitVec 32,
        ⌜tvNsec.toNat < 1000000000⌝ ∗
        (p ↦₆₄ tvSec) ∗ ((p + 8#64) ↦₃₂ tvNsec) ∗ memRegion (p + 12#64) 4) ∗
      memRegion ret 24 ∗ stackAt s.sp hookStack
  post := fun (p, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion p 16 ∗ memRegion ret 24 ∗ stackAt s0.sp hookStack

/-- `durationSinceBoundedAtSpec` at `extHookStack`. -/
abbrev durationSinceBoundedSpec : Spec (BitVec 64 × BitVec 64) :=
  durationSinceBoundedAtSpec extHookStack

private theorem systemTime_entails_memRegion16 (p s1 : BitVec 64) (n1 : BitVec 32) :
    ((p ↦₆₄ s1) ∗ ((p + 8#64) ↦₃₂ n1) ∗ memRegion (p + 12#64) 4) ⊢ memRegion p 16 := by
  rw [memRegion_split3_ord p 16 8 4 (by decide) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion p s1)
    (sepConj_mono (pointsTo32_entails_memRegion (p + 8#64) n1) (Entails.refl _))

private theorem pair32_at16_entails_exists64 (ret : BitVec 64) (r16 b20 : BitVec 32) :
    (((ret + 16#64) ↦₃₂ r16) ∗ ((ret + 20#64) ↦₃₂ b20)) ⊢
      ∃∗ w2 : BitVec 64, (ret + 16#64) ↦₆₄ w2 := by
  rw [← memRegion_eight (ret + 16#64), memRegion_split (ret + 16#64) 4 4 (by decide)]
  have hoff : (ret + 16#64) + 4#64 = ret + 20#64 := by rw [BitVec.add_assoc]; rfl
  rw [hoff]
  exact sepConj_mono (pointsTo32_entails_memRegion (ret + 16#64) r16)
    (pointsTo32_entails_memRegion (ret + 20#64) b20)

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

private theorem timeDurationSince_simulates_epoch_roSep_keepsFs (c16 : BitVec 64)
    {hookStack : Nat} (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64) :
    SpecSimulates (timeDurationSinceSpec c16)
      (withRoDataSep c16 timePlacedData0 (keepsFs (durationSinceEpochAtSpec hookStack))) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨p, ret⟩ R s0 hpre
  dsimp only [withRoDataSep, keepsFs, durationSinceEpochAtSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (c16 ↦ᵣ timePlacedData0) ⌜_⌝, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8, hx1, hx2⟩, hpre⟩ := hpre
  rw [memRegion_split ret 20 4 (by decide), memRegion_four (ret + 20#64),
    stackAt_shrink s0.sp hookStack 208 hstk.1 hstk.2,
    stackAt_eq_stackFrameAt s0.sp 208 (by decide)] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  obtain ⟨b20, hpre⟩ := hpre
  have hx2_32 : s0.readReg32 .x2 = 0#32 := by
    have hsw : s0.readReg32 .x2 = (s0.readReg64 .x2).setWidth 32 := by
      simp [State.readReg32, State.readReg64]
    exact hsw.trans hx2
  refine ⟨(p, 0#64, 0#32, ret, s0.sp, 0#64, 0#32, b20),
    memRegion (p + 12#64) 4 ∗ memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - 208) ∗ R,
    ?_, ?_⟩
  · dsimp only [timeDurationSinceSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2_32, hx8, rfl, by decide, by decide⟩,
      Satisfies.mono (by sep_entail) hpre⟩
  · intro sf _hret _hcc hpost
    dsimp only [timeDurationSinceSpec] at hpost
    have htag :
        (if ((0#64).toInt * 10 ^ 9 + ↑(0#32).toNat : Int) ≤
              (0#64).toInt * 10 ^ 9 + ↑(0#32).toNat
         then 0#64 else 1#64) = 0#64 := by decide
    have hdiv :
        BitVec.ofNat 64
          ((((0#64).toInt * 10 ^ 9 + ↑(0#32).toNat : Int) -
            ((0#64).toInt * 10 ^ 9 + ↑(0#32).toNat : Int)).natAbs / 10 ^ 9) = 0#64 := by decide
    have hmod :
        BitVec.ofNat 32
          ((((0#64).toInt * 10 ^ 9 + ↑(0#32).toNat : Int) -
            ((0#64).toInt * 10 ^ 9 + ↑(0#32).toNat : Int)).natAbs % 10 ^ 9) = 0#32 := by decide
    rw [htag, hdiv, hmod, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨htr, hfs⟩, hpost⟩ := hpost
    have hp16 := systemTime_entails_memRegion16 p 0#64 0#32
    have hw2 := pair32_at16_entails_exists64 ret 0#32 b20
    have hreord :
        sf.mem ⊨ ((p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₃₂ 0#32) ∗ memRegion (p + 12#64) 4) ∗
          (((ret + 16#64) ↦₃₂ 0#32) ∗ ((ret + 20#64) ↦₃₂ b20)) ∗
          (c16 ↦ᵣ timePlacedData0) ∗ (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - 208) ∗
          stackFrameAt s0.sp 208 ∗ R :=
      Satisfies.mono (by sep_entail) hpost
    have hstep := Satisfies.mono
      (sepConj_mono hp16 (sepConj_mono hw2 (Entails.refl _))) hreord
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hstep
    obtain ⟨w2, hpost1⟩ := hstep
    dsimp only [withRoDataSep, keepsFs, durationSinceEpochAtSpec]
    rw [stackAt_shrink s0.sp hookStack 208 hstk.1 hstk.2,
      stackAt_eq_stackFrameAt s0.sp 208 (by decide)]
    simp only [sepConj_assoc]
    rw [sepConj_left_comm (c16 ↦ᵣ timePlacedData0) ⌜sf.fs = s0.fs⌝,
      satisfies_pure_sepConj]
    refine ⟨hfs, ?_⟩
    rw [sepConj_left_comm (c16 ↦ᵣ timePlacedData0) ⌜sf.trace = s0.trace⌝, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨w2, 0#64, Satisfies.mono (by sep_entail) hpost1⟩

private theorem timeDurationSince_simulates_bounded_roSep_keepsFs (c16 : BitVec 64)
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

/-! ## Spec-level bridges (`timeDurationSinceSpec c16 → CliExt.durationSinceEpochSpec`) -/

/-- Separating `.rodata` + `keepsFs` bridge for `durationSinceEpochAtSpec hookStack` (`208 ≤ hookStack ≤ 2 ^ 64`). -/
theorem timeDurationSince_epochAtSpec_roSep_keepsFs_ok {prog : Program} {entry c16 : BitVec 64}
    {hookStack : Nat} (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (timeDurationSinceSpec c16)) :
    subroutine_ok prog entry
      (keepsFs (withRoDataSep c16 timePlacedData0 (durationSinceEpochAtSpec hookStack))) :=
  ((timeDurationSince_simulates_epoch_roSep_keepsFs c16 hstk).trans
    SpecSimulates.keepsFs_withRoDataSep).subroutine_ok h

/-- Separating `.rodata` bridge for `durationSinceEpochAtSpec hookStack`. -/
theorem timeDurationSince_epochAtSpec_roSep_ok {prog : Program} {entry c16 : BitVec 64}
    {hookStack : Nat} (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (timeDurationSinceSpec c16)) :
    subroutine_ok prog entry
      (withRoDataSep c16 timePlacedData0 (durationSinceEpochAtSpec hookStack)) :=
  ((timeDurationSince_simulates_epoch_roSep_keepsFs c16 hstk).trans
    SpecSimulates.drop_keepsFs_withRoDataSep).subroutine_ok h

/-- Pure `RoDataAt` + `keepsFs` bridge for `durationSinceEpochAtSpec hookStack`. -/
theorem timeDurationSince_epochAtSpec_keepsFs_ok {prog : Program} {entry c16 : BitVec 64}
    {hookStack : Nat} (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (timeDurationSinceSpec c16)) :
    subroutine_ok prog entry
      (keepsFs (withRoData c16 timePlacedData0 (durationSinceEpochAtSpec hookStack))) := by
  rw [keepsFs_withRoData]
  exact ((timeDurationSince_simulates_epoch_roSep_keepsFs c16 hstk).trans
    (SpecSimulates.withRoData_of_sep timePlacedData0_length_le)).subroutine_ok h

/-- Pure `RoDataAt` bridge for `durationSinceEpochAtSpec hookStack`. -/
theorem timeDurationSince_epochAtSpec_ok {prog : Program} {entry c16 : BitVec 64}
    {hookStack : Nat} (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (timeDurationSinceSpec c16)) :
    subroutine_ok prog entry
      (withRoData c16 timePlacedData0 (durationSinceEpochAtSpec hookStack)) :=
  subroutine_ok_withRoData_of_sep timePlacedData0_length_le
    (timeDurationSince_epochAtSpec_roSep_ok hstk h)

/-- `timeDurationSinceSpec c16` implies `withRoData c16 timePlacedData0 durationSinceEpochSpec`. -/
theorem timeDurationSince_durationSinceEpochSpec_ok {prog : Program} {entry c16 : BitVec 64}
    (h : subroutine_ok prog entry (timeDurationSinceSpec c16)) :
    subroutine_ok prog entry (withRoData c16 timePlacedData0 durationSinceEpochSpec) :=
  timeDurationSince_epochAtSpec_ok (by decide) h

/-- `timeDurationSinceSpec c16` implies `withRoDataSep c16 timePlacedData0 durationSinceEpochSpec`. -/
theorem timeDurationSince_durationSinceEpochSpec_roSep_ok {prog : Program} {entry c16 : BitVec 64}
    (h : subroutine_ok prog entry (timeDurationSinceSpec c16)) :
    subroutine_ok prog entry (withRoDataSep c16 timePlacedData0 durationSinceEpochSpec) :=
  timeDurationSince_epochAtSpec_roSep_ok (by decide) h

/-- General bounded bridge (`durationSinceBoundedAtSpec hookStack`, `n1 < 10^9 ∧ n2 < 10^9`) in
    separating `withRoDataSep` + `keepsFs` form. -/
theorem timeDurationSince_boundedAtSpec_roSep_keepsFs_ok {prog : Program} {entry c16 : BitVec 64}
    {hookStack : Nat} (hstk : 208 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (timeDurationSinceSpec c16)) :
    subroutine_ok prog entry
      (keepsFs (withRoDataSep c16 timePlacedData0 (durationSinceBoundedAtSpec hookStack))) :=
  ((timeDurationSince_simulates_bounded_roSep_keepsFs c16 hstk).trans
    SpecSimulates.keepsFs_withRoDataSep).subroutine_ok h

/-- General bounded bridge (`durationSinceBoundedSpec`, `hookStack = extHookStack`) in pure
    `RoDataAt` form. -/
theorem timeDurationSince_boundedSpec_ok {prog : Program} {entry c16 : BitVec 64}
    (h : subroutine_ok prog entry (timeDurationSinceSpec c16)) :
    subroutine_ok prog entry (withRoData c16 timePlacedData0 durationSinceBoundedSpec) :=
  (((timeDurationSince_simulates_bounded_roSep_keepsFs c16 (by decide)).trans
    SpecSimulates.drop_keepsFs_withRoDataSep).trans
    (SpecSimulates.withRoData_of_sep timePlacedData0_length_le)).subroutine_ok h

/-! ## Placed `timeMultiLib` bridges -/

/-- `MultiPlacedLib.subroutineOk` for `timeDurationSinceSym` against `CliExt.durationSinceEpochSpec`
    (pure `withRoData` form) under any `externs` map. -/
theorem timeDurationSince_durationSinceEpochSpec_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0
        durationSinceEpochSpec)
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      ((timeDurationSince_simulates_epoch_roSep_keepsFs (mpl.ρ timeRodataCst16Sym) (by decide)).trans
        SpecSimulates.drop_keepsFs_withRoDataSep).trans
        (SpecSimulates.withRoData_of_sep timePlacedData0_length_le))
    (timeDurationSince_subroutineOk externs)

/-- `MultiPlacedLib.subroutineOk` for `timeDurationSinceSym` against `CliExt.durationSinceEpochSpec`
    (separating `withRoDataSep` form) under any `externs` map. -/
theorem timeDurationSince_durationSinceEpochSpec_roSep_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => withRoDataSep (mpl.ρ timeRodataCst16Sym) timePlacedData0
        durationSinceEpochSpec)
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      (timeDurationSince_simulates_epoch_roSep_keepsFs (mpl.ρ timeRodataCst16Sym) (by decide)).trans
        SpecSimulates.drop_keepsFs_withRoDataSep)
    (timeDurationSince_subroutineOk externs)

/-- `MultiPlacedLib.subroutineOk` for `timeDurationSinceSym` against `durationSinceBoundedSpec`
    (pure `withRoData` form) under any `externs` map. -/
theorem timeDurationSince_boundedSpec_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0 durationSinceBoundedSpec)
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl =>
      ((timeDurationSince_simulates_bounded_roSep_keepsFs (mpl.ρ timeRodataCst16Sym) (by decide)).trans
        SpecSimulates.drop_keepsFs_withRoDataSep).trans
        (SpecSimulates.withRoData_of_sep timePlacedData0_length_le))
    (timeDurationSince_subroutineOk externs)

end LibsignalBinary.Proofs.HookDischarge.RustStd.TimeDurationSince
