/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.Wave2.FromUtf8
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common

/-!
# `core::str::converts::from_utf8` CLI hook discharge

Bridges `VerifiedLibraries.RustStd.coreFromUtf8Spec` (`coreMultiLib` block `1`, 624 bytes, 0-byte
stack frame) to `CliExt.fromUtf8Spec` (`fromUtf8AsciiSpec`), under either `withRoDataSep` or pure
`withRoData` for the 256-byte `UTF8_CHAR_WIDTH` table `corePlacedData1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8

open Arm64 ProofLib
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries.RustStd (coreMultiLib coreFromUtf8Sym coreUtf8CharWidthSym corePlacedData1
  coreFromUtf8Spec coreFromUtf8_ok coreFromUtf8_subroutineOk runUtf8Validation
  runUtf8ValidationLoop runUtf8ValidationLoop_nil runUtf8ValidationLoop_ascii_cons
  fromUtf8SretPost)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.CliExt (fromUtf8Spec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (withRoData withRoDataSep
  subroutine_ok_withRoData_of_sep SpecSimulates keepsFs_withRoData)

/-- Stack-parameterized `CliExt.fromUtf8Spec` (`fromUtf8AsciiSpec extHookStack = fromUtf8Spec`). -/
def fromUtf8AsciiSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (r, p, bs) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = BitVec.ofNat 64 bs.length ∧
      s0.readReg64 (.gpr 8#5) = r ∧ ∀ b ∈ bs, b.toNat < 128⌝ ∗
      (p ↦ₛ bs) ∗ memRegion r 24 ∗ stackAt s0.sp hookStack
  post := fun (r, p, bs) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗ (p ↦ₛ bs) ∗ (r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ p) ∗
      ((r + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ stackAt s0.sp hookStack

theorem fromUtf8AsciiSpec_extHookStack : fromUtf8AsciiSpec extHookStack = fromUtf8Spec := rfl

private theorem corePlacedData1_length_le : corePlacedData1.length ≤ 2 ^ 64 := by
  have h : corePlacedData1.length = 256 := rfl
  rw [h]
  decide

private theorem runUtf8ValidationLoop_of_ascii (off : Nat) :
    ∀ {bs : List (BitVec 8)}, (∀ b ∈ bs, b.toNat < 128) →
      runUtf8ValidationLoop off bs = .ok ()
  | [], _ => runUtf8ValidationLoop_nil off
  | b0 :: rest, hascii => by
    have hb0 : b0 < 0x80#8 :=
      BitVec.lt_def.mpr (show b0.toNat < (0x80#8).toNat from hascii b0 List.mem_cons_self)
    rw [runUtf8ValidationLoop_ascii_cons hb0]
    exact runUtf8ValidationLoop_of_ascii (off + 1)
      (fun b hb => hascii b (List.mem_cons_of_mem b0 hb))

/-- Every pure-ASCII byte slice passes `runUtf8Validation` (`.ok ()`). -/
theorem runUtf8Validation_of_ascii {bs : List (BitVec 8)} (hascii : ∀ b ∈ bs, b.toNat < 128) :
    runUtf8Validation bs = .ok () :=
  runUtf8ValidationLoop_of_ascii 0 hascii

private theorem slice_lt_two_pow_64_of_sep_region24 {m : Memory} {p r : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp}
    (h : m ⊨ (p ↦ₛ bs) ∗ (memRegion r 24 ∗ R)) :
    bs.length < 2 ^ 64 := by
  have hle : bs.length ≤ 2 ^ 64 := ((IsBlock.pointsToBytes p bs).read h).1
  by_cases heq : bs.length = 2 ^ 64
  · exfalso
    have hd := (IsBlock.pointsToBytes p bs).disjoint (IsBlock.memRegion r 24)
      (by omega) (by decide) h
    have hd1 := hd.1
    have hlt := (r - p).isLt
    omega
  · omega

private theorem coreFromUtf8_simulates_roSep_keepsFs (tbl : BitVec 64)
    (hookStack : Nat := extHookStack) :
    SpecSimulates (coreFromUtf8Spec tbl)
      (withRoDataSep tbl corePlacedData1 (keepsFs (fromUtf8AsciiSpec hookStack))) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨r, p, bs⟩ R s0 hpre
  dsimp only [withRoDataSep, keepsFs, fromUtf8AsciiSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [sepConj_left_comm (tbl ↦ᵣ corePlacedData1) ⌜_⌝, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx8, hascii⟩, hpre⟩ := hpre
  have hlen : bs.length < 2 ^ 64 :=
    slice_lt_two_pow_64_of_sep_region24 (R := (tbl ↦ᵣ corePlacedData1) ∗ stackAt s0.sp hookStack ∗ R)
      (Satisfies.mono (by sep_entail) hpre)
  rw [memRegion_split3_ord r 24 18 2 (by decide) (by decide),
    memRegion_two, memRegion_four] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  obtain ⟨b20, b18, hpre⟩ := hpre
  refine ⟨(p, r, bs, b18, b20), stackAt s0.sp hookStack ∗ R, ?_, ?_⟩
  · dsimp only [coreFromUtf8Spec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlen⟩, Satisfies.mono (by sep_entail) hpre⟩
  · intro sf _hret _hcc hpost
    dsimp only [coreFromUtf8Spec] at hpost
    rw [runUtf8Validation_of_ascii hascii] at hpost
    dsimp only [fromUtf8SretPost] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨htr, hfs⟩, hpost⟩ := hpost
    dsimp only [withRoDataSep, keepsFs, fromUtf8AsciiSpec]
    simp only [sepConj_assoc]
    rw [sepConj_left_comm (tbl ↦ᵣ corePlacedData1) ⌜sf.fs = s0.fs⌝,
      satisfies_pure_sepConj]
    refine ⟨hfs, ?_⟩
    rw [sepConj_left_comm (tbl ↦ᵣ corePlacedData1) ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝,
      satisfies_pure_sepConj]
    exact ⟨⟨htr, hfs⟩, Satisfies.mono (by sep_entail) hpost⟩

/-! ## Spec-level bridges (`coreFromUtf8Spec tbl → CliExt.fromUtf8Spec`) -/

/-- `coreFromUtf8Spec tbl` implies `withRoDataSep tbl corePlacedData1 (fromUtf8AsciiSpec hookStack)`. -/
theorem coreFromUtf8_fromUtf8AsciiSpec_roSep_ok {prog : Program} {entry tbl : BitVec 64}
    (hookStack : Nat := extHookStack)
    (h : subroutine_ok prog entry (coreFromUtf8Spec tbl)) :
    subroutine_ok prog entry (withRoDataSep tbl corePlacedData1 (fromUtf8AsciiSpec hookStack)) :=
  ((coreFromUtf8_simulates_roSep_keepsFs tbl hookStack).trans
    SpecSimulates.drop_keepsFs_withRoDataSep).subroutine_ok h

/-- `coreFromUtf8Spec tbl` implies `withRoData tbl corePlacedData1 (fromUtf8AsciiSpec hookStack)`. -/
theorem coreFromUtf8_fromUtf8AsciiSpec_ok {prog : Program} {entry tbl : BitVec 64}
    (hookStack : Nat := extHookStack)
    (h : subroutine_ok prog entry (coreFromUtf8Spec tbl)) :
    subroutine_ok prog entry (withRoData tbl corePlacedData1 (fromUtf8AsciiSpec hookStack)) :=
  subroutine_ok_withRoData_of_sep corePlacedData1_length_le
    (coreFromUtf8_fromUtf8AsciiSpec_roSep_ok hookStack h)

theorem coreFromUtf8_fromUtf8Spec_roSep_ok {prog : Program} {entry tbl : BitVec 64}
    (h : subroutine_ok prog entry (coreFromUtf8Spec tbl)) :
    subroutine_ok prog entry (withRoDataSep tbl corePlacedData1 fromUtf8Spec) :=
  coreFromUtf8_fromUtf8AsciiSpec_roSep_ok extHookStack h

theorem coreFromUtf8_fromUtf8Spec_ok {prog : Program} {entry tbl : BitVec 64}
    (h : subroutine_ok prog entry (coreFromUtf8Spec tbl)) :
    subroutine_ok prog entry (withRoData tbl corePlacedData1 fromUtf8Spec) :=
  coreFromUtf8_fromUtf8AsciiSpec_ok extHookStack h

theorem coreFromUtf8_fromUtf8Spec_keepsFs_ok {prog : Program} {entry tbl : BitVec 64}
    (h : subroutine_ok prog entry (coreFromUtf8Spec tbl)) :
    subroutine_ok prog entry (keepsFs (withRoData tbl corePlacedData1 fromUtf8Spec)) := by
  rw [keepsFs_withRoData]
  exact ((coreFromUtf8_simulates_roSep_keepsFs tbl extHookStack).trans
    (SpecSimulates.withRoData_of_sep corePlacedData1_length_le)).subroutine_ok h

/-! ## Placed `coreMultiLib` bridges -/

/-- Placed `coreMultiLib` `from_utf8` satisfies `withRoData tbl corePlacedData1 fromUtf8Spec`. -/
theorem coreFromUtf8_placed_fromUtf8Spec_ok {mpl : MultiPlacement}
    (hpl : coreMultiLib.Placeable mpl) {P : Program}
    (hext : ∀ off : Nat, off < 624 → P.externAt? (mpl.base 1 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (coreMultiLib.fnAddr mpl coreFromUtf8Sym)
      (coreMultiLib.withCodeLoaded mpl
        (withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1 fromUtf8Spec)) :=
  (((coreFromUtf8_simulates_roSep_keepsFs (mpl.ρ coreUtf8CharWidthSym) extHookStack).trans
    SpecSimulates.drop_keepsFs_withRoDataSep).trans
    (SpecSimulates.withRoData_of_sep corePlacedData1_length_le) |>.withCodeLoaded coreMultiLib mpl).subroutine_ok
    (coreFromUtf8_ok hpl hext)

/-- `MultiPlacedLib.subroutineOk` for `coreFromUtf8Sym` against `CliExt.fromUtf8Spec` (separating
    `withRoDataSep` form) under any `externs` map. -/
theorem coreFromUtf8_fromUtf8Spec_roSep_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym
      (fun mpl => withRoDataSep (mpl.ρ coreUtf8CharWidthSym) corePlacedData1 fromUtf8Spec)
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => (coreFromUtf8_simulates_roSep_keepsFs (mpl.ρ coreUtf8CharWidthSym) extHookStack).trans
      SpecSimulates.drop_keepsFs_withRoDataSep)
    (coreFromUtf8_subroutineOk externs)

/-- `MultiPlacedLib.subroutineOk` for `coreFromUtf8Sym` against `CliExt.fromUtf8Spec` (pure
    `withRoData` form) under any `externs` map. -/
theorem coreFromUtf8_fromUtf8Spec_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    coreMultiLib.subroutineOk coreFromUtf8Sym
      (fun mpl => withRoData (mpl.ρ coreUtf8CharWidthSym) corePlacedData1 fromUtf8Spec)
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun _ => SpecSimulates.withRoData_of_sep corePlacedData1_length_le)
    (coreFromUtf8_fromUtf8Spec_roSep_subroutineOk externs)

end LibsignalBinary.Proofs.HookDischarge.RustStd.FromUtf8
