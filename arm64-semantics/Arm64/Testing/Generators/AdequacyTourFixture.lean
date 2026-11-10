/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Object.Placed
public import Arm64.Trusted.Surface.IncludeBytes

/-!
# Checked-In `adequacy_tour` Placed-Library Fixture

Static `Arm64.Obj.PlacedLib` fixture (`adequacy_tourLib`) extracted from `AdequacyTourFixture.bin`.
-/

@[expose] public section

namespace Testing.Generators

open Arm64

set_option maxHeartbeats 10000000
set_option maxRecDepth 2000000

def adequacy_tourPlacedCode : List (BitVec 8) := include_bytes% "AdequacyTourFixture.bin" 0 396
def adequacy_tourPlacedData0 : List (BitVec 8) := include_bytes% "AdequacyTourFixture.bin" 396 36
def adequacy_tourPlacedData1 : List (BitVec 8) := include_bytes% "AdequacyTourFixture.bin" 432 11
def adequacy_tourPlacedData2 : List (BitVec 8) := include_bytes% "AdequacyTourFixture.bin" 443 24
def adequacy_tourPlacedData3 : List (BitVec 8) := include_bytes% "AdequacyTourFixture.bin" 467 23
def adequacy_tourPlacedData4 : List (BitVec 8) := include_bytes% "AdequacyTourFixture.bin" 490 24
def adequacy_tourPlacedData5 : List (BitVec 8) := include_bytes% "AdequacyTourFixture.bin" 514 32
def adequacy_tourPlacedData6 : List (BitVec 8) := include_bytes% "AdequacyTourFixture.bin" 546 24
def adequacy_tourPlacedData7 : List (BitVec 8) := include_bytes% "AdequacyTourFixture.bin" 570 44
def adequacy_tourPlacedData8 : List (BitVec 8) := include_bytes% "AdequacyTourFixture.bin" 614 24

def adequacy_tourText : Obj.CodeBlock where
  code := adequacy_tourPlacedCode
  align := 4
  symbols := [
    ("__rustc::rust_begin_unwind", 0x0),
    ("adequacy_tour::read_fixed_addr", 0x10),
    ("adequacy_tour::nonzero_exit_one", 0x20),
    ("adequacy_tour::stack_spill_verify", 0x34),
    ("adequacy_tour::write_own_code_bytes", 0x78),
    ("adequacy_tour::assert_getrandom_gt_5", 0x90),
    ("adequacy_tour::mmap_write_and_verify", 0xe4),
    ("adequacy_tour::verify_own_code_bytes", 0x14c)]
  relocs := [
    { off := 96, kind := .adrpHi21, sym := "adequacy_tour:.rodata..Lanon.0" },
    { off := 100, kind := .addLo12, sym := "adequacy_tour:.rodata..Lanon.0" },
    { off := 104, kind := .adrpHi21, sym := "adequacy_tour:.rodata..Lanon.2" },
    { off := 108, kind := .addLo12, sym := "adequacy_tour:.rodata..Lanon.2" },
    { off := 116, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking5panic" },
    { off := 204, kind := .adrpHi21, sym := "adequacy_tour:.rodata..Lanon.3" },
    { off := 208, kind := .addLo12, sym := "adequacy_tour:.rodata..Lanon.3" },
    { off := 212, kind := .adrpHi21, sym := "adequacy_tour:.rodata..Lanon.4" },
    { off := 216, kind := .addLo12, sym := "adequacy_tour:.rodata..Lanon.4" },
    { off := 224, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking5panic" },
    { off := 308, kind := .adrpHi21, sym := "adequacy_tour:.rodata.cst32+0x0" },
    { off := 312, kind := .addLo12, sym := "adequacy_tour:.rodata.cst32+0x0" },
    { off := 316, kind := .adrpHi21, sym := "adequacy_tour:.rodata..Lanon.6" },
    { off := 320, kind := .addLo12, sym := "adequacy_tour:.rodata..Lanon.6" },
    { off := 328, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking5panic" },
    { off := 372, kind := .adrpHi21, sym := "adequacy_tour:.rodata..Lanon.7" },
    { off := 376, kind := .addLo12, sym := "adequacy_tour:.rodata..Lanon.7" },
    { off := 380, kind := .adrpHi21, sym := "adequacy_tour:.rodata..Lanon.8" },
    { off := 384, kind := .addLo12, sym := "adequacy_tour:.rodata..Lanon.8" },
    { off := 392, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking5panic" }]
  externs := [
    "_RNvNtCskxtBwYRO61I_4core9panicking5panic"]

def adequacy_tourData : List Obj.SymDataInfo := [
  { sym := "adequacy_tour:.rodata..Lanon.0"
    align := 1
    readOnly := true
    bytes := adequacy_tourPlacedData0
    zeroTail := 0
    relocs := [] },
  { sym := "adequacy_tour:.rodata.str1.1+0x0"
    align := 1
    readOnly := true
    bytes := adequacy_tourPlacedData1
    zeroTail := 0
    relocs := [] },
  { sym := "adequacy_tour:.rodata..Lanon.2"
    align := 8
    readOnly := true
    bytes := adequacy_tourPlacedData2
    zeroTail := 0
    relocs := [
      { off := 0, kind := .abs64, sym := "adequacy_tour:.rodata.str1.1+0x0" }] },
  { sym := "adequacy_tour:.rodata..Lanon.3"
    align := 1
    readOnly := true
    bytes := adequacy_tourPlacedData3
    zeroTail := 0
    relocs := [] },
  { sym := "adequacy_tour:.rodata..Lanon.4"
    align := 8
    readOnly := true
    bytes := adequacy_tourPlacedData4
    zeroTail := 0
    relocs := [
      { off := 0, kind := .abs64, sym := "adequacy_tour:.rodata.str1.1+0x0" }] },
  { sym := "adequacy_tour:.rodata.cst32+0x0"
    align := 1
    readOnly := true
    bytes := adequacy_tourPlacedData5
    zeroTail := 0
    relocs := [] },
  { sym := "adequacy_tour:.rodata..Lanon.6"
    align := 8
    readOnly := true
    bytes := adequacy_tourPlacedData6
    zeroTail := 0
    relocs := [
      { off := 0, kind := .abs64, sym := "adequacy_tour:.rodata.str1.1+0x0" }] },
  { sym := "adequacy_tour:.rodata..Lanon.7"
    align := 1
    readOnly := true
    bytes := adequacy_tourPlacedData7
    zeroTail := 0
    relocs := [] },
  { sym := "adequacy_tour:.rodata..Lanon.8"
    align := 8
    readOnly := true
    bytes := adequacy_tourPlacedData8
    zeroTail := 0
    relocs := [
      { off := 0, kind := .abs64, sym := "adequacy_tour:.rodata.str1.1+0x0" }] }
]

/-- The placed library `adequacy_tour`. -/
def adequacy_tourLib : Obj.PlacedLib where
  name := "adequacy_tour"
  text := adequacy_tourText
  data := adequacy_tourData
  exports := [
    "adequacy_tour::read_fixed_addr",
    "adequacy_tour::nonzero_exit_one",
    "adequacy_tour::stack_spill_verify",
    "adequacy_tour::write_own_code_bytes",
    "adequacy_tour::assert_getrandom_gt_5",
    "adequacy_tour::mmap_write_and_verify",
    "adequacy_tour::verify_own_code_bytes"]

end Testing.Generators
