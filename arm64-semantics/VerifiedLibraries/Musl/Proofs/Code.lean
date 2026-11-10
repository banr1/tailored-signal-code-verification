/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.Placed.Fetch
public import VerifiedLibraries.Musl.Spec
public import VerifiedLibraries.Musl.Proofs.MemcpySym
public import VerifiedLibraries.Musl.Proofs.MemsetSymCommon

/-!
# Instruction Words and Relocations for `musl` String Routines

Defines instruction word lists, relocation entries, and `Program.hasWords` segment-extraction
lemmas for `VerifiedLibraries.muslStringLib`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Musl

open Arm64 ProofLib

theorem muslStringProg_fnAddr {pl : Obj.Placement} {hooks : String → Option (State → State)}
    {name : String} {fo : Nat}
    (hsym : Obj.lookup name VerifiedLibraries.muslStringLib.text.symbols = some fo) :
    (muslStringProg pl hooks).fnAddr name = pl.base + BitVec.ofNat 64 fo := by
  have h := Obj.PlacedLib.fnAddr_program
    (pl := pl) (X := hooks) (O := fun _ => none) (svc := Syscall.standard) hsym
  exact h.1.trans h.2

theorem muslStringLib_resolve_sym {pl : Obj.Placement} {hooks : String → Option (State → State)}
    {name : String} {fo : Nat}
    (hsym : Obj.lookup name VerifiedLibraries.muslStringLib.text.symbols = some fo) :
    VerifiedLibraries.muslStringLib.text.resolve pl name =
      (muslStringProg pl hooks).fnAddr name := by
  rw [muslStringProg_fnAddr hsym]
  simp [Obj.CodeBlock.resolve, hsym]

private theorem len_le_of_checkSegment {blk : Obj.CodeBlock} {fo : Nat}
    {ws : List (BitVec 32)} {R : List Obj.RelocEntry}
    (hchk : blk.checkSegment fo ws R = true) :
    fo + 4 * ws.length ≤ blk.code.length := by
  simp only [Obj.CodeBlock.checkSegment, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨_, hpos⟩, _⟩, _⟩, hwords⟩ := hchk
  have ⟨hlen, _⟩ := Obj.CodeBlock.segWordsOk_spec hwords
  rw [List.length_drop] at hlen
  omega

theorem muslStringProg_hasWords_of_checkSegment
    {pl : Obj.Placement} {hooks : String → Option (State → State)}
    {name : String} {fo : Nat} {ws : List (BitVec 32)} {R : List Obj.RelocEntry}
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (hsym : Obj.lookup name VerifiedLibraries.muslStringLib.text.symbols = some fo)
    (hchk : VerifiedLibraries.muslStringLib.text.checkSegment fo ws R = true) :
    let prog := muslStringProg pl hooks
    prog.hasWords (prog.fnAddr name)
        (Obj.patchRelocs R ws (prog.fnAddr name)
          (VerifiedLibraries.muslStringLib.text.resolve pl)) ∧
      ∀ r ∈ R, Obj.CodeRelocInRange r.kind
        (prog.fnAddr name + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (VerifiedLibraries.muslStringLib.text.resolve pl r.sym) r.addend) := by
  dsimp only
  rw [muslStringProg_fnAddr hsym]
  exact Obj.CodeBlock.hasWords_of_checkSegment hP.text
    (Obj.PlacedLib.program_base VerifiedLibraries.muslStringLib pl)
    (Obj.PlacedLib.program_code VerifiedLibraries.muslStringLib pl)
    hchk (Obj.PlacedLib.hookFree_program_noOverrides hP.text (len_le_of_checkSegment hchk))

theorem muslStringProg_hasWords_relocFree
    {pl : Obj.Placement} {hooks : String → Option (State → State)}
    {name : String} {fo : Nat} {ws : List (BitVec 32)}
    (hP : VerifiedLibraries.muslStringLib.Placeable pl)
    (hsym : Obj.lookup name VerifiedLibraries.muslStringLib.text.symbols = some fo)
    (hchk : VerifiedLibraries.muslStringLib.text.checkSegment fo ws [] = true) :
    (muslStringProg pl hooks).hasWords ((muslStringProg pl hooks).fnAddr name) ws := by
  have ⟨hw, _⟩ := muslStringProg_hasWords_of_checkSegment (hooks := hooks) hP hsym hchk
  simpa [Obj.patchRelocs] using hw

abbrev memcpyWords : List (BitVec 32) := memcpySymWords

abbrev memsetWords : List (BitVec 32) := memsetWordsSym

def bcmpWords : List (BitVec 32) := [0x17fffff6#32]

abbrev bcmpCalls : List (Nat × String) := [(0, "memcmp")]

def bcmpLibcaRelocs : List Obj.RelocEntry :=
  [{ off := 0, kind := .jump26, sym := "memcmp", addend := 0 }]

def memcmpWords : List (BitVec 32) := [
  0xb40000e2#32, 0x38401408#32, 0x38401429#32, 0x6b090108#32, 0x54000081#32, 0xf1000442#32,
  0x54ffff61#32, 0x2a1f03e8#32, 0x2a0803e0#32, 0xd65f03c0#32]

def memcmpLibcaWords : List (BitVec 32) := [
  0xd1000421#32, 0xd2800003#32, 0xeb02007f#32, 0x54000100#32, 0x38636804#32, 0x91000463#32,
  0x38636825#32, 0x6b05009f#32, 0x54ffff40#32, 0x4b050080#32, 0x14000002#32, 0x52800000#32,
  0xd65f03c0#32]

def mempcpyLibcaWords : List (BitVec 32) := [
  0xa9be7bfd#32, 0x910003fd#32, 0xf9000bf3#32, 0xaa0203f3#32, 0x94000000#32, 0x8b130000#32,
  0xf9400bf3#32, 0xa8c27bfd#32, 0xd65f03c0#32]

abbrev mempcpyCalls : List (Nat × String) := [(16, "memcpy")]

def mempcpyLibcaRelocs : List Obj.RelocEntry :=
  [{ off := 16, kind := .call26, sym := "memcpy", addend := 0 }]

def memrchrLibcaWords : List (BitVec 32) := [
  0xd1000442#32, 0xd1000404#32, 0x8b020002#32, 0x12001c21#32, 0xaa0203e0#32, 0xeb04005f#32,
  0x540000c0#32, 0x39400003#32, 0xd1000442#32, 0x6b01007f#32, 0x54ffff41#32, 0x14000002#32,
  0xd2800000#32, 0xd65f03c0#32]

def memchrLibcaWords : List (BitVec 32) := [
  0xaa0003e3#32, 0x12001c21#32, 0x14000003#32, 0x91000463#32, 0xd1000442#32, 0xf240087f#32,
  0x54000100#32, 0xb40004e2#32, 0x39400060#32, 0x6b01001f#32, 0x54ffff21#32, 0x8b020062#32,
  0xaa0303e0#32, 0x1400001b#32, 0xd2800000#32, 0xb40003c2#32, 0x39400060#32, 0x6b01001f#32,
  0x54ffff20#32, 0x93407c26#32, 0xb200c3e0#32, 0x927df045#32, 0xb207dbe8#32, 0x8b020067#32,
  0x8b050065#32, 0x9b007cc6#32, 0xf29fdfe8#32, 0x14000002#32, 0x91002063#32, 0xeb05007f#32,
  0xcb0300e2#32, 0x54fffd80#32, 0xf9400060#32, 0xca0000c0#32, 0x8b080004#32, 0x8a200080#32,
  0xf201c01f#32, 0x54fffee0#32, 0x17ffffe5#32, 0x91000400#32, 0xeb02001f#32, 0x540000a0#32,
  0x39400003#32, 0x6b01007f#32, 0x54ffff61#32, 0xd65f03c0#32, 0xd2800000#32, 0x17fffffe#32]

def memccpyLibcaWords : List (BitVec 32) := [
  0xca000024#32, 0x12001c42#32, 0xf240089f#32, 0x54000301#32, 0xf240083f#32, 0x540003e0#32,
  0xb4000103#32, 0x39400024#32, 0xd1000463#32, 0x38001404#32, 0x91000421#32, 0x6b02009f#32,
  0x54ffff01#32, 0x14000002#32, 0xd2800000#32, 0xd65f03c0#32, 0xd1002063#32, 0x91002021#32,
  0xf8008405#32, 0xeb08007f#32, 0x540000e0#32, 0xf9400025#32, 0xca0700a4#32, 0x8b090086#32,
  0x8a2400c4#32, 0xf201c09f#32, 0x54fffec0#32, 0x8b030003#32, 0xeb03001f#32, 0x54fffe20#32,
  0x39400024#32, 0x91000421#32, 0x38001404#32, 0x6b02009f#32, 0x54ffff41#32, 0x17ffffec#32,
  0x93407c47#32, 0xb200c3e4#32, 0xb207dbe9#32, 0x92400868#32, 0xf29fdfe9#32, 0x9b047ce7#32,
  0x17ffffe9#32]

def memmoveLibcaWords : List (BitVec 32) := [
  0xaa0003e7#32, 0xaa0103e4#32, 0xeb01001f#32, 0xaa0203e3#32, 0x54000880#32, 0xcb020025#32,
  0xcb0207e6#32, 0xcb0000a8#32, 0xeb06011f#32, 0x54000229#32, 0xca000021#32, 0xeb04001f#32,
  0x92400821#32, 0x54000442#32, 0xb5000321#32, 0x8b0204a2#32, 0x8b030083#32, 0xaa0003e1#32,
  0xcb040040#32, 0xf2400825#32, 0x540000e0#32, 0xeb03009f#32, 0x54000640#32, 0x38401485#32,
  0x38001425#32, 0x17fffff9#32, 0x14000000#32, 0xd343fc03#32, 0x927df006#32, 0x14000004#32,
  0xf8656882#32, 0xf8256822#32, 0x910020a5#32, 0xeb0600bf#32, 0x54ffff81#32, 0xcb030c03#32,
  0x8b050022#32, 0x8b050084#32, 0x14000002#32, 0xaa0003e2#32, 0xd2800001#32, 0xeb01007f#32,
  0x540003c0#32, 0x38616885#32, 0x38216845#32, 0x91000421#32, 0x17fffffb#32, 0xb40000c1#32,
  0xb4000303#32, 0xd1000463#32, 0x38636881#32, 0x382368e1#32, 0x17fffffc#32, 0x8b0300e1#32,
  0xd1000462#32, 0xf240083f#32, 0x540000c0#32, 0xb40001e3#32, 0x38626881#32, 0xaa0203e3#32,
  0x382268e1#32, 0x17fffff8#32, 0x92400862#32, 0xaa0303e1#32, 0x14000003#32, 0xf8616880#32,
  0xf82168e0#32, 0xeb02003f#32, 0xd1002021#32, 0x54ffff81#32, 0x92400863#32, 0x17ffffe9#32,
  0xaa0703e0#32, 0xd65f03c0#32]

abbrev memmoveLibcaCalls : List (Nat × String) := [(104, "memcpy")]

def memmoveLibcaRelocs : List Obj.RelocEntry :=
  [{ off := 104, kind := .jump26, sym := "memcpy", addend := 0 }]

def memmemLibcaWords : List (BitVec 32) := [
  0xa9bd7bfd#32, 0x910003fd#32, 0xa9025bf5#32, 0xaa0003f5#32, 0xb4000cc3#32, 0xa90153f3#32,
  0xeb01007f#32, 0xaa0103f3#32, 0xaa0303f4#32, 0x54000948#32, 0x39400041#32, 0xaa0203f6#32,
  0xaa1303e2#32, 0x94000000#32, 0xf100001f#32, 0xaa0003e1#32, 0xfa411a84#32, 0x54000bc0#32,
  0xcb150015#32, 0xcb150273#32, 0xeb13029f#32, 0x540007c8#32, 0xf1000a9f#32, 0x54000180#32,
  0xf1000e9f#32, 0x540003e0#32, 0xf100129f#32, 0x54000760#32, 0xaa1403e3#32, 0xaa1603e2#32,
  0x8b130001#32, 0xa94153f3#32, 0xa9425bf5#32, 0xa8c37bfd#32, 0x14000000#32, 0x39400005#32,
  0x8b130003#32, 0x394002c6#32, 0x91000802#32, 0x394006c4#32, 0x39400400#32, 0x33185cc4#32,
  0x33185ca0#32, 0xeb03005f#32, 0x540000e0#32, 0x6b00009f#32, 0x540000e0#32, 0x38401441#32,
  0x2a002020#32, 0x12003c00#32, 0x17fffff9#32, 0x6b00009f#32, 0x540003e1#32, 0xd1000841#32,
  0xa94153f3#32, 0x14000034#32, 0x39400ac4#32, 0xaa0003e2#32, 0x39400800#32, 0x8b130023#32,
  0x394006c5#32, 0x39400421#32, 0x53185c87#32, 0x53185c06#32, 0x394002c4#32, 0x38403440#32,
  0x2a0540e5#32, 0x2a0140c1#32, 0x2a0460a4#32, 0x2a006020#32, 0x14000004#32, 0x38401441#32,
  0x2a000020#32, 0x53185c00#32, 0xeb03005f#32, 0x540000c0#32, 0x6b00009f#32, 0x54ffff41#32,
  0xd1000c41#32, 0xa94153f3#32, 0x1400001b#32, 0x6b00009f#32, 0x54ffff80#32, 0xd2800001#32,
  0xa94153f3#32, 0x14000016#32, 0xb94002c3#32, 0x8b130013#32, 0xb8404420#32, 0x5ac00863#32,
  0x5ac00800#32, 0xeb01027f#32, 0x54000120#32, 0x6b00007f#32, 0x54000080#32, 0x38401422#32,
  0x2a002040#32, 0x17fffffa#32, 0xd1001021#32, 0xa94153f3#32, 0x14000007#32, 0x6b00007f#32,
  0x54fffda1#32, 0xd1001261#32, 0xa94153f3#32, 0x14000002#32, 0xaa0003e1#32, 0xaa0103e0#32,
  0xa9425bf5#32, 0xa8c37bfd#32, 0xd65f03c0#32, 0xa94153f3#32, 0x17fffffb#32]

def memmemLibcaRelocs : List Obj.RelocEntry :=
  [{ off := 52, kind := .call26, sym := "memchr", addend := 0 },
   { off := 136, kind := .jump26, sym := "twoway_memmem [musl_string_libca]", addend := 0 }]

end VerifiedLibraries.Musl
