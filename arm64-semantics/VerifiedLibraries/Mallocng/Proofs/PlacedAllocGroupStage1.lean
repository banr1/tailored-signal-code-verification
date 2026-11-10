/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupHelpers3

/-!
# Placed `alloc_group` Stage 1 Helpers

Defines the plain code segments, instruction-offset abbreviations, `.rodata` table splits, and
`wp_publish_new_group` for `alloc_slot` (`blk08`) on `mallocngBlockProg mmpl 8 msvc`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## `blk08` Code Segments and Instruction Offsets -/

def blk08Words : List (BitVec 32) := [
  0xa9ba7bfd#32, 0x910003fd#32, 0xa90363f7#32, 0x93407c17#32, 0xa9025bf5#32, 0x90000016#32, 0x910002c3#32, 0xa9046bf9#32, 0xaa0103f9#32, 0x91002ae1#32,
  0xaa1703f5#32, 0xf8617862#32, 0xb4001242#32, 0xb9401840#32, 0x35000e80#32, 0xa90153f3#32, 0xa90573fb#32, 0xb9401c44#32, 0xf9400440#32, 0x350002a4#32,
  0xeb00005f#32, 0x54000220#32, 0xf9400044#32, 0xf9000480#32, 0xa9400044#32, 0xf9000004#32, 0xf8617860#32, 0xeb00005f#32, 0x540000e0#32, 0x910002c0#32,
  0x91002ae1#32, 0xa9007c5f#32, 0xf8617802#32, 0xb5000122#32, 0x1400007e#32, 0xf9400440#32, 0xf8217860#32, 0x17fffff8#32, 0xf821787f#32, 0x17fffff6#32,
  0xaa0003e2#32, 0xf8217860#32, 0x39408041#32, 0x52800040#32, 0xb9401c44#32, 0xd3401023#32, 0x1ac32000#32, 0x51000400#32, 0x6b00009f#32, 0x54000380#32,
  0xf9400845#32, 0x52800040#32, 0x394020a1#32, 0x12001023#32, 0xd3401021#32, 0x1ac12000#32, 0x51000400#32, 0x6a04001f#32, 0x54000101#32, 0xf9400444#32,
  0xeb04005f#32, 0x540002e0#32, 0x910002c0#32, 0x91002ae1#32, 0xaa0403e2#32, 0xf8217804#32, 0xb9401840#32, 0x350020e0#32, 0xf9400840#32, 0x52800043#32,
  0x91007045#32, 0x39402000#32, 0xd3401000#32, 0x1ac02063#32, 0x51000460#32, 0x4b0303e3#32, 0x14000025#32, 0x362ffca1#32, 0x910002c0#32, 0x91002ae1#32,
  0xf9400442#32, 0xf8217802#32, 0xb9401c44#32, 0x17ffffdf#32, 0x79404081#32, 0x90000000#32, 0x91000000#32, 0x11000863#32, 0xd3462c21#32, 0x78617806#32,
  0x531c6cc6#32, 0x1b067c60#32, 0x11004001#32, 0x14000003#32, 0x11000463#32, 0x2a0203e1#32, 0x0b0100c2#32, 0x51000440#32, 0x4a010000#32, 0x713ffc1f#32,
  0x54ffff4d#32, 0x39408080#32, 0xaa0403e2#32, 0x394020a1#32, 0x12001000#32, 0x11000400#32, 0x6b03001f#32, 0x1a83d000#32, 0x51000400#32, 0x33001001#32,
  0x390020a1#32, 0x17ffffd3#32, 0xd5033bbf#32, 0xb9401c41#32, 0x0a030024#32, 0x885ffca6#32, 0x6b06003f#32, 0x54ffff61#32, 0x8806fca4#32, 0x35ffff86#32,
  0x0a010000#32, 0xb9001840#32, 0x34001a00#32, 0x79404041#32, 0xd3462c21#32, 0x51001c21#32, 0x71007c3f#32, 0x540002c9#32, 0xa94153f3#32, 0xa94573fb#32,
  0x4b0003e3#32, 0x0a230001#32, 0xb9001841#32, 0x6a000060#32, 0x54000300#32, 0x4b0003e3#32, 0x529cc522#32, 0x0a000060#32, 0x72a0ed62#32, 0x90000001#32,
  0x91000021#32, 0x1b027c00#32, 0x531b7c00#32, 0x38604820#32, 0xa9425bf5#32, 0xa94363f7#32, 0xa9446bf9#32, 0xa8c67bfd#32, 0xd65f03c0#32, 0x910002c3#32,
  0x8b21c061#32, 0x394dc023#32, 0x34fffd03#32, 0x51000463#32, 0x390dc023#32, 0xa94153f3#32, 0xa94573fb#32, 0x17ffffe5#32, 0xa90153f3#32, 0xa90573fb#32,
  0x9000001a#32, 0x91000340#32, 0x78777801#32, 0x531c6c3b#32, 0xd37c3c38#32, 0x94000000#32, 0xaa0003f3#32, 0xb4003460#32, 0x910002c0#32, 0x9100eae1#32,
  0x90000002#32, 0x710022bf#32, 0xf9400044#32, 0xf8617802#32, 0x540001ec#32, 0x8b1706e0#32, 0x90000001#32, 0x91000021#32, 0x8b000023#32, 0x38606834#32,
  0xd37e1e80#32, 0xeb02001f#32, 0x540002e9#32, 0x39400474#32, 0xd37e1e80#32, 0xeb00005f#32, 0x54000262#32, 0x39400874#32, 0x14000011#32, 0x120006a1#32,
  0x90000000#32, 0x91000000#32, 0x3861c814#32, 0x14000002#32, 0x13017e94#32, 0x37000094#32, 0x531e7680#32, 0xeb20c05f#32, 0x54ffff83#32, 0xb2404fe1#32,
  0x14000002#32, 0x13017e94#32, 0x9b347f60#32, 0xeb01001f#32, 0x54ffffa8#32, 0x93407e9c#32, 0x7100069f#32, 0xd341fc81#32, 0x54000380#32, 0x9b1c7f00#32,
  0x91004003#32, 0xeb01007f#32, 0x540018a9#32, 0x531e7686#32, 0x93407cc6#32, 0x910002c5#32, 0x51001ea3#32, 0x71007c7f#32, 0x394e40a1#32, 0x54000348#32,
  0x8b23c0a3#32, 0x394d4069#32, 0x394dc068#32, 0x71018d1f#32, 0x1a9f97e5#32, 0x1a9f87e7#32, 0x340002a9#32, 0x4b090029#32, 0x7100253f#32, 0x5400024c#32,
  0x71018d1f#32, 0x11000508#32, 0x12800d29#32, 0x1a882128#32, 0x390dc068#32, 0x1400000c#32, 0x91004300#32, 0xeb01001f#32, 0x54000088#32, 0xd280005c#32,
  0x2a1c03f4#32, 0x17ffffe0#32, 0xaa1803e0#32, 0xd2800086#32, 0x17ffffe3#32, 0x52800027#32, 0x52800005#32, 0x910002c3#32, 0x7103fc3f#32, 0x54000a80#32,
  0x11000421#32, 0x390e4061#32, 0x71007ebf#32, 0x1a9fc7e1#32, 0x6a35003f#32, 0x54000ae1#32, 0x710000ff#32, 0xfa461042#32, 0x54000b43#32, 0x9b347f7b#32,
  0x71001e9f#32, 0xd1000483#32, 0x928001fa#32, 0xcb1b035a#32, 0x520000a1#32, 0x1a9fc7e0#32, 0x9100437b#32, 0x8a03035a#32, 0x6a01001f#32, 0x8b1b035a#32,
  0x54000d61#32, 0xaa1a03e1#32, 0xd2800005#32, 0x12800004#32, 0x52800443#32, 0x52800062#32, 0xd2800000#32, 0x94000000#32, 0xb100041f#32, 0x54000ea0#32,
  0xd281fe02#32, 0xd34cff5a#32, 0xf9401263#32, 0x910002c4#32, 0x9ad80841#32, 0x51000682#32, 0x93407e9c#32, 0xb374cf43#32, 0xf9001263#32, 0x51000421#32,
  0xb9400c83#32, 0x6b14003f#32, 0x1a82b021#32, 0x11000463#32, 0x7100003f#32, 0xb9000c83#32, 0x1a9fa021#32, 0x910002d6#32, 0x9100eae6#32, 0x52800043#32,
  0x120016b5#32, 0x1ac12064#32, 0x51000484#32, 0xf8667ac5#32, 0x1ac22063#32, 0x12001042#32, 0x8b1c00bc#32, 0xf8267adc#32, 0xb9001a64#32, 0x321b0042#32,
  0xf9000a60#32, 0x2a151842#32, 0xb9401a64#32, 0x2a2403e4#32, 0x0b040063#32, 0xb9001e63#32, 0xf9000013#32, 0xf9400a60#32, 0x39402003#32, 0x33001023#32,
  0x39002003#32, 0x79404275#32, 0xb9401a60#32, 0xf9400661#32, 0x12144eb5#32, 0x2a150042#32, 0x51000400#32, 0xb9001a60#32, 0x79004262#32, 0xb4001d41#32,
  0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0x910d4061#32, 0x910dc063#32, 0x3800143f#32, 0xeb01007f#32, 0x54ffffc1#32, 0x910002c1#32, 0x52800023#32,
  0x390e4023#32, 0x17ffffa7#32, 0x110006a1#32, 0x910002c3#32, 0x8b21cc61#32, 0xf940e821#32, 0x8b010042#32, 0x17ffffa5#32, 0x120006a1#32, 0x7100043f#32,
  0x54000160#32, 0x7100083f#32, 0x540001c0#32, 0x35fff441#32, 0xeb040c1f#32, 0x540001a8#32, 0xeb04041f#32, 0x54fff3c9#32, 0xd28000a0#32, 0x2a0003f4#32,
  0x1400000a#32, 0xeb040c1f#32, 0x54fff329#32, 0xd2800040#32, 0x2a0003f4#32, 0x14000005#32, 0xeb04081f#32, 0x54fff289#32, 0xd2800060#32, 0x2a0003f4#32,
  0x9b007f00#32, 0xd1000483#32, 0x928001fa#32, 0xcb00035a#32, 0x91004000#32, 0x8a03035a#32, 0x8b00035a#32, 0x92800260#32, 0xcb190000#32, 0x8a030000#32,
  0x91005339#32, 0x8b190019#32, 0x91004300#32, 0xeb00033f#32, 0x54000123#32, 0xeb040b3f#32, 0x54fff1a3#32, 0x531f7a80#32, 0x93407c00#32, 0xeb00005f#32,
  0x9a99235a#32, 0x1a9f2694#32, 0x17ffff87#32, 0xaa1903fa#32, 0x52800034#32, 0x17ffff84#32, 0x910002d6#32, 0xa9007e7f#32, 0xa9017e7f#32, 0xf9400ac1#32,
  0xf900127f#32, 0xb4000061#32, 0xf9000661#32, 0x140000a9#32, 0xa9004e73#32, 0xf9000ad3#32, 0xa94153f3#32, 0xa94573fb#32, 0x17fffef8#32, 0xf102401f#32,
  0x91003001#32, 0xd344fc19#32, 0x540003a9#32, 0x91000720#32, 0x529cc525#32, 0x72a0ed65#32, 0x90000004#32, 0x53027c02#32, 0x91000084#32, 0x2a400442#32,
  0x91000343#32, 0x2a420842#32, 0x2a421042#32, 0x2a422042#32, 0x2a424042#32, 0x11000446#32, 0x0a2200c2#32, 0x1b057c42#32, 0x531b7c42#32, 0x38624899#32,
  0xaa0303e2#32, 0x51000739#32, 0x531e7739#32, 0x11000725#32, 0x11000b24#32, 0x7865d863#32, 0xeb03001f#32, 0x1a998099#32, 0x7879d842#32, 0xeb02001f#32,
  0x1a999739#32, 0x2a1903e0#32, 0x97fffe46#32, 0x2a0003e1#32, 0x37f80280#32, 0x93407f39#32, 0x910002c0#32, 0x91002b24#32, 0x91000343#32, 0xb9400c02#32,
  0xf8647807#32, 0x78797865#32, 0x394080e0#32, 0x531c6ca5#32, 0x510010a5#32, 0xf240101f#32, 0x93407ca3#32, 0x540002c1#32, 0xf94010e0#32, 0xf274cc1f#32,
  0x54000260#32, 0x9274cc00#32, 0xd1004006#32, 0x14000015#32, 0x910002d6#32, 0xa9007e7f#32, 0xa9017e7f#32, 0xf9400ac1#32, 0xf900127f#32, 0xb4000081#32,
  0x12800000#32, 0xf9000661#32, 0x14000064#32, 0xa9004e73#32, 0x12800000#32, 0xf9000ad3#32, 0xa94153f3#32, 0xa94573fb#32, 0x17fffeb2#32, 0x794040e0#32,
  0x9100035a#32, 0xd3462c00#32, 0x78607b40#32, 0xd37c3c06#32, 0xf94008e4#32, 0x93407c20#32, 0xcb0300c3#32, 0xd10010c8#32, 0x91004084#32, 0xd1001063#32,
  0x12001c42#32, 0xd344fc69#32, 0x9b061000#32, 0x8b080008#32, 0x385fd006#32, 0x34000086#32, 0x785fe002#32, 0x11000442#32, 0x12001c42#32, 0x385fc006#32,
  0x35ffeac6#32, 0xeb22c13f#32, 0x54000182#32, 0xaa431523#32, 0x2a2903ea#32, 0xaa430863#32, 0xaa431063#32, 0x0a03004b#32, 0x0a030042#32, 0xeb02013f#32,
  0x0b0a0162#32, 0x1a8b3042#32, 0xeb22c13f#32, 0x54ffe923#32, 0x34000122#32, 0x531c6c43#32, 0x128003e4#32, 0x381fd004#32, 0x781fe002#32, 0x8b23c000#32,
  0x381fc01f#32, 0xf94008e4#32, 0x91004084#32, 0xcb040004#32, 0x12001c21#32, 0x381fd001#32, 0xcb000103#32, 0xd344fc84#32, 0x781fe004#32, 0x6b050065#32,
  0x54000120#32, 0x4b0503e1#32, 0x710010bf#32, 0x3821c91f#32, 0x5400034d#32, 0x381fb11f#32, 0x52801406#32, 0xb81fc105#32, 0x385fd001#32, 0x12001022#32,
  0x11000683#32, 0x0b0200c2#32, 0x381fd002#32, 0x91003001#32, 0x52800002#32, 0xf9401264#32, 0x92402c84#32, 0xf9001264#32, 0x385fd004#32, 0x12001084#32,
  0x321a6484#32, 0x381fd004#32, 0x3900003f#32, 0x11000442#32, 0x6b03005f#32, 0x8b180021#32, 0x54ffff81#32, 0x51000682#32, 0x2a0203e1#32, 0x17fffefa#32,
  0x385fd001#32, 0x531b08a6#32, 0x17ffffe9#32, 0xf9400260#32, 0xb4000060#32, 0x3900003f#32, 0xd4207d00#32, 0x91002af7#32, 0xf8777ac1#32, 0xb4000161#32,
  0x52800000#32, 0xf9000661#32, 0xf9400021#32, 0xf9000261#32, 0xf9000433#32, 0xf9400661#32, 0xf9000033#32, 0xa94153f3#32, 0xa94573fb#32, 0x17fffe4d#32,
  0xa9004e73#32, 0x52800000#32, 0xf8377ad3#32, 0xa94153f3#32, 0xa94573fb#32, 0x17fffe47#32, 0x12800000#32, 0xa94153f3#32, 0xa94573fb#32, 0x17fffe43#32]

def blk08Words0 : List (BitVec 32) := blk08Words.take 85
def blk08Relocs0 : List Obj.RelocEntry :=
  VerifiedLibraries.mallocng_blk08_alloc_slot.segRelocs 0 (4 * 85)

def blk08Words348 : List (BitVec 32) := (blk08Words.drop 87).take 52
def blk08Relocs348 : List Obj.RelocEntry :=
  VerifiedLibraries.mallocng_blk08_alloc_slot.segRelocs 348 (4 * 52)

def blk08Words564 : List (BitVec 32) := (blk08Words.drop 141).take 35
def blk08Relocs564 : List Obj.RelocEntry :=
  VerifiedLibraries.mallocng_blk08_alloc_slot.segRelocs 564 (4 * 35)

def blk08Words712 : List (BitVec 32) := (blk08Words.drop 178).take 12
def blk08Relocs712 : List Obj.RelocEntry :=
  VerifiedLibraries.mallocng_blk08_alloc_slot.segRelocs 712 (4 * 12)

def blk08Words768 : List (BitVec 32) := blk08Words.drop 192
def blk08Relocs768 : List Obj.RelocEntry :=
  VerifiedLibraries.mallocng_blk08_alloc_slot.segRelocs 768 (4 * 398)

macro "Blk08HasWords0" svc:term : term =>
  `(((mallocngBlockProg mmpl 8 msvc).withSvc $svc).hasWords (mbase 8)
      (Obj.patchRelocs blk08Relocs0 blk08Words0 (mbase 8) (VerifiedLibraries.mallocngLib.resolve mmpl)))

macro "Blk08Range0" : term =>
  `(∀ r ∈ blk08Relocs0, Obj.CodeRelocInRange r.kind
      (mbase 8 + BitVec.ofNat 64 r.off)
      (Obj.addSignedAddr (VerifiedLibraries.mallocngLib.resolve mmpl r.sym) r.addend))

macro "Blk08HasWords348" svc:term : term =>
  `(((mallocngBlockProg mmpl 8 msvc).withSvc $svc).hasWords (mbase 8 + 348#64)
      (Obj.patchRelocs blk08Relocs348 blk08Words348 (mbase 8 + 348#64) (VerifiedLibraries.mallocngLib.resolve mmpl)))

macro "Blk08Range348" : term =>
  `(∀ r ∈ blk08Relocs348, Obj.CodeRelocInRange r.kind
      (mbase 8 + 348#64 + BitVec.ofNat 64 r.off)
      (Obj.addSignedAddr (VerifiedLibraries.mallocngLib.resolve mmpl r.sym) r.addend))

macro "Blk08HasWords564" svc:term : term =>
  `(((mallocngBlockProg mmpl 8 msvc).withSvc $svc).hasWords (mbase 8 + 564#64)
      (Obj.patchRelocs blk08Relocs564 blk08Words564 (mbase 8 + 564#64) (VerifiedLibraries.mallocngLib.resolve mmpl)))

macro "Blk08Range564" : term =>
  `(∀ r ∈ blk08Relocs564, Obj.CodeRelocInRange r.kind
      (mbase 8 + 564#64 + BitVec.ofNat 64 r.off)
      (Obj.addSignedAddr (VerifiedLibraries.mallocngLib.resolve mmpl r.sym) r.addend))

macro "Blk08HasWords712" svc:term : term =>
  `(((mallocngBlockProg mmpl 8 msvc).withSvc $svc).hasWords (mbase 8 + 712#64)
      (Obj.patchRelocs blk08Relocs712 blk08Words712 (mbase 8 + 712#64) (VerifiedLibraries.mallocngLib.resolve mmpl)))

macro "Blk08Range712" : term =>
  `(∀ r ∈ blk08Relocs712, Obj.CodeRelocInRange r.kind
      (mbase 8 + 712#64 + BitVec.ofNat 64 r.off)
      (Obj.addSignedAddr (VerifiedLibraries.mallocngLib.resolve mmpl r.sym) r.addend))

macro "Blk08HasWords768" svc:term : term =>
  `(((mallocngBlockProg mmpl 8 msvc).withSvc $svc).hasWords (mbase 8 + 768#64)
      (Obj.patchRelocs blk08Relocs768 blk08Words768 (mbase 8 + 768#64) (VerifiedLibraries.mallocngLib.resolve mmpl)))

macro "Blk08Range768" : term =>
  `(∀ r ∈ blk08Relocs768, Obj.CodeRelocInRange r.kind
      (mbase 8 + 768#64 + BitVec.ofNat 64 r.off)
      (Obj.addSignedAddr (VerifiedLibraries.mallocngLib.resolve mmpl r.sym) r.addend))

theorem blk08_segments_noSyscalls [MallocngMultiPlacement] :
    ((Blk08HasWords0 mallocngFaultSvc) ∧ Blk08Range0) ∧
    ((Blk08HasWords348 mallocngFaultSvc) ∧ Blk08Range348) ∧
    ((Blk08HasWords564 mallocngFaultSvc) ∧ Blk08Range564) ∧
    ((Blk08HasWords712 mallocngFaultSvc) ∧ Blk08Range712) ∧
    ((Blk08HasWords768 mallocngFaultSvc) ∧ Blk08Range768) := by
  have ⟨hw0, hr0⟩ := hasWords_blk_seg0 (i := 8) (by decide)
    (ws := blk08Words0) (R := blk08Relocs0) (by decide +kernel)
  have ⟨hw348, hr348⟩ := hasWords_blk_seg (i := 8) (by decide) 348
    (ws := blk08Words348) (R := blk08Relocs348) (by decide +kernel)
  have ⟨hw564, hr564⟩ := hasWords_blk_seg (i := 8) (by decide) 564
    (ws := blk08Words564) (R := blk08Relocs564) (by decide +kernel)
  have ⟨hw712, hr712⟩ := hasWords_blk_seg (i := 8) (by decide) 712
    (ws := blk08Words712) (R := blk08Relocs712) (by decide +kernel)
  have ⟨hw768, hr768⟩ := hasWords_blk_seg (i := 8) (by decide) 768
    (ws := blk08Words768) (R := blk08Relocs768) (by decide +kernel)
  exact ⟨⟨Program.hasWords_withSvc hw0, hr0⟩,
    ⟨Program.hasWords_withSvc hw348, hr348⟩,
    ⟨Program.hasWords_withSvc hw564, hr564⟩,
    ⟨Program.hasWords_withSvc hw712, hr712⟩,
    ⟨Program.hasWords_withSvc hw768, hr768⟩⟩

abbrev blk08Relocs : List Obj.RelocEntry := VerifiedLibraries.mallocng_blk08_alloc_slot.relocs

abbrev allocSlotOff_epi : BitVec 64 := words_insn_off% blk08Words 0xa9425bf5#32
abbrev allocSlotOff_ret : BitVec 64 := words_ret_off% blk08Words
abbrev allocSlotOff_ag_stp : BitVec 64 := words_insn_off% blk08Words 0xa90153f3#32 1
abbrev allocSlotOff_ag : BitVec 64 := words_insn_off% blk08Words 0x9000001a#32
abbrev allocSlotOff_call_meta : BitVec 64 := reloc_call_off% blk08Relocs "__malloc_alloc_meta"
abbrev allocSlotOff_after_meta : BitVec 64 := words_insn_off% blk08Words 0xaa0003f3#32
abbrev allocSlotOff_cnt1 : BitVec 64 := words_insn_off% blk08Words 0x37000094#32
abbrev allocSlotOff_cnt2 : BitVec 64 := words_insn_off% blk08Words 0x9b347f60#32
abbrev allocSlotOff_cnt_join : BitVec 64 := words_insn_off% blk08Words 0x93407e9c#32 0
abbrev allocSlotOff_cnt_check : BitVec 64 := words_insn_off% blk08Words 0x9b1c7f00#32
abbrev allocSlotOff_root : BitVec 64 := words_insn_off% blk08Words 0x910002c5#32
abbrev allocSlotOff_seq_join : BitVec 64 := words_insn_off% blk08Words 0x910002c3#32 2
abbrev allocSlotOff_unmap_loop : BitVec 64 := words_insn_off% blk08Words 0x3800143f#32
abbrev allocSlotOff_bounces_cap : BitVec 64 := words_insn_off% blk08Words 0x710000ff#32
abbrev allocSlotOff_mmap_prep : BitVec 64 := words_insn_off% blk08Words 0x9b347f7b#32
abbrev allocSlotOff_mmap_go : BitVec 64 := words_insn_off% blk08Words 0xaa1a03e1#32
abbrev allocSlotOff_call_mmap : BitVec 64 := reloc_call_off% blk08Relocs "__mmap"
abbrev allocSlotOff_after_mmap : BitVec 64 := words_insn_off% blk08Words 0xb100041f#32
abbrev allocSlotOff_pub_add : BitVec 64 := words_insn_off% blk08Words 0x910002d6#32 0
abbrev allocSlotOff_nested : BitVec 64 := words_insn_off% blk08Words 0xf102401f#32
abbrev allocSlotOff_call_self : BitVec 64 := words_insn_off% blk08Words "bl" 2
abbrev allocSlotOff_after_self : BitVec 64 := words_insn_off% blk08Words 0x2a0003e1#32
abbrev allocSlotOff_enframe_hdr : BitVec 64 := words_insn_off% blk08Words 0xf94008e4#32 0
abbrev allocSlotOff_enframe_idx : BitVec 64 := words_insn_off% blk08Words 0xcb040004#32
abbrev allocSlotOff_enframe_fin : BitVec 64 := words_insn_off% blk08Words 0x12001022#32
abbrev allocSlotOff_zero_loop : BitVec 64 := words_insn_off% blk08Words 0x3900003f#32 0
abbrev allocSlotOff_req_round : BitVec 64 := words_insn_off% blk08Words 0x92800260#32
abbrev allocSlotOff_cnt_mul : BitVec 64 := words_insn_off% blk08Words 0x9b007f00#32

/-! ## Publish-Group Helpers and `wp_publish_new_group` -/

private theorem pub_avail_eq {idx : Nat} (h : idx ≤ 31) :
    2#32 <<< ((BitVec.setWidth 32 (BitVec.ofNat 64 idx)).toNat % 32) =
      2#32 <<< BitVec.ofNat 32 idx := by
  have hw : BitVec.setWidth 32 (BitVec.ofNat 64 idx) = BitVec.ofNat 32 idx := by bv_omega
  have hi : (BitVec.ofNat 32 idx).toNat = idx := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [hw, BitVec.shiftLeft_eq', hi, Nat.mod_eq_of_lt (by omega)]

private theorem pub_not32 (x : BitVec 32) :
    BitVec.setWidth 32 (~~~BitVec.setWidth 64 x) = ~~~x := by bv_robdd

private theorem pub_packed_parts (vL vS vM m5 m12 : BitVec 64)
    (hm5 : m5 = 32#64 ||| (32#64 <<< 32))
    (hm12 : m12 = (~~~0xfff#32).zeroExtend 64 ||| ((~~~0xfff#32).zeroExtend 64 <<< 32)) :
    let w64 := vM <<< 12
    let p := (vL &&& 0x1f#64) ||| (1#64 <<< 5) ||| ((vS &&& 0x3f#64) <<< 6) ||| w64
    BitVec.truncate 16
      (BitVec.setWidth 32 (BitVec.zeroExtend 64 (BitVec.setWidth 32 vL) &&& 31#64 ||| m5) |||
       BitVec.setWidth 32 (BitVec.zeroExtend 64 (BitVec.setWidth 32 vS) &&& 63#64) <<< 6 |||
       BitVec.setWidth 32 (BitVec.zeroExtend 64 (w64.extractLsb' 0 16) &&& m12)) =
      p.extractLsb' 0 16 ∧
    w64.extractLsb' 16 16 = p.extractLsb' 16 16 ∧
    w64.extractLsb' 32 32 = p.extractLsb' 32 32 := by
  subst hm5 hm12; dsimp only; refine ⟨by bv_robdd, by bv_robdd, by bv_robdd⟩

private theorem pub_actB_mask (b8 : BitVec 8) (m31 : BitVec 64) (hm31 : m31 = ~~~31#64)
    {activeIdx : Nat} (hAct : activeIdx ≤ 31) :
    (BitVec.zeroExtend 8
      (BitVec.zeroExtend 64 b8 &&& m31 |||
        BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 activeIdx)) >>> 0 &&& 31#64) &&&
      31#8).toNat = activeIdx := by
  subst hm31
  have hb : (BitVec.zeroExtend 8
      (BitVec.zeroExtend 64 b8 &&& (~~~31#64) |||
        BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 activeIdx)) >>> 0 &&& 31#64) &&&
      31#8) = (BitVec.ofNat 64 activeIdx).truncate 8 &&& 31#8 := by bv_robdd
  have htr : (BitVec.ofNat 64 activeIdx).truncate 8 = BitVec.ofNat 8 activeIdx := by bv_omega
  have ha : (BitVec.ofNat 8 activeIdx &&& 31#8) = BitVec.ofNat 8 activeIdx := by
    apply BitVec.eq_of_toNat_eq
    change ((activeIdx % 256) &&& 31) = activeIdx % 256
    rw [Nat.mod_eq_of_lt (by omega), Nat.and_two_pow_sub_one_eq_mod _ 5]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hb, htr, ha, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem spAligned_of_sub96 {s : State} {sp0 : BitVec 64}
    (hsp : s.sp = sp0 - 96#64) (hsAl : s.spAligned = true) :
    (sp0 &&& 15#64 == 0#64) = true := by
  simp only [State.spAligned, hsp] at hsAl; revert hsAl; bv_robdd

theorem ctx_off_active {ctxAddr : BitVec 64} {sc : Nat} (hsc : sc < 48) :
    ctxAddr + ((BitVec.ofNat 64 sc + 10#64) <<< 3) =
      ctxAddr + 80#64 + BitVec.ofNat 64 (8 * sc) := by
  have h2 : BitVec.ofNat 64 (8 * sc) = (BitVec.ofNat 64 sc) <<< 3#64 := by
    apply BitVec.eq_of_toNat_eq
    change (8 * sc) % (2 ^ 64) = ((sc % (2 ^ 64)) <<< 3) % (2 ^ 64)
    rw [Nat.mod_eq_of_lt (by omega : sc < 2 ^ 64), Nat.shiftLeft_eq]
    congr 1; omega
  have hsh : ((BitVec.ofNat 64 sc + 10#64) <<< 3) =
      80#64 + ((BitVec.ofNat 64 sc) <<< 3#64) := by bv_robdd
  rw [h2, hsh]; bv_omega

theorem ctx_off_usage {ctxAddr : BitVec 64} {sc : Nat} (hsc : sc < 48) :
    ctxAddr + ((BitVec.ofNat 64 sc + 58#64) <<< 3) =
      ctxAddr + 464#64 + BitVec.ofNat 64 (8 * sc) := by
  have h2 : BitVec.ofNat 64 (8 * sc) = (BitVec.ofNat 64 sc) <<< 3#64 := by
    apply BitVec.eq_of_toNat_eq
    change (8 * sc) % (2 ^ 64) = ((sc % (2 ^ 64)) <<< 3) % (2 ^ 64)
    rw [Nat.mod_eq_of_lt (by omega : sc < 2 ^ 64), Nat.shiftLeft_eq]
    congr 1; omega
  have hsh : ((BitVec.ofNat 64 sc + 58#64) <<< 3) =
      464#64 + ((BitVec.ofNat 64 sc) <<< 3#64) := by bv_robdd
  rw [h2, hsh]; bv_omega

theorem split_m32 (m v : BitVec 64) (R : SepProp) :
    (((m + 32#64) ↦₆₄ v) ∗ R) =
      (((m + 32#64) ↦₁₆ v.extractLsb' 0 16) ∗
       ((m + 34#64) ↦₁₆ v.extractLsb' 16 16) ∗
       ((m + 36#64) ↦₃₂ v.extractLsb' 32 32) ∗ R) := by
  have h1 : m + 32#64 + 2#64 = m + 34#64 := by bv_omega
  have h2 : m + 32#64 + 4#64 = m + 36#64 := by bv_omega
  have he1 : (v.extractLsb' 0 32).extractLsb' 0 16 = v.extractLsb' 0 16 := by bv_robdd
  have he2 : (v.extractLsb' 0 32).extractLsb' 16 16 = v.extractLsb' 16 16 := by bv_robdd
  rw [pointsTo64_split32 (m + 32#64) v, pointsTo32_split16 (m + 32#64), h1, h2, he1, he2]
  simp only [sepConj_assoc]

private theorem fold_m32_pub (m : BitVec 64) (lastIdx sc maplen : Nat)
    (m5 m12 : BitVec 64) (hm5 : m5 = 32#64 ||| (32#64 <<< 32))
    (hm12 : m12 = (~~~0xfff#32).zeroExtend 64 ||| ((~~~0xfff#32).zeroExtend 64 <<< 32))
    (R : SepProp) :
    let vL := BitVec.ofNat 64 lastIdx
    let vS := BitVec.ofNat 64 sc
    let vM := BitVec.ofNat 64 maplen
    let w64 := vM <<< 12
    let p := (vL &&& 0x1f#64) ||| (1#64 <<< 5) ||| ((vS &&& 0x3f#64) <<< 6) ||| w64
    (((m + 32#64) ↦₁₆ BitVec.truncate 16
        (BitVec.setWidth 32 (BitVec.zeroExtend 64 (BitVec.setWidth 32 vL) &&& 31#64 ||| m5) |||
         BitVec.setWidth 32 (BitVec.zeroExtend 64 (BitVec.setWidth 32 vS) &&& 63#64) <<< 6 |||
         BitVec.setWidth 32 (BitVec.zeroExtend 64 (w64.extractLsb' 0 16) &&& m12))) ∗
     ((m + 34#64) ↦₁₆ w64.extractLsb' 16 16) ∗
     ((m + 36#64) ↦₃₂ w64.extractLsb' 32 32) ∗ R) =
      (((m + 32#64) ↦₆₄ p) ∗ R) := by
  intro vL vS vM w64 p
  have ⟨h0, h1, h2⟩ := pub_packed_parts vL vS vM m5 m12 hm5 hm12
  rw [h0, h1, h2, ← split_m32 m p R]

arm64_proof_prelude

set_option maxHeartbeats 800000 in
theorem wp_publish_new_group_core [MallocngMultiPlacement]
    (s : State) (sp0 ret_pc m mb useOld m16 mb0 : BitVec 64)
    (m24 m28 : BitVec 32) (b8Old : BitVec 8)
    (r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 : BitVec 64)
    (sc activeIdx lastIdx maplen : Nat) (Frame : SepProp)
    (_hw564 : Blk08HasWords564 mallocngFaultSvc)
    (_hw768 : Blk08HasWords768 mallocngFaultSvc) (_hr768 : Blk08Range768)
    (hsc : sc < 48) (hLast31 : lastIdx ≤ 31) (hActLe : activeIdx ≤ lastIdx)
    (hpc : s.pc = mbase 8 + allocSlotOff_pub_add)
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 96#64) (hsAl : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 sc)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 sc)
    (hx19 : s.readReg64 .x19 = m) (hx0 : s.readReg64 .x0 = mb)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 activeIdx)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 lastIdx)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (lastIdx + 1)) :
    let w64 := BitVec.ofNat 64 maplen <<< 12
    let initAvail : BitVec 32 := (2#32 <<< BitVec.ofNat 32 activeIdx) - 1#32
    let packedW : BitVec 64 :=
      (((BitVec.ofNat 64 lastIdx &&& 0x1f#64) ||| (1#64 <<< 5)) |||
        ((BitVec.ofNat 64 sc &&& 0x3f#64) <<< 6) ||| w64)
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) ret_pc s
      (((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ 0#64) ∗
       ((maddrs.ctx + 464#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ useOld) ∗
       (m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦₆₄ m16) ∗
       ((m + 24#64) ↦₃₂ m24) ∗ ((m + 28#64) ↦₃₂ m28) ∗
       ((m + 32#64) ↦₁₆ w64.extractLsb' 0 16) ∗
       ((m + 34#64) ↦₁₆ w64.extractLsb' 16 16) ∗
       ((m + 36#64) ↦₃₂ w64.extractLsb' 32 32) ∗
       (mb ↦₆₄ mb0) ∗ ((mb + 8#64) ↦₈ b8Old) ∗
       ((sp0 - 96#64) ↦₆₄ r29) ∗ ((sp0 - 88#64) ↦₆₄ ret_pc) ∗
       ((sp0 - 80#64) ↦₆₄ r19) ∗ ((sp0 - 72#64) ↦₆₄ r20) ∗
       ((sp0 - 64#64) ↦₆₄ r21) ∗ ((sp0 - 56#64) ↦₆₄ r22) ∗
       ((sp0 - 48#64) ↦₆₄ r23) ∗ ((sp0 - 40#64) ↦₆₄ r24) ∗
       ((sp0 - 32#64) ↦₆₄ r25) ∗ ((sp0 - 24#64) ↦₆₄ r26) ∗
       ((sp0 - 16#64) ↦₆₄ r27) ∗ ((sp0 - 8#64) ↦₆₄ r28) ∗ Frame)
      (fun sf P_f =>
        sf.status = .Running ∧ sf.sp = sp0 ∧ sf.spAligned = true ∧
        PureStatePres s sf ∧
        sf.readReg64 .x0 = 0#64 ∧
        sf.readReg64 .x19 = r19 ∧ sf.readReg64 .x20 = r20 ∧
        sf.readReg64 .x21 = r21 ∧ sf.readReg64 .x22 = r22 ∧
        sf.readReg64 .x23 = r23 ∧ sf.readReg64 .x24 = r24 ∧
        sf.readReg64 .x25 = r25 ∧ sf.readReg64 .x26 = r26 ∧
        sf.readReg64 .x27 = r27 ∧ sf.readReg64 .x28 = r28 ∧
        sf.readReg64 .x29 = r29 ∧ sf.readReg64 .x30 = ret_pc ∧
        ∃ actB : BitVec 8, (actB &&& 0x1f#8).toNat = activeIdx ∧
          P_f = (((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ m) ∗
            ((maddrs.ctx + 464#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄
              (useOld + BitVec.ofNat 64 (lastIdx + 1))) ∗
            (m ↦₆₄ m) ∗ ((m + 8#64) ↦₆₄ m) ∗ ((m + 16#64) ↦₆₄ mb) ∗
            ((m + 24#64) ↦₃₂ (initAvail - 1#32)) ∗
            ((m + 28#64) ↦₃₂ ((2#32 <<< BitVec.ofNat 32 lastIdx) + ~~~initAvail)) ∗
            ((m + 32#64) ↦₆₄ packedW) ∗
            (mb ↦₆₄ m) ∗ ((mb + 8#64) ↦₈ actB) ∗
            ((sp0 - 96#64) ↦₆₄ r29) ∗ ((sp0 - 88#64) ↦₆₄ ret_pc) ∗
            ((sp0 - 80#64) ↦₆₄ r19) ∗ ((sp0 - 72#64) ↦₆₄ r20) ∗
            ((sp0 - 64#64) ↦₆₄ r21) ∗ ((sp0 - 56#64) ↦₆₄ r22) ∗
            ((sp0 - 48#64) ↦₆₄ r23) ∗ ((sp0 - 40#64) ↦₆₄ r24) ∗
            ((sp0 - 32#64) ↦₆₄ r25) ∗ ((sp0 - 24#64) ↦₆₄ r26) ∗
            ((sp0 - 16#64) ↦₆₄ r27) ∗ ((sp0 - 8#64) ↦₆₄ r28) ∗ Frame))
      (fun _ => ⌜False⌝) := by
  intro w64 initAvail packedW
  dsimp only [allocSlotOff_pub_add] at hpc
  have hoff_u := ctx_off_usage (ctxAddr := maddrs.ctx) hsc
  have hoff_a := ctx_off_active (ctxAddr := maddrs.ctx) hsc
  have hAl0 := spAligned_of_sub96 hsp hsAl
  wp_sym_steps
  have hAct31 : activeIdx ≤ 31 := Nat.le_trans hActLe hLast31
  have hav := pub_avail_eq hAct31
  have hlsh := pub_avail_eq hLast31
  refine SepWP.done rfl ?_ ?_
  · simp [hrun]
  · refine ⟨by simp [hrun], by simp, by simpa [State.spAligned] using hAl0, psp_rfl,
      by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp,
      _, pub_actB_mask b8Old _ rfl hAct31, ?_⟩
    dsimp only [w64, initAvail, packedW]
    rw [hav, hlsh, pub_not32]
    refine congrArg (_ ∗ ·) (congrArg (_ ∗ ·) (congrArg (_ ∗ ·) (congrArg (_ ∗ ·)
      (congrArg (_ ∗ ·) (congrArg (_ ∗ ·) (congrArg (_ ∗ ·) ?_))))))
    exact fold_m32_pub m lastIdx sc maplen _ _ rfl rfl _

theorem wp_publish_new_group [MallocngMultiPlacement]
    {s : State}
    (sp0 ret_pc m mb useOld m16 mb0 : BitVec 64)
    (m24 m28 : BitVec 32) (b8Old : BitVec 8)
    (r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 : BitVec 64)
    (sc activeIdx lastIdx maplen : Nat)
    (pm : Option (BitVec 64)) (ncap : Nat) (fzero : Bool)
    (Frame : SepProp) (oom : State → SepProp)
    (hw564 : Blk08HasWords564 mallocngFaultSvc)
    (hw768 : Blk08HasWords768 mallocngFaultSvc) (hr768 : Blk08Range768)
    (hsc : sc < 48) (hLast31 : lastIdx ≤ 31) (hActLe : activeIdx ≤ lastIdx)
    (hpc : s.pc = mbase 8 + allocSlotOff_pub_add)
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 96#64) (hsAl : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 sc)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 sc)
    (hx19 : s.readReg64 .x19 = m) (hx0 : s.readReg64 .x0 = mb)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 activeIdx)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 lastIdx)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (lastIdx + 1)) :
    SepWP (mallocngBlockProg mmpl 8 msvc) ret_pc s
      (((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ 0#64) ∗
       ((maddrs.ctx + 464#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ useOld) ∗
       (m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦₆₄ m16) ∗
       ((m + 24#64) ↦₃₂ m24) ∗ ((m + 28#64) ↦₃₂ m28) ∗
       ((m + 32#64) ↦₆₄ (BitVec.ofNat 64 maplen <<< 12)) ∗
       (mb ↦₆₄ mb0) ∗ ((mb + 8#64) ↦₈ b8Old) ∗
       ((sp0 - 96#64) ↦₆₄ r29) ∗ ((sp0 - 88#64) ↦₆₄ ret_pc) ∗
       ((sp0 - 80#64) ↦₆₄ r19) ∗ ((sp0 - 72#64) ↦₆₄ r20) ∗
       ((sp0 - 64#64) ↦₆₄ r21) ∗ ((sp0 - 56#64) ↦₆₄ r22) ∗
       ((sp0 - 48#64) ↦₆₄ r23) ∗ ((sp0 - 40#64) ↦₆₄ r24) ∗
       ((sp0 - 32#64) ↦₆₄ r25) ∗ ((sp0 - 24#64) ↦₆₄ r26) ∗
       ((sp0 - 16#64) ↦₆₄ r27) ∗ ((sp0 - 8#64) ↦₆₄ r28) ∗ Frame)
      (fun sf P_f =>
        sf.status = .Running ∧ sf.sp = sp0 ∧ sf.spAligned = true ∧
        PureStatePres s sf ∧ sf.mem.perm = s.mem.perm ∧
        sf.readReg64 .x0 = 0#64 ∧
        sf.readReg64 .x19 = r19 ∧ sf.readReg64 .x20 = r20 ∧
        sf.readReg64 .x21 = r21 ∧ sf.readReg64 .x22 = r22 ∧
        sf.readReg64 .x23 = r23 ∧ sf.readReg64 .x24 = r24 ∧
        sf.readReg64 .x25 = r25 ∧ sf.readReg64 .x26 = r26 ∧
        sf.readReg64 .x27 = r27 ∧ sf.readReg64 .x28 = r28 ∧
        sf.readReg64 .x29 = r29 ∧ sf.readReg64 .x30 = ret_pc ∧
        ∃ actB : BitVec 8, (actB &&& 0x1f#8).toNat = activeIdx ∧
          let initAvail : BitVec 32 := (2#32 <<< BitVec.ofNat 32 activeIdx) - 1#32
          let cg : GroupDesc := {
            metaPtr := m, prev := m, next := m, mem := mb,
            availMask := initAvail - 1#32,
            freedMask := (2#32 <<< BitVec.ofNat 32 lastIdx) + ~~~initAvail,
            lastIdx := lastIdx, sc := sc, maplen := maplen, activeByte := actB,
            parentMeta := pm, nestedCap := ncap,
            slots := newGroupSlots lastIdx activeIdx, freshZero := fzero }
          P_f = (((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ m) ∗
            ((maddrs.ctx + 464#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄
              (useOld + BitVec.ofNat 64 (lastIdx + 1))) ∗
            (m ↦ₛ cg.metaBytes) ∗ (mb ↦₆₄ m) ∗ ((mb + 8#64) ↦₈ actB) ∗
            ((sp0 - 96#64) ↦₆₄ r29) ∗ ((sp0 - 88#64) ↦₆₄ ret_pc) ∗
            ((sp0 - 80#64) ↦₆₄ r19) ∗ ((sp0 - 72#64) ↦₆₄ r20) ∗
            ((sp0 - 64#64) ↦₆₄ r21) ∗ ((sp0 - 56#64) ↦₆₄ r22) ∗
            ((sp0 - 48#64) ↦₆₄ r23) ∗ ((sp0 - 40#64) ↦₆₄ r24) ∗
            ((sp0 - 32#64) ↦₆₄ r25) ∗ ((sp0 - 24#64) ↦₆₄ r26) ∗
            ((sp0 - 16#64) ↦₆₄ r27) ∗ ((sp0 - 8#64) ↦₆₄ r28) ∗ Frame))
      oom := by
  apply sepWP_of_noSyscalls_block
  conv =>
    arg 4
    simp only [sepConj_assoc]
    rw [split_m32 m (BitVec.ofNat 64 maplen <<< 12)]
  refine SepWP.mono (wp_publish_new_group_core s sp0 ret_pc m mb useOld m16 mb0 m24 m28 b8Old
    r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 sc activeIdx lastIdx maplen Frame
    hw564 hw768 hr768 hsc hLast31 hActLe hpc hrun hsp hsAl
    hx22 hx23 hx21 hx19 hx0 hx1 hx2 hx28) ?_
  intro sf P_f _ _ hpost hperm
  rcases hpost with ⟨h1, h2, h3, hpsp, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, actB, hActB, hPf⟩
  refine ⟨h1, h2, h3, hpsp, hperm, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, actB, hActB, ?_⟩
  dsimp only
  rw [GroupDesc.metaBytes_pointsTo m]
  simpa only [GroupDesc.packedWord, sepConj_assoc] using hPf

/-! ## `.rodata` Table Splits -/

theorem split_sizeClass_ro (scAddr : BitVec 64) {sc : Nat} (hsc : sc < 48) (R : SepProp) :
    ∃ Rest : SepProp, ((scAddr ↦ᵣ sizeClassBytes) ∗ R) =
      (((scAddr + BitVec.ofNat 64 (2 * sc)) ↦₁₆ᵣ BitVec.ofNat 16 (sizeClass sc)) ∗ Rest ∗ R) := by
  refine ⟨(scAddr ↦ᵣ sizeClassBytes.take (2 * sc)) ∗
    ((scAddr + BitVec.ofNat 64 (2 * sc + 2)) ↦ᵣ sizeClassBytes.drop (2 * sc + 2)), ?_⟩
  rw [pointsToBytesRO_split3 scAddr sizeClassBytes (2 * sc) 2
    (by rw [sizeClassBytes_length]; omega)]
  rw [pointsToBytesRO_take2_eq_pointsTo16RO _ _ _ (by rw [sizeClassBytes_length]; omega),
    pack16_sizeClassBytes hsc]
  simp only [sepConj_assoc]

theorem split_medCnt_ro (medAddr : BitVec 64) {sc : Nat} (_hsc : sc < 48) (R : SepProp) :
    ∃ Rest : SepProp, ((medAddr ↦ᵣ medCntTabBytes) ∗ R) =
      (((medAddr + BitVec.ofNat 64 (sc % 4)) ↦₈ᵣ medCntTabBytes.getD (sc % 4) 0#8) ∗
        Rest ∗ R) := by
  have hm4 : (sc % 4) + 1 ≤ medCntTabBytes.length := by rw [medCntTabBytes_length]; omega
  refine ⟨(medAddr ↦ᵣ medCntTabBytes.take (sc % 4)) ∗
    ((medAddr + BitVec.ofNat 64 (sc % 4 + 1)) ↦ᵣ medCntTabBytes.drop (sc % 4 + 1)), ?_⟩
  rw [pointsToBytesRO_split3 medAddr medCntTabBytes (sc % 4) 1 hm4,
    pointsToBytesRO_take1_eq_pointsTo8RO _ _ _ hm4]
  simp only [sepConj_assoc]

private theorem smallCnt_take3_all :
    (List.range 9).all (fun sc =>
      (smallCntTabBytes.drop (3 * sc)).take 3 ==
        [smallCntTabBytes.getD (3 * sc) 0#8,
         smallCntTabBytes.getD (3 * sc + 1) 0#8,
         smallCntTabBytes.getD (3 * sc + 2) 0#8]) = true := by
  decide +kernel

theorem split_smallCnt_ro (smAddr : BitVec 64) {sc : Nat} (hsc : sc ≤ 8) (R : SepProp) :
    ∃ Rest : SepProp, ((smAddr ↦ᵣ smallCntTabBytes) ∗ R) =
      (((smAddr + BitVec.ofNat 64 (3 * sc)) ↦₈ᵣ smallCntTabBytes.getD (3 * sc) 0#8) ∗
       ((smAddr + BitVec.ofNat 64 (3 * sc) + 1#64) ↦₈ᵣ
         smallCntTabBytes.getD (3 * sc + 1) 0#8) ∗
       ((smAddr + BitVec.ofNat 64 (3 * sc) + 2#64) ↦₈ᵣ
         smallCntTabBytes.getD (3 * sc + 2) 0#8) ∗ Rest ∗ R) := by
  have hslen : 3 * sc + 3 ≤ smallCntTabBytes.length := by rw [smallCntTabBytes_length]; omega
  refine ⟨(smAddr ↦ᵣ smallCntTabBytes.take (3 * sc)) ∗
    ((smAddr + BitVec.ofNat 64 (3 * sc + 3)) ↦ᵣ smallCntTabBytes.drop (3 * sc + 3)), ?_⟩
  have htake3 : (smallCntTabBytes.drop (3 * sc)).take 3 =
      [smallCntTabBytes.getD (3 * sc) 0#8] ++
      ([smallCntTabBytes.getD (3 * sc + 1) 0#8] ++ [smallCntTabBytes.getD (3 * sc + 2) 0#8]) := by
    simpa [beq_iff_eq] using List.all_eq_true.mp smallCnt_take3_all sc (List.mem_range.mpr (by omega))
  rw [pointsToBytesRO_split3 smAddr smallCntTabBytes (3 * sc) 3 hslen, htake3]
  rw [pointsToBytesRO_append, pointsToBytesRO_append]
  simp only [List.length_singleton, pointsToBytesRO_singleton, sepConj_assoc]
  have ha2 : smAddr + BitVec.ofNat 64 (3 * sc) + (BitVec.ofNat 64 1 + BitVec.ofNat 64 1) =
      smAddr + BitVec.ofNat 64 (3 * sc) + 2#64 := by bv_omega
  rw [BitVec.add_assoc (smAddr + BitVec.ofNat 64 (3 * sc)), ha2]

end VerifiedLibraries.Mallocng.Proofs
