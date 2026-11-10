/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64

/-!
# Multi-Block Placed Library for musl 1.2.5 `mallocng`

Defines `VerifiedLibraries.mallocngLib : Obj.MultiPlacedLib` containing the 24 `.text.<fn>` code
blocks (13 `mallocng` allocator functions and 11 musl leaf helpers), 9 `.rodata`/`.bss`
`Obj.SymDataInfo` entries, and the 6 C allocator exports (`malloc`, `free`, `calloc`, `realloc`,
`aligned_alloc`, `posix_memalign`) from musl 1.2.5.
-/

@[expose] public section

namespace VerifiedLibraries

open Arm64

/-- Little-endian byte expansion of a list of 32-bit A64 instruction words. -/
def mallocngWordsLE (ws : List (BitVec 32)) : List (BitVec 8) :=
  ws.flatMap fun w => [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

def mallocng_blk00_errno_location : Obj.CodeBlock where
  code := mallocngWordsLE [0xd53bd040#32, 0xd1029000#32, 0xd65f03c0#32]
  align := 4
  symbols := [("__errno_location", 0), ("___errno_location", 0)]
  relocs := []

def mallocng_blk01_syscall_ret : Obj.CodeBlock where
  code := mallocngWordsLE [
    0xa9be7bfd#32, 0xb140041f#32, 0x910003fd#32, 0xf9000bf3#32, 0xaa0003f3#32, 0x54000088#32, 0xf9400bf3#32, 0xa8c27bfd#32, 0xd65f03c0#32, 0x94000000#32,
    0xaa0003e1#32, 0x4b1303f3#32, 0x92800000#32, 0xb9000033#32, 0x17fffff8#32]
  align := 4
  symbols := [("__syscall_ret", 0)]
  relocs := [
    { off := 36, kind := .call26, sym := "___errno_location" }]

def mallocng_blk02_calloc : Obj.CodeBlock where
  code := mallocngWordsLE [
    0xa9bd7bfd#32, 0x910003fd#32, 0xa90153f3#32, 0xb4000061#32, 0x9bc17c02#32, 0xb5000422#32, 0x9b007c33#32, 0xaa1303e0#32, 0x94000000#32, 0xaa0003f4#32,
    0xb4000460#32, 0x90000001#32, 0xb9400021#32, 0x340003c1#32, 0xf13ffe7f#32, 0x54000469#32, 0x8b130293#32, 0xf90013f5#32, 0x92402e62#32, 0xd2820015#32,
    0xcb020260#32, 0x52800001#32, 0x94000000#32, 0xcb140013#32, 0xf13ffe7f#32, 0x54000309#32, 0xaa0003f3#32, 0xd1400400#32, 0xcb1302a4#32, 0xa97f0e65#32,
    0x8b040262#32, 0xaa050063#32, 0xb5fffe83#32, 0xd1004273#32, 0xeb13001f#32, 0x54ffff41#32, 0xd2800002#32, 0x17ffffef#32, 0x94000000#32, 0xd2800014#32,
    0x52800181#32, 0xb9000001#32, 0x14000003#32, 0x94000000#32, 0x34fffc40#32, 0xaa1403e0#32, 0xa94153f3#32, 0xa8c37bfd#32, 0xd65f03c0#32, 0xf94013f5#32,
    0xaa1303e2#32, 0xaa1403e0#32, 0x52800001#32, 0xa94153f3#32, 0xa8c37bfd#32, 0x14000000#32]
  align := 4
  symbols := [("calloc", 0)]
  relocs := [
    { off := 32, kind := .call26, sym := "malloc" },
    { off := 44, kind := .adrpHi21, sym := "__malloc_replaced" },
    { off := 48, kind := .ldst32Lo12, sym := "__malloc_replaced" },
    { off := 88, kind := .call26, sym := "memset" },
    { off := 152, kind := .call26, sym := "___errno_location" },
    { off := 172, kind := .call26, sym := "__malloc_allzerop" },
    { off := 220, kind := .jump26, sym := "memset" }]

def mallocng_blk03_free : Obj.CodeBlock where
  code := mallocngWordsLE [0x14000000#32]
  align := 4
  symbols := [("free", 0)]
  relocs := [
    { off := 0, kind := .jump26, sym := "__libc_free" }]

def mallocng_blk04_default_malloc : Obj.CodeBlock where
  code := mallocngWordsLE [0x14000000#32]
  align := 4
  symbols := [("default_malloc", 0), ("malloc", 0), ("__libc_malloc", 0)]
  relocs := [
    { off := 0, kind := .jump26, sym := "__libc_malloc_impl" }]

def mallocng_blk05_nontrivial_free : Obj.CodeBlock where
  code := mallocngWordsLE [
    0xa9be7bfd#32, 0x52800042#32, 0x910003fd#32, 0xa90153f3#32, 0xaa0003f3#32, 0x52800020#32, 0x1ac12001#32, 0x39408260#32, 0xb9401e64#32, 0xb9401a63#32,
    0x12001006#32, 0x79404265#32, 0xd3401000#32, 0x2a030083#32, 0x1ac02042#32, 0x0b030024#32, 0x51000442#32, 0xd3462ca0#32, 0x6b02009f#32, 0x540000e0#32,
    0x35002123#32, 0x7100bc1f#32, 0x54001e6d#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0x39408262#32, 0x362fff22#32, 0x7100bc1f#32, 0xf9400664#32,
    0x5400218c#32, 0xf9401265#32, 0xf240105f#32, 0x9274cca2#32, 0x540002a1#32, 0x93407c08#32, 0xb4000142#32, 0x90000007#32, 0x910000e7#32, 0x9274cca2#32,
    0x93407c08#32, 0xd1004042#32, 0x7860d8e5#32, 0xd37c3ca5#32, 0xeb05005f#32, 0x54000182#32, 0xb5000624#32, 0x90000014#32, 0x91000294#32, 0x9100e902#32,
    0x110004c6#32, 0xf8627a81#32, 0xcb26c021#32, 0xf8227a81#32, 0x1400003f#32, 0x93407c08#32, 0xb4fffec2#32, 0xeb04027f#32, 0x540000e0#32, 0xb4fffe84#32,
    0x91002900#32, 0x90000014#32, 0x91000281#32, 0xf8607820#32, 0x14000025#32, 0x51001c00#32, 0x90000014#32, 0x71007c1f#32, 0x54000109#32, 0x91000280#32,
    0x91002901#32, 0xf8617800#32, 0x91000281#32, 0x91002902#32, 0xf822783f#32, 0x14000023#32, 0x91000284#32, 0x8b20c080#32, 0x394dc000#32, 0x71018c1f#32,
    0x54fffea9#32, 0x9100e902#32, 0x110004c6#32, 0x937d7cc0#32, 0xf8627882#32, 0x8b26c000#32, 0xeb00005f#32, 0x7a5328c0#32, 0x54fffdad#32, 0x35001883#32,
    0x91002902#32, 0xf8627880#32, 0xeb13001f#32, 0x54fff741#32, 0x140000bf#32, 0x91002900#32, 0x90000014#32, 0x91000281#32, 0xeb04027f#32, 0xf8607820#32,
    0x54fffc80#32, 0xf9400262#32, 0x91000281#32, 0x91002903#32, 0xf9000444#32, 0xf9400262#32, 0xf9000082#32, 0xf8637822#32, 0xeb02027f#32, 0x54000520#32,
    0xa9007e7f#32, 0xeb00027f#32, 0x54000520#32, 0x79404260#32, 0xd3462c00#32, 0x7100bc1f#32, 0x540007ed#32, 0xf9401261#32, 0xf274cc21#32, 0x54000940#32,
    0x90000014#32, 0x91000282#32, 0x394e4041#32, 0x7103fc3f#32, 0x54000760#32, 0x11000421#32, 0x390e4041#32, 0x51001c00#32, 0x71007c1f#32, 0x540000a8#32,
    0x91000281#32, 0x8b20c020#32, 0x394e4021#32, 0x390d4001#32, 0xf9401261#32, 0xf9400a60#32, 0x9274cc21#32, 0x91000294#32, 0xa9007e7f#32, 0xa9017e7f#32,
    0xf9400a82#32, 0xf900127f#32, 0xb4000f02#32, 0xf9000662#32, 0xf9400042#32, 0xf9000262#32, 0xf9000453#32, 0xf9400662#32, 0xf9000053#32, 0x1400008f#32,
    0xf9400662#32, 0xf8237822#32, 0x17ffffd6#32, 0x91002902#32, 0x91000280#32, 0xf8627804#32, 0xb4fffaa4#32, 0xb9401880#32, 0x35ffef20#32, 0xf9400880#32,
    0x52800045#32, 0x91007082#32, 0x39402000#32, 0xd3401000#32, 0x1ac020a5#32, 0x510004a6#32, 0x4b0503e5#32, 0x14000002#32, 0xd5033bbf#32, 0xb9401c83#32,
    0x0a050061#32, 0x885ffc40#32, 0x6b00007f#32, 0x54ffff61#32, 0x8800fc41#32, 0x35ffff80#32, 0x0a0300c3#32, 0xb9001883#32, 0x17ffffbf#32, 0x39408266#32,
    0x93407c08#32, 0x120010c6#32, 0x17ffff7a#32, 0x90000001#32, 0x910dc042#32, 0x91000021#32, 0x3800143f#32, 0xeb01005f#32, 0x54ffffc1#32, 0x91000281#32,
    0x52800022#32, 0x390e4022#32, 0x17ffffbf#32, 0xf9400a63#32, 0xf2400c62#32, 0x54000060#32, 0x3900003f#32, 0xd4207d00#32, 0x385fc060#32, 0x385fd061#32,
    0x785fe064#32, 0x12001021#32, 0x34000100#32, 0x34000064#32, 0x3900005f#32, 0xd4207d00#32, 0xb85f8064#32, 0x529fffe0#32, 0x6b00009f#32, 0x54ffff6d#32,
    0x531c6c82#32, 0x928001e0#32, 0xcb22c000#32, 0x8b000065#32, 0xf8606860#32, 0xf9400802#32, 0xeb0200bf#32, 0x54ffe7c1#32, 0x39408002#32, 0x12001042#32,
    0x6b02003f#32, 0x54ffe74c#32, 0xb9401802#32, 0x1ac12442#32, 0x3707e6e2#32, 0xb9401c02#32, 0x1ac12442#32, 0x3707e682#32, 0x9274cc02#32, 0x90000014#32,
    0xf9400285#32, 0xf9400042#32, 0xeb05005f#32, 0x54ffe5c1#32, 0x79404002#32, 0xd3462c45#32, 0x7100bcbf#32, 0x540002a8#32, 0x90000002#32, 0x91000042#32,
    0x7865d842#32, 0x1b027c25#32, 0x6b05009f#32, 0x54ffe48b#32, 0x0b050042#32, 0x6b02009f#32, 0x54ffe42a#32, 0xf9401002#32, 0xf274cc5f#32, 0x540000c0#32,
    0x9274cc42#32, 0xd344fc42#32, 0xd1000442#32, 0xeb24c05f#32, 0x54ffe323#32, 0xf900007f#32, 0x97ffff00#32, 0x17ffff88#32, 0x121a1442#32, 0x713f005f#32,
    0x54ffe261#32, 0x17fffff2#32, 0xa9004e73#32, 0xf9000a93#32, 0x1400001c#32, 0x93407c00#32, 0x90000002#32, 0x91002800#32, 0x91000042#32, 0xf8607843#32,
    0xeb13007f#32, 0x540001c0#32, 0xf9400664#32, 0xb5ffe0c4#32, 0xf9400265#32, 0xb4000065#32, 0x3900009f#32, 0xd4207d00#32, 0xb4000223#32, 0xf9000663#32,
    0xf9400060#32, 0xf9000260#32, 0xf9000413#32, 0xf9400660#32, 0xf9000013#32, 0x91007262#32, 0x885ffc40#32, 0x2a000020#32, 0x8803fc40#32, 0x35ffffa3#32,
    0xd2800000#32, 0xd2800001#32, 0xa94153f3#32, 0xa8c27bfd#32, 0xd65f03c0#32, 0xa9004e73#32, 0xf8207853#32, 0x17fffff4#32, 0xb5ffdda4#32, 0x17ffff4a#32]
  align := 4
  symbols := [("nontrivial_free", 0)]
  relocs := [
    { off := 148, kind := .adrpHi21, sym := "__malloc_size_classes" },
    { off := 152, kind := .addLo12, sym := "__malloc_size_classes" },
    { off := 188, kind := .adrpHi21, sym := "__malloc_context" },
    { off := 192, kind := .addLo12, sym := "__malloc_context" },
    { off := 244, kind := .adrpHi21, sym := "__malloc_context" },
    { off := 248, kind := .addLo12, sym := "__malloc_context" },
    { off := 264, kind := .adrpHi21, sym := "__malloc_context" },
    { off := 276, kind := .addLo12, sym := "__malloc_context" },
    { off := 288, kind := .addLo12, sym := "__malloc_context" },
    { off := 304, kind := .addLo12, sym := "__malloc_context" },
    { off := 384, kind := .adrpHi21, sym := "__malloc_context" },
    { off := 388, kind := .addLo12, sym := "__malloc_context" },
    { off := 408, kind := .addLo12, sym := "__malloc_context" },
    { off := 480, kind := .adrpHi21, sym := "__malloc_context" },
    { off := 484, kind := .addLo12, sym := "__malloc_context" },
    { off := 520, kind := .addLo12, sym := "__malloc_context" },
    { off := 548, kind := .addLo12, sym := "__malloc_context" },
    { off := 616, kind := .addLo12, sym := "__malloc_context" },
    { off := 732, kind := .adrpHi21, sym := "__malloc_context", addend := 848 },
    { off := 740, kind := .addLo12, sym := "__malloc_context", addend := 848 },
    { off := 756, kind := .addLo12, sym := "__malloc_context" },
    { off := 916, kind := .adrpHi21, sym := "__malloc_context" },
    { off := 920, kind := .ldst64Lo12, sym := "__malloc_context" },
    { off := 952, kind := .adrpHi21, sym := "__malloc_size_classes" },
    { off := 956, kind := .addLo12, sym := "__malloc_size_classes" },
    { off := 1064, kind := .adrpHi21, sym := "__malloc_context" },
    { off := 1072, kind := .addLo12, sym := "__malloc_context" }]

def mallocng_blk06_libc_free : Obj.CodeBlock where
  code := mallocngWordsLE [
    0xb4001ac0#32, 0xf2400c05#32, 0x54000080#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0xa9bd7bfd#32, 0x910003fd#32, 0xa90153f3#32, 0xf90013f5#32,
    0x385fc003#32, 0x385fd002#32, 0x785fe004#32, 0x12001054#32, 0x34000143#32, 0x34000064#32, 0x390000bf#32, 0xd4207d00#32, 0xb85f8004#32, 0x529fffe3#32,
    0x6b03009f#32, 0x5400006c#32, 0x390000bf#32, 0xd4207d00#32, 0x531c6c83#32, 0x928001e5#32, 0xcb23c0a3#32, 0x8b030006#32, 0xf8636813#32, 0xf9400a65#32,
    0xeb0500df#32, 0x54000080#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0x39408267#32, 0x120010e3#32, 0x6b03029f#32, 0xd34010e9#32, 0x5400008d#32,
    0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0xb9401a63#32, 0x1ad42463#32, 0x36000083#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0xb9401e63#32,
    0x1ad42463#32, 0x36000083#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0x9274ce63#32, 0x90000006#32, 0xf94000c6#32, 0xf9400063#32, 0xeb06007f#32,
    0x54000080#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0x79404263#32, 0xd3462c68#32, 0x7100bd1f#32, 0x54000208#32, 0x90000003#32, 0x91000063#32,
    0x7868d863#32, 0x1b037e86#32, 0x6b06009f#32, 0x5400008a#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0x0b060063#32, 0x6b03009f#32, 0x5400014b#32,
    0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0x121a1463#32, 0x713f007f#32, 0x54000080#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0xf9401263#32,
    0xf274cc7f#32, 0x54000d20#32, 0x9274cc63#32, 0xd344fc66#32, 0xd10004c6#32, 0xeb24c0df#32, 0x54000c22#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32,
    0xb85fc082#32, 0xf100105f#32, 0x54000088#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0x385fb086#32, 0x34000086#32, 0xd2800000#32, 0x3900001f#32,
    0xd4207d00#32, 0xcb000086#32, 0xeb0200df#32, 0x54000082#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0xcb020084#32, 0x39400082#32, 0x34000082#32,
    0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0x386368a2#32, 0x34000082#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0x52800046#32, 0x52800025#32,
    0x1ac920c6#32, 0x90000007#32, 0x510004c6#32, 0x910000e7#32, 0x12800002#32, 0x1ad420a5#32, 0x381fd002#32, 0x781fe01f#32, 0xb9401e64#32, 0xb9401a60#32,
    0x2a040000#32, 0x6a0000bf#32, 0x54000080#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0x340002c4#32, 0x0b0000a0#32, 0x6b06001f#32, 0x54000260#32,
    0x39400ce0#32, 0x0b0400a2#32, 0x72001c1f#32, 0x54000160#32, 0x91007260#32, 0x885ffc03#32, 0x6b03009f#32, 0x54000121#32, 0x8803fc02#32, 0x35ffff83#32,
    0xa94153f3#32, 0xf94013f5#32, 0xa8c37bfd#32, 0xd65f03c0#32, 0xb9001e62#32, 0x17fffffb#32, 0xd5033bbf#32, 0x17ffffe3#32, 0x90000000#32, 0x91000000#32,
    0x90000015#32, 0x39400c00#32, 0x72001c1f#32, 0x54000221#32, 0x2a1403e1#32, 0xaa1303e0#32, 0x94000000#32, 0xaa0003f4#32, 0xaa0103f3#32, 0x910002a0#32,
    0x94000000#32, 0xb4fffd73#32, 0x94000000#32, 0xaa0003f5#32, 0xaa1303e1#32, 0xaa1403e0#32, 0xb94002b3#32, 0x94000000#32, 0xb90002b3#32, 0x17ffffe3#32,
    0x910002a0#32, 0x94000000#32, 0x17ffffee#32, 0xd1004063#32, 0xf24010ff#32, 0x540000a0#32, 0x90000003#32, 0x91000063#32, 0x7868d863#32, 0xd37c3c63#32,
    0x92401e84#32, 0xd1001066#32, 0x910040a5#32, 0x71027c5f#32, 0x53057c47#32, 0xd3451c42#32, 0x9b031883#32, 0x8b0300a4#32, 0x54fff3e9#32, 0x710014ff#32,
    0x54fff240#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0xd65f03c0#32]
  align := 4
  symbols := [("__libc_free", 0)]
  relocs := [
    { off := 224, kind := .adrpHi21, sym := "__malloc_context" },
    { off := 228, kind := .ldst64Lo12, sym := "__malloc_context" },
    { off := 272, kind := .adrpHi21, sym := "__malloc_size_classes" },
    { off := 276, kind := .addLo12, sym := "__malloc_size_classes" },
    { off := 524, kind := .adrpHi21, sym := "__libc" },
    { off := 532, kind := .addLo12, sym := "__libc" },
    { off := 672, kind := .adrpHi21, sym := "__libc" },
    { off := 676, kind := .addLo12, sym := "__libc" },
    { off := 680, kind := .adrpHi21, sym := "__malloc_lock" },
    { off := 704, kind := .call26, sym := "nontrivial_free" },
    { off := 716, kind := .addLo12, sym := "__malloc_lock" },
    { off := 720, kind := .call26, sym := "__unlock" },
    { off := 728, kind := .call26, sym := "___errno_location" },
    { off := 748, kind := .call26, sym := "munmap" },
    { off := 760, kind := .addLo12, sym := "__malloc_lock" },
    { off := 764, kind := .call26, sym := "__lock" },
    { off := 784, kind := .adrpHi21, sym := "__malloc_size_classes" },
    { off := 788, kind := .addLo12, sym := "__malloc_size_classes" }]

def mallocng_blk07_malloc_alloc_meta : Obj.CodeBlock where
  code := mallocngWordsLE [
    0xa9bb7bfd#32, 0x910003fd#32, 0xa90153f3#32, 0x90000014#32, 0x91000280#32, 0xb9400800#32, 0x34000220#32, 0x91000281#32, 0xf9400833#32, 0xb40011d3#32,
    0xf9400660#32, 0xeb00027f#32, 0x54000560#32, 0xf9400262#32, 0xf9000440#32, 0xf9400262#32, 0xf9000002#32, 0xf9400820#32, 0xeb00027f#32, 0x54001161#32,
    0xf9400660#32, 0xf9000820#32, 0x14000088#32, 0xd289cda1#32, 0xa9025bf5#32, 0x910123f5#32, 0xf2a838c1#32, 0x90000000#32, 0x91000000#32, 0xd2800013#32,
    0x9b017ea1#32, 0xaa0003f6#32, 0xf90027e1#32, 0xf9400400#32, 0x14000009#32, 0x8b130001#32, 0xd2800102#32, 0xaa1503e0#32, 0xf9400421#32, 0x8b020021#32,
    0x94000000#32, 0xf94006c0#32, 0x91004273#32, 0xf8736801#32, 0xf100643f#32, 0xb4000061#32, 0x54ffff81#32, 0x17fffff4#32, 0x91000280#32, 0x52800021#32,
    0xf94027e2#32, 0xf9000282#32, 0xb9000801#32, 0xa9425bf5#32, 0x17ffffd1#32, 0xf900083f#32, 0x14000066#32, 0x90000000#32, 0xa9025bf5#32, 0xd2820003#32,
    0xa90363f7#32, 0xf9400000#32, 0xf9401422#32, 0xeb03001f#32, 0x9a832018#32, 0xb5000c42#32, 0xf941cc35#32, 0xb10006bf#32, 0x540001a0#32, 0xb40004b5#32,
    0x8b1802b6#32, 0xd2801ac8#32, 0xaa1603e0#32, 0xd4000001#32, 0xeb0002df#32, 0x54000680#32, 0x91000280#32, 0x92800002#32, 0xf9401401#32, 0xf901cc02#32,
    0xb5000681#32, 0x91000297#32, 0xd2800056#32, 0xd2800005#32, 0x12800004#32, 0x52800443#32, 0x52800002#32, 0xf9401ae1#32, 0xd2800000#32, 0x9ac122d6#32,
    0x9b167f01#32, 0x94000000#32, 0xb100041f#32, 0x540006a0#32, 0xd10006c1#32, 0xd34cff16#32, 0xf9401ae2#32, 0x8b180015#32, 0xd1000700#32, 0x9b167c36#32,
    0xea0002bf#32, 0x91000441#32, 0x1a9f17e0#32, 0xa90286f6#32, 0xf90026f5#32, 0x1400003e#32, 0xd2801ac8#32, 0xd2800000#32, 0xd4000001#32, 0xcb0003e2#32,
    0xd1000716#32, 0x8a160056#32, 0x8b0002d6#32, 0xf901cc36#32, 0x8b1806d6#32, 0xaa1603e0#32, 0xd4000001#32, 0xeb0002df#32, 0x54fffac1#32, 0xf941cc20#32,
    0xcb1802d5#32, 0xaa1803e1#32, 0xd2800005#32, 0x12800004#32, 0x52800643#32, 0x52800002#32, 0x94000000#32, 0x91000281#32, 0xd34cff00#32, 0xf9001420#32,
    0xf901cc36#32, 0x14000025#32, 0xf9402415#32, 0xd1000700#32, 0xea0002bf#32, 0x1a9f17e0#32, 0x1400001f#32, 0xaa1803e1#32, 0xaa1503e0#32, 0x52800062#32,
    0x94000000#32, 0x34000360#32, 0x94000000#32, 0xb9400000#32, 0x7100981f#32, 0x540002e0#32, 0xa9425bf5#32, 0xa94363f7#32, 0x1400000b#32, 0xf9001c15#32,
    0x1400001b#32, 0xf9401020#32, 0xb4fff420#32, 0xf9400c33#32, 0xd1000400#32, 0x91000294#32, 0x9100a261#32, 0xa9018281#32, 0xa9007e7f#32, 0xaa1303e0#32,
    0xa94153f3#32, 0xa8c57bfd#32, 0xd65f03c0#32, 0xf9402435#32, 0xd1000700#32, 0xea0002bf#32, 0x1a9f17e0#32, 0x35fffc40#32, 0x91000280#32, 0x914006a2#32,
    0xf9401401#32, 0xf9002402#32, 0xf9402002#32, 0xd1000421#32, 0xf9001401#32, 0xb4fffcc2#32, 0xf9000455#32, 0x91000281#32, 0x52800ca3#32, 0xf9400282#32,
    0xd2800c80#32, 0xf9002035#32, 0xf90002a2#32, 0xf9402022#32, 0xb9001043#32, 0xf9402033#32, 0xa9425bf5#32, 0x91006273#32, 0xa94363f7#32, 0x17ffffde#32]
  align := 4
  symbols := [("__malloc_alloc_meta", 0)]
  relocs := [
    { off := 12, kind := .adrpHi21, sym := "__malloc_context" },
    { off := 16, kind := .addLo12, sym := "__malloc_context" },
    { off := 28, kind := .addLo12, sym := "__malloc_context" },
    { off := 108, kind := .adrpHi21, sym := "__libc" },
    { off := 112, kind := .addLo12, sym := "__libc" },
    { off := 160, kind := .call26, sym := "memcpy" },
    { off := 192, kind := .addLo12, sym := "__malloc_context" },
    { off := 204, kind := .ldst64Lo12, sym := "__malloc_context" },
    { off := 228, kind := .adrpHi21, sym := "__libc", addend := 48 },
    { off := 244, kind := .ldst64Lo12, sym := "__libc", addend := 48 },
    { off := 304, kind := .addLo12, sym := "__malloc_context" },
    { off := 324, kind := .addLo12, sym := "__malloc_context" },
    { off := 364, kind := .call26, sym := "__mmap" },
    { off := 504, kind := .call26, sym := "__mmap" },
    { off := 508, kind := .addLo12, sym := "__malloc_context" },
    { off := 560, kind := .call26, sym := "mprotect" },
    { off := 568, kind := .call26, sym := "___errno_location" },
    { off := 620, kind := .addLo12, sym := "__malloc_context" },
    { off := 672, kind := .addLo12, sym := "__malloc_context" },
    { off := 708, kind := .addLo12, sym := "__malloc_context" },
    { off := 716, kind := .ldst64Lo12, sym := "__malloc_context" }]

def mallocng_blk08_alloc_slot : Obj.CodeBlock where
  code := mallocngWordsLE [
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
  align := 4
  symbols := [("alloc_slot", 0)]
  relocs := [
    { off := 20, kind := .adrpHi21, sym := "__malloc_context" },
    { off := 24, kind := .addLo12, sym := "__malloc_context" },
    { off := 116, kind := .addLo12, sym := "__malloc_context" },
    { off := 248, kind := .addLo12, sym := "__malloc_context" },
    { off := 312, kind := .addLo12, sym := "__malloc_context" },
    { off := 340, kind := .adrpHi21, sym := "__malloc_size_classes" },
    { off := 344, kind := .addLo12, sym := "__malloc_size_classes" },
    { off := 556, kind := .adrpHi21, sym := "debruijn32.4681" },
    { off := 560, kind := .addLo12, sym := "debruijn32.4681" },
    { off := 596, kind := .addLo12, sym := "__malloc_context" },
    { off := 640, kind := .adrpHi21, sym := "__malloc_size_classes" },
    { off := 644, kind := .addLo12, sym := "__malloc_size_classes" },
    { off := 660, kind := .call26, sym := "__malloc_alloc_meta" },
    { off := 672, kind := .addLo12, sym := "__malloc_context" },
    { off := 680, kind := .adrpHi21, sym := "__libc", addend := 48 },
    { off := 688, kind := .ldst64Lo12, sym := "__libc", addend := 48 },
    { off := 704, kind := .adrpHi21, sym := "small_cnt_tab" },
    { off := 708, kind := .addLo12, sym := "small_cnt_tab" },
    { off := 760, kind := .adrpHi21, sym := "med_cnt_tab" },
    { off := 764, kind := .addLo12, sym := "med_cnt_tab" },
    { off := 860, kind := .addLo12, sym := "__malloc_context" },
    { off := 988, kind := .addLo12, sym := "__malloc_context" },
    { off := 1108, kind := .call26, sym := "__mmap" },
    { off := 1132, kind := .addLo12, sym := "__malloc_context" },
    { off := 1188, kind := .addLo12, sym := "__malloc_context" },
    { off := 1352, kind := .addLo12, sym := "__malloc_context" },
    { off := 1372, kind := .addLo12, sym := "__malloc_context" },
    { off := 1584, kind := .addLo12, sym := "__malloc_context" },
    { off := 1664, kind := .adrpHi21, sym := "debruijn32.4681" },
    { off := 1672, kind := .addLo12, sym := "debruijn32.4681" },
    { off := 1680, kind := .addLo12, sym := "__malloc_size_classes" },
    { off := 1784, kind := .addLo12, sym := "__malloc_context" },
    { off := 1792, kind := .addLo12, sym := "__malloc_size_classes" },
    { off := 1856, kind := .addLo12, sym := "__malloc_context" },
    { off := 1920, kind := .addLo12, sym := "__malloc_size_classes" }]

def mallocng_blk09_libc_malloc_impl : Obj.CodeBlock where
  code := mallocngWordsLE [
    0xa9bb7bfd#32, 0x92820021#32, 0xf2efffe1#32, 0x910003fd#32, 0xeb01001f#32, 0x54000da8#32, 0xa90153f3#32, 0xaa0003f4#32, 0xd29ffd60#32, 0xa9025bf5#32,
    0xf2a00020#32, 0xeb00029f#32, 0xa90363f7#32, 0xf90023f9#32, 0x54000d48#32, 0x91000e93#32, 0xf1027e7f#32, 0xd344fe73#32, 0x540003c9#32, 0x91000661#32,
    0x529cc524#32, 0x72a0ed64#32, 0x90000003#32, 0x53027c20#32, 0x91000063#32, 0x2a410400#32, 0x90000002#32, 0x91000042#32, 0x2a400800#32, 0x2a401000#32,
    0x2a402000#32, 0x11000405#32, 0x0a2000a0#32, 0x1b047c00#32, 0x531b7c00#32, 0x38604873#32, 0x51000673#32, 0x531e7673#32, 0x11000663#32, 0x11000a60#32,
    0x7863d843#32, 0xeb03003f#32, 0x1a938013#32, 0x93407e75#32, 0x7873d840#32, 0xeb00003f#32, 0x54000069#32, 0x11000673#32, 0x93407e75#32, 0x90000000#32,
    0x91000000#32, 0x90000018#32, 0x39400c00#32, 0x72001c1f#32, 0x54001081#32, 0x91002aa0#32, 0x90000019#32, 0x91000321#32, 0xf8607836#32, 0xf10002df#32,
    0x7a430a64#32, 0x540002ed#32, 0x71007e7f#32, 0x7a46da64#32, 0x54000fa0#32, 0x37000f93#32, 0x9100eab5#32, 0xf8757820#32, 0xb5000f20#32, 0x32000262#32,
    0x93407c40#32, 0x91002803#32, 0x9100e800#32, 0xf8637836#32, 0xf8607820#32, 0xb40000b6#32, 0xb9401ac1#32, 0x35000081#32, 0xb9401ec1#32, 0x35000041#32,
    0x91000c00#32, 0xf100301f#32, 0x54000d68#32, 0x2a0203f3#32, 0xb4000d36#32, 0xb9401ac1#32, 0x4b0103e2#32, 0x6a010042#32, 0x54000ca0#32, 0x4b0203e0#32,
    0x529cc524#32, 0x0a020000#32, 0x72a0ed64#32, 0x90000003#32, 0x91000063#32, 0x91000339#32, 0x4b020021#32, 0x1b047c00#32, 0xb9001ac1#32, 0xb9400f33#32,
    0x531b7c00#32, 0x38604877#32, 0x92401ef5#32, 0x91000300#32, 0x94000000#32, 0x394082c0#32, 0xf240101f#32, 0x54000c01#32, 0xf94012c4#32, 0xf274cc9f#32,
    0x54000ba0#32, 0x9274cc84#32, 0xd1004084#32, 0x14000060#32, 0x94000000#32, 0xaa0003e1#32, 0x52800182#32, 0xd2800000#32, 0xb9000022#32, 0x1400009a#32,
    0x91005295#32, 0xd2800005#32, 0xaa1503e1#32, 0x12800004#32, 0x52800443#32, 0x52800062#32, 0xd2800000#32, 0x94000000#32, 0xaa0003f3#32, 0xb100041f#32,
    0x54000640#32, 0x90000000#32, 0x91000000#32, 0x90000018#32, 0x39400c00#32, 0x72001c1f#32, 0x54000361#32, 0x90000019#32, 0x91000322#32, 0x394e4040#32,
    0x7103fc1f#32, 0x54000320#32, 0x11000400#32, 0x390e4040#32, 0x94000000#32, 0xaa0003f6#32, 0xb40003a0#32, 0x91000320#32, 0xf9000ad3#32, 0xf9000276#32,
    0xd2820261#32, 0x8b010282#32, 0xb9001edf#32, 0xb9400c01#32, 0x9274cc42#32, 0xb27b1842#32, 0xd2800015#32, 0x11000433#32, 0x52800017#32, 0xb9000c13#32,
    0xb9001adf#32, 0xf90012c2#32, 0x17ffffc5#32, 0x91000300#32, 0x94000000#32, 0x17ffffe4#32, 0x910d4041#32, 0x910dc042#32, 0x3800143f#32, 0xeb01005f#32,
    0x54ffffc1#32, 0x91000320#32, 0x52800021#32, 0x390e4001#32, 0x17ffffe2#32, 0x91000300#32, 0x94000000#32, 0xaa1503e1#32, 0xaa1303e0#32, 0x94000000#32,
    0xd2800000#32, 0xa94153f3#32, 0xa9425bf5#32, 0xa94363f7#32, 0xf94023f9#32, 0x14000058#32, 0x91000300#32, 0x94000000#32, 0x17ffff7b#32, 0xaa1403e1#32,
    0x2a1303e0#32, 0x94000000#32, 0x2a0003f7#32, 0x37f800e0#32, 0x91000320#32, 0x93407ef5#32, 0x8b33cc02#32, 0xb9400c13#32, 0xf9402856#32, 0x17ffffa0#32,
    0x91000300#32, 0x94000000#32, 0x17ffffea#32, 0x794042c1#32, 0x90000000#32, 0x91000000#32, 0xd3462c21#32, 0x78617804#32, 0xd37c3c84#32, 0xf9400ac2#32,
    0xcb140083#32, 0xd1001086#32, 0xd1001063#32, 0x91004042#32, 0x12001e61#32, 0xd344fc65#32, 0x9b150880#32, 0x8b060006#32, 0x385fd004#32, 0x34000084#32,
    0x785fe001#32, 0x11000421#32, 0x12001c21#32, 0x385fc004#32, 0x34000084#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0xeb21c0bf#32, 0x54000182#32,
    0xaa4314a3#32, 0x2a2503e7#32, 0xaa430863#32, 0xaa431063#32, 0x0a030028#32, 0x0a030021#32, 0xeb0100bf#32, 0x0b070101#32, 0x1a883021#32, 0xeb21c0bf#32,
    0x54fffe23#32, 0x34000121#32, 0x531c6c22#32, 0x128003e3#32, 0x381fd003#32, 0x781fe001#32, 0x8b22c000#32, 0x381fc01f#32, 0xf9400ac2#32, 0x91004042#32,
    0xcb020002#32, 0x12001ee1#32, 0x381fd001#32, 0xcb0000c3#32, 0xd344fc42#32, 0x781fe002#32, 0x6b140074#32, 0x54000120#32, 0x4b1403e1#32, 0x7100129f#32,
    0x3821c8df#32, 0x540001cd#32, 0x381fb0df#32, 0x52801404#32, 0xb81fc0d4#32, 0x385fd001#32, 0x12001021#32, 0x0b010081#32, 0x381fd001#32, 0xa94153f3#32,
    0xa9425bf5#32, 0xa94363f7#32, 0xf94023f9#32, 0xa8c57bfd#32, 0xd65f03c0#32, 0x385fd001#32, 0x531b0a84#32, 0x17fffff5#32]
  align := 4
  symbols := [("__libc_malloc_impl", 0)]
  relocs := [
    { off := 88, kind := .adrpHi21, sym := "debruijn32.4681" },
    { off := 96, kind := .addLo12, sym := "debruijn32.4681" },
    { off := 104, kind := .adrpHi21, sym := "__malloc_size_classes" },
    { off := 108, kind := .addLo12, sym := "__malloc_size_classes" },
    { off := 196, kind := .adrpHi21, sym := "__libc" },
    { off := 200, kind := .addLo12, sym := "__libc" },
    { off := 204, kind := .adrpHi21, sym := "__malloc_lock" },
    { off := 224, kind := .adrpHi21, sym := "__malloc_context" },
    { off := 228, kind := .addLo12, sym := "__malloc_context" },
    { off := 372, kind := .adrpHi21, sym := "debruijn32.4681" },
    { off := 376, kind := .addLo12, sym := "debruijn32.4681" },
    { off := 380, kind := .addLo12, sym := "__malloc_context" },
    { off := 412, kind := .addLo12, sym := "__malloc_lock" },
    { off := 416, kind := .call26, sym := "__unlock" },
    { off := 456, kind := .call26, sym := "___errno_location" },
    { off := 508, kind := .call26, sym := "__mmap" },
    { off := 524, kind := .adrpHi21, sym := "__libc" },
    { off := 528, kind := .addLo12, sym := "__libc" },
    { off := 532, kind := .adrpHi21, sym := "__malloc_lock" },
    { off := 548, kind := .adrpHi21, sym := "__malloc_context" },
    { off := 552, kind := .addLo12, sym := "__malloc_context" },
    { off := 576, kind := .call26, sym := "__malloc_alloc_meta" },
    { off := 588, kind := .addLo12, sym := "__malloc_context" },
    { off := 652, kind := .addLo12, sym := "__malloc_lock" },
    { off := 656, kind := .call26, sym := "__lock" },
    { off := 684, kind := .addLo12, sym := "__malloc_context" },
    { off := 700, kind := .addLo12, sym := "__malloc_lock" },
    { off := 704, kind := .call26, sym := "__unlock" },
    { off := 716, kind := .call26, sym := "munmap" },
    { off := 744, kind := .addLo12, sym := "__malloc_lock" },
    { off := 748, kind := .call26, sym := "__lock" },
    { off := 764, kind := .call26, sym := "alloc_slot" },
    { off := 776, kind := .addLo12, sym := "__malloc_context" },
    { off := 800, kind := .addLo12, sym := "__malloc_lock" },
    { off := 804, kind := .call26, sym := "__unlock" },
    { off := 816, kind := .adrpHi21, sym := "__malloc_size_classes" },
    { off := 820, kind := .addLo12, sym := "__malloc_size_classes" }]

def mallocng_blk10_malloc_allzerop : Obj.CodeBlock where
  code := mallocngWordsLE [
    0xf2400c04#32, 0x540002a1#32, 0x385fc003#32, 0x385fd001#32, 0x785fe002#32, 0x12001021#32, 0x34000103#32, 0x34000062#32, 0x3900009f#32, 0xd4207d00#32,
    0xb85f8002#32, 0x529fffe3#32, 0x6b03005f#32, 0x54ffff6d#32, 0x531c6c43#32, 0x928001e4#32, 0xcb23c083#32, 0x8b030004#32, 0xf8636800#32, 0xf9400803#32,
    0xeb03009f#32, 0x54000080#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0x39408005#32, 0x120010a3#32, 0x6b03003f#32, 0x54ffff4c#32, 0xb9401803#32,
    0x1ac12463#32, 0x3707fee3#32, 0xb9401c03#32, 0x1ac12463#32, 0x3707fe83#32, 0x9274cc03#32, 0x90000004#32, 0xf9400084#32, 0xf9400063#32, 0xeb04007f#32,
    0x54fffdc1#32, 0x79404003#32, 0xd3462c64#32, 0x7100bc9f#32, 0x54000368#32, 0x90000003#32, 0x91000067#32, 0x93407c86#32, 0x7864d8e4#32, 0x1b047c21#32,
    0x6b01005f#32, 0x54fffc6b#32, 0x0b010081#32, 0x6b01005f#32, 0x54fffc0a#32, 0xf9401001#32, 0xf274cc3f#32, 0x540002c1#32, 0x91000063#32, 0xf24010bf#32,
    0x52800000#32, 0x78667862#32, 0xd37c3c42#32, 0x540001e1#32, 0xf274cc3f#32, 0x540001a0#32, 0x9274cc21#32, 0xd1004021#32, 0xeb02003f#32, 0x1a9f27e0#32,
    0x14000008#32, 0x121a1463#32, 0x713f007f#32, 0x54fff9a1#32, 0xf9401000#32, 0xf274cc1f#32, 0x54000121#32, 0x52800020#32, 0xd65f03c0#32, 0x9274cc20#32,
    0xd344fc00#32, 0xd1000400#32, 0xeb22c01f#32, 0x54fff863#32, 0x17ffffe6#32, 0x9274cc00#32, 0xd344fc00#32, 0xd1000400#32, 0xeb22c01f#32, 0x54fffe82#32,
    0x17ffffbc#32]
  align := 4
  symbols := [("__malloc_allzerop", 0)]
  relocs := [
    { off := 144, kind := .adrpHi21, sym := "__malloc_context" },
    { off := 148, kind := .ldst64Lo12, sym := "__malloc_context" },
    { off := 180, kind := .adrpHi21, sym := "__malloc_size_classes" },
    { off := 184, kind := .addLo12, sym := "__malloc_size_classes" },
    { off := 232, kind := .addLo12, sym := "__malloc_size_classes" }]

def mallocng_blk11_posix_memalign : Obj.CodeBlock where
  code := mallocngWordsLE [
    0xf1001c3f#32, 0x54000269#32, 0xa9be7bfd#32, 0xaa0103e3#32, 0xaa0203e1#32, 0x910003fd#32, 0xf9000bf3#32, 0xaa0003f3#32, 0xaa0303e0#32, 0x94000000#32,
    0xaa0003e1#32, 0xb40000c0#32, 0x52800000#32, 0xf9000261#32, 0xf9400bf3#32, 0xa8c27bfd#32, 0xd65f03c0#32, 0x94000000#32, 0xb9400000#32, 0x17fffffb#32,
    0x528002c0#32, 0xd65f03c0#32]
  align := 4
  symbols := [("posix_memalign", 0)]
  relocs := [
    { off := 36, kind := .call26, sym := "aligned_alloc" },
    { off := 68, kind := .call26, sym := "___errno_location" }]

def mallocng_blk12_aligned_alloc : Obj.CodeBlock where
  code := mallocngWordsLE [
    0xa9be7bfd#32, 0xcb0003e2#32, 0xea22001f#32, 0x910003fd#32, 0x8a000042#32, 0x540003e1#32, 0xaa2203e3#32, 0xa90153f3#32, 0xaa0103f4#32, 0xeb14007f#32,
    0xb2408be1#32, 0xfa412042#32, 0x540003e8#32, 0x90000001#32, 0xb9400021#32, 0x34000081#32, 0x90000001#32, 0xb9400021#32, 0x34000321#32, 0xf100401f#32,
    0xd1004281#32, 0xd2800213#32, 0x9a932013#32, 0x8b130020#32, 0x94000000#32, 0xb4001420#32, 0xf2400c03#32, 0x54000461#32, 0x385fc001#32, 0x385fd002#32,
    0x785fe004#32, 0x12001042#32, 0x340002c1#32, 0x34000224#32, 0x3900007f#32, 0xd4207d00#32, 0x94000000#32, 0xaa0003e1#32, 0x528002c2#32, 0xd2800000#32,
    0xb9000022#32, 0xa8c27bfd#32, 0xd65f03c0#32, 0x94000000#32, 0xaa0003e1#32, 0x52800182#32, 0xd2800000#32, 0xb9000022#32, 0xa94153f3#32, 0x17fffff8#32,
    0xb85f8004#32, 0x529fffe1#32, 0x6b01009f#32, 0x54fffdad#32, 0x531c6c81#32, 0x928001e3#32, 0xcb21c061#32, 0x8b010003#32, 0xf8616801#32, 0xf9400826#32,
    0xeb06007f#32, 0x54000080#32, 0xd2800000#32, 0x3900001f#32, 0xd4207d00#32, 0x39408027#32, 0x120010e3#32, 0x6b03005f#32, 0x54ffff4c#32, 0xb9401823#32,
    0x1ac22463#32, 0x3707fee3#32, 0xb9401c23#32, 0x1ac22463#32, 0x3707fe83#32, 0x9274cc23#32, 0x90000005#32, 0xf94000a5#32, 0xf9400063#32, 0xeb05007f#32,
    0x54fffdc1#32, 0x79404023#32, 0xd3462c65#32, 0x7100bcbf#32, 0x54000868#32, 0x90000003#32, 0x91000063#32, 0x7865d863#32, 0x1b037c48#32, 0x6b08009f#32,
    0x54fffc8b#32, 0x0b080063#32, 0x6b03009f#32, 0x54fffc2a#32, 0xf9401021#32, 0xf274cc3f#32, 0x54000120#32, 0x9274cc21#32, 0xd344fc23#32, 0xd1000463#32,
    0xeb24c07f#32, 0x54fffb23#32, 0xd1004024#32, 0xf24010ff#32, 0x540000a0#32, 0x90000001#32, 0x91000021#32, 0x7865d824#32, 0xd37c3c84#32, 0x11000443#32,
    0x910040c6#32, 0xd1000673#32, 0xcb0003e1#32, 0x93407c63#32, 0xea130021#32, 0x9b041863#32, 0xd1001063#32, 0x540004c0#32, 0x8b010000#32, 0x529fffe5#32,
    0xcb060001#32, 0xd344fc21#32, 0x6b05003f#32, 0x540006a8#32, 0x381fc01f#32, 0x781fe001#32, 0x381fd002#32, 0xcb000061#32, 0x6b140021#32, 0x2a0203e5#32,
    0x54000160#32, 0x4b0103e5#32, 0x7100103f#32, 0x3825c87f#32, 0x540005ed#32, 0x381fb07f#32, 0xb81fc061#32, 0x385fd001#32, 0x12001021#32, 0x51018021#32,
    0x12001c25#32, 0x92401c42#32, 0x381fd005#32, 0x128003e3#32, 0x9b041844#32, 0xcb040001#32, 0xd344fc21#32, 0x381fd083#32, 0x781fe081#32, 0xa94153f3#32,
    0x17ffff93#32, 0x121a1463#32, 0x713f007f#32, 0x54fff4a1#32, 0x17ffffc4#32, 0xcb000061#32, 0x6b140021#32, 0x54000160#32, 0x4b0103e2#32, 0x7100103f#32,
    0x3822c87f#32, 0x5400014d#32, 0x381fb07f#32, 0xb81fc061#32, 0x385fd002#32, 0x12001042#32, 0x51018042#32, 0x12001c42#32, 0x381fd002#32, 0xa94153f3#32,
    0x17ffff7f#32, 0x385fd002#32, 0x12001042#32, 0x0b011441#32, 0x12001c22#32, 0x17fffff9#32, 0x52800025#32, 0xb81f8001#32, 0x381fc005#32, 0x781fe01f#32,
    0x17ffffca#32, 0x385fd003#32, 0x12001063#32, 0x0b011461#32, 0x12001c25#32, 0x17ffffd4#32, 0xa94153f3#32, 0x17ffff6e#32]
  align := 4
  symbols := [("aligned_alloc", 0)]
  relocs := [
    { off := 52, kind := .adrpHi21, sym := "__malloc_replaced" },
    { off := 56, kind := .ldst32Lo12, sym := "__malloc_replaced" },
    { off := 64, kind := .adrpHi21, sym := "__aligned_alloc_replaced" },
    { off := 68, kind := .ldst32Lo12, sym := "__aligned_alloc_replaced" },
    { off := 96, kind := .call26, sym := "__libc_malloc_impl" },
    { off := 144, kind := .call26, sym := "___errno_location" },
    { off := 172, kind := .call26, sym := "___errno_location" },
    { off := 304, kind := .adrpHi21, sym := "__malloc_context" },
    { off := 308, kind := .ldst64Lo12, sym := "__malloc_context" },
    { off := 340, kind := .adrpHi21, sym := "__malloc_size_classes" },
    { off := 344, kind := .addLo12, sym := "__malloc_size_classes" },
    { off := 420, kind := .adrpHi21, sym := "__malloc_size_classes" },
    { off := 424, kind := .addLo12, sym := "__malloc_size_classes" }]

def mallocng_blk13_realloc : Obj.CodeBlock where
  code := mallocngWordsLE [0x14000000#32]
  align := 4
  symbols := [("realloc", 0)]
  relocs := [
    { off := 0, kind := .jump26, sym := "__libc_realloc" }]

def mallocng_blk14_libc_realloc : Obj.CodeBlock where
  code := mallocngWordsLE [
    0xa9bb7bfd#32, 0x910003fd#32, 0xa9025bf5#32, 0xaa0103f5#32, 0xb4000260#32, 0xa90153f3#32, 0xaa0003f3#32, 0x92820020#32, 0xf2efffe0#32, 0xeb00003f#32,
    0x54001488#32, 0xa90363f7#32, 0xf2400e61#32, 0xa9046bf9#32, 0x54000321#32, 0x385fc260#32, 0x385fd262#32, 0x785fe263#32, 0x12001044#32, 0x34000180#32,
    0x340000e3#32, 0x3900003f#32, 0xd4207d00#32, 0xa9425bf5#32, 0xaa0103e0#32, 0xa8c57bfd#32, 0x14000000#32, 0xb85f8263#32, 0x529fffe0#32, 0x6b00007f#32,
    0x54fffeed#32, 0x531c6c60#32, 0x928001e1#32, 0xcb20c020#32, 0x8b000261#32, 0xf8606a76#32, 0xf9400ac0#32, 0xeb00003f#32, 0x54000080#32, 0xd2800000#32,
    0x3900001f#32, 0xd4207d00#32, 0x394082c5#32, 0x120010a1#32, 0x6b01009f#32, 0x54ffff4c#32, 0xb9401ac1#32, 0x1ac42421#32, 0x3707fee1#32, 0xb9401ec1#32,
    0x1ac42421#32, 0x3707fe81#32, 0x9274cec1#32, 0x90000006#32, 0xf94000c6#32, 0xf9400021#32, 0xeb06003f#32, 0x54fffdc1#32, 0x794042c7#32, 0xd3462ce6#32,
    0x7100bcdf#32, 0x54000da8#32, 0x90000001#32, 0x91000021#32, 0x7866d821#32, 0x1b017c88#32, 0x6b08007f#32, 0x54fffc8b#32, 0x0b080021#32, 0x6b01007f#32,
    0x54fffc2a#32, 0xf94012c1#32, 0xf274cc3f#32, 0x54000120#32, 0x9274cc34#32, 0xd344fe88#32, 0xd1000508#32, 0xeb23c11f#32, 0x54fffb23#32, 0xd1004283#32,
    0xf24010bf#32, 0x540000a0#32, 0x90000003#32, 0x91000063#32, 0x7866d874#32, 0xd37c3e83#32, 0x91004005#32, 0x92401c94#32, 0xd1001068#32, 0x71027c5f#32,
    0x53057c49#32, 0xd3451c42#32, 0x9b031694#32, 0x8b080285#32, 0x54000109#32, 0x7100153f#32, 0x54fff8e1#32, 0xb85fc0a2#32, 0xf100105f#32, 0x54fff889#32,
    0x385fb0a3#32, 0x35fff843#32, 0xcb1300a3#32, 0xeb02007f#32, 0x54fff7e3#32, 0xcb0200b7#32, 0x394002e2#32, 0x35fff782#32, 0x38686a98#32, 0x35fff758#32,
    0xd29ffd62#32, 0xf2a00022#32, 0xeb02007f#32, 0x9a829068#32, 0xeb0802bf#32, 0x54000ac8#32, 0x91000ea1#32, 0xf1027c3f#32, 0xd344fc21#32, 0x11000422#32,
    0x540003c9#32, 0x91000421#32, 0x529cc529#32, 0x72a0ed69#32, 0x90000002#32, 0x53027c20#32, 0x91000042#32, 0x2a410400#32, 0x90000007#32, 0x910000e8#32,
    0x2a400800#32, 0x2a401000#32, 0x2a402000#32, 0x1100040a#32, 0x0a200140#32, 0x1b097c00#32, 0x531b7c00#32, 0x38604840#32, 0x51000400#32, 0x531e7400#32,
    0x11000402#32, 0x7862d908#32, 0xeb08003f#32, 0x54000069#32, 0x11000c02#32, 0x11000800#32, 0x910000e7#32, 0x7860d8e0#32, 0xeb00003f#32, 0x1a829442#32,
    0x6b0200df#32, 0x5400038d#32, 0xaa1503e0#32, 0x94000000#32, 0xaa0003f4#32, 0xb4000bc0#32, 0xcb1302e2#32, 0xaa1303e1#32, 0xeb15005f#32, 0x9a959042#32,
    0x94000000#32, 0xaa1303e0#32, 0x94000000#32, 0xa94363f7#32, 0xa9446bf9#32, 0xaa1403e0#32, 0xa94153f3#32, 0xa9425bf5#32, 0xa8c57bfd#32, 0xd65f03c0#32,
    0x121a14e1#32, 0x713f003f#32, 0x54ffef61#32, 0x17ffff9a#32, 0x94000000#32, 0xd2800014#32, 0x52800181#32, 0xb9000001#32, 0x17fffff3#32, 0x6b150075#32,
    0x54000160#32, 0x4b1503e0#32, 0x710012bf#32, 0x3820c8bf#32, 0x5400018d#32, 0x381fb0bf#32, 0xb81fc0b5#32, 0x385fd275#32, 0x120012b5#32, 0x510182b5#32,
    0x12001ea4#32, 0x381fd264#32, 0xaa1303f4#32, 0xa94363f7#32, 0xa9446bf9#32, 0x17ffffe2#32, 0x385fd260#32, 0x12001000#32, 0x0b151415#32, 0x12001ea4#32,
    0x17fffff7#32, 0x7100bcdf#32, 0xfa4282a0#32, 0x54fff9a9#32, 0x121a14e7#32, 0x713f00ff#32, 0x54ffeb21#32, 0xcb140274#32, 0xd2820262#32, 0x8b0202b9#32,
    0x9274cc21#32, 0x8b140339#32, 0x9274cf3a#32, 0xeb1a003f#32, 0x540003e1#32, 0xb100041f#32, 0x54fff800#32, 0xf94012c2#32, 0x91004001#32, 0xd100535a#32,
    0xd34cff39#32, 0xf9000ac0#32, 0xcb140340#32, 0xb374cf22#32, 0xf90012c2#32, 0x383a683f#32, 0x6b150015#32, 0x8b140034#32, 0x8b1a003a#32, 0x54000120#32,
    0x4b1503e0#32, 0x531b0ab8#32, 0x710012bf#32, 0x3820cb5f#32, 0x5400008d#32, 0x52801418#32, 0x381fb35f#32, 0xb81fc355#32, 0x385fd280#32, 0x12001000#32,
    0x0b000318#32, 0x381fd298#32, 0xa94363f7#32, 0xa9446bf9#32, 0x17ffffb1#32, 0xaa1a03e2#32, 0x52800023#32, 0x94000000#32, 0x17ffffdf#32, 0xa94363f7#32,
    0xa9446bf9#32, 0x17ffffaa#32]
  align := 4
  symbols := [("__libc_realloc", 0)]
  relocs := [
    { off := 104, kind := .jump26, sym := "__libc_malloc_impl" },
    { off := 212, kind := .adrpHi21, sym := "__malloc_context" },
    { off := 216, kind := .ldst64Lo12, sym := "__malloc_context" },
    { off := 248, kind := .adrpHi21, sym := "__malloc_size_classes" },
    { off := 252, kind := .addLo12, sym := "__malloc_size_classes" },
    { off := 328, kind := .adrpHi21, sym := "__malloc_size_classes" },
    { off := 332, kind := .addLo12, sym := "__malloc_size_classes" },
    { off := 496, kind := .adrpHi21, sym := "debruijn32.5048" },
    { off := 504, kind := .addLo12, sym := "debruijn32.5048" },
    { off := 512, kind := .adrpHi21, sym := "__malloc_size_classes" },
    { off := 516, kind := .addLo12, sym := "__malloc_size_classes" },
    { off := 584, kind := .addLo12, sym := "__malloc_size_classes" },
    { off := 612, kind := .call26, sym := "__libc_malloc_impl" },
    { off := 640, kind := .call26, sym := "memcpy" },
    { off := 648, kind := .call26, sym := "__libc_free" },
    { off := 696, kind := .call26, sym := "___errno_location" },
    { off := 988, kind := .call26, sym := "__mremap" }]

def mallocng_blk15_vm_wait : Obj.CodeBlock where
  code := mallocngWordsLE [0xd65f03c0#32]
  align := 4
  symbols := [("__vm_wait", 0)]
  relocs := []

def mallocng_blk16_mmap : Obj.CodeBlock where
  code := mallocngWordsLE [
    0xa9bc7bfd#32, 0xf2402cbf#32, 0x910003fd#32, 0x54000381#32, 0xa90153f3#32, 0xaa0003f4#32, 0xb27ff7e0#32, 0xeb00003f#32, 0x540003a8#32, 0xa9025bf5#32,
    0x2a0303f3#32, 0x2a0203f6#32, 0x2a0403f5#32, 0x372003b3#32, 0x93407ec2#32, 0x93407ea4#32, 0xaa1403e0#32, 0x93407e63#32, 0xd2801bc8#32, 0xd4000001#32,
    0xf100029f#32, 0xba410800#32, 0x540000a1#32, 0x121c0673#32, 0x92800160#32, 0x7100827f#32, 0xda9f0000#32, 0xa94153f3#32, 0xa9425bf5#32, 0xa8c47bfd#32,
    0x14000000#32, 0x94000000#32, 0x528002c1#32, 0xb9000001#32, 0x92800000#32, 0xa8c47bfd#32, 0xd65f03c0#32, 0x94000000#32, 0x52800181#32, 0xb9000001#32,
    0xa94153f3#32, 0x17fffff9#32, 0xa90317e1#32, 0x94000000#32, 0xa94317e1#32, 0x17ffffe1#32]
  align := 4
  symbols := [("__mmap", 0), ("mmap", 0), ("mmap64", 0)]
  relocs := [
    { off := 120, kind := .jump26, sym := "__syscall_ret" },
    { off := 124, kind := .call26, sym := "___errno_location" },
    { off := 148, kind := .call26, sym := "___errno_location" },
    { off := 172, kind := .call26, sym := "__vm_wait" }]

def mallocng_blk17_mprotect : Obj.CodeBlock where
  code := mallocngWordsLE [
    0xa9bf7bfd#32, 0x90000004#32, 0xaa0003e3#32, 0x910003fd#32, 0xf9400084#32, 0xd2801c48#32, 0x93407c42#32, 0xd1000480#32, 0xcb0403e4#32, 0x8b010001#32,
    0x8a040060#32, 0x8b010063#32, 0x8a040061#32, 0xcb000021#32, 0xd4000001#32, 0x94000000#32, 0xa8c17bfd#32, 0xd65f03c0#32]
  align := 4
  symbols := [("__mprotect", 0), ("mprotect", 0)]
  relocs := [
    { off := 4, kind := .adrpHi21, sym := "__libc", addend := 48 },
    { off := 16, kind := .ldst64Lo12, sym := "__libc", addend := 48 },
    { off := 60, kind := .call26, sym := "__syscall_ret" }]

def mallocng_blk18_mremap : Obj.CodeBlock where
  code := mallocngWordsLE [
    0xa9b97bfd#32, 0x910003fd#32, 0xf9000bf3#32, 0x2a0303f3#32, 0xf90037e4#32, 0xb27ff7e3#32, 0xeb03005f#32, 0x54000148#32, 0xd2800004#32, 0x370801d3#32,
    0x93407e63#32, 0xd2801b08#32, 0xd4000001#32, 0x94000000#32, 0xf9400bf3#32, 0xa8c77bfd#32, 0xd65f03c0#32, 0x94000000#32, 0xaa0003e1#32, 0x52800182#32,
    0x92800000#32, 0xb9000022#32, 0x17fffff8#32, 0xa90287e0#32, 0xf9001fe2#32, 0x94000000#32, 0x9101c3e0#32, 0x910183e5#32, 0x128000e3#32, 0xa90403e0#32,
    0xf9002be5#32, 0x290b7fe3#32, 0xf94017e0#32, 0xa9430be1#32, 0xf94037e4#32, 0x17ffffe7#32]
  align := 4
  symbols := [("__mremap", 0), ("mremap", 0)]
  relocs := [
    { off := 52, kind := .call26, sym := "__syscall_ret" },
    { off := 68, kind := .call26, sym := "___errno_location" },
    { off := 100, kind := .call26, sym := "__vm_wait" }]

def mallocng_blk19_munmap : Obj.CodeBlock where
  code := mallocngWordsLE [
    0xa9be7bfd#32, 0x910003fd#32, 0xa90153f3#32, 0xaa0003f4#32, 0xaa0103f3#32, 0x94000000#32, 0xaa1403e0#32, 0xaa1303e1#32, 0xd2801ae8#32, 0xd4000001#32,
    0x94000000#32, 0xa94153f3#32, 0xa8c27bfd#32, 0xd65f03c0#32]
  align := 4
  symbols := [("__munmap", 0), ("munmap", 0)]
  relocs := [
    { off := 20, kind := .call26, sym := "__vm_wait" },
    { off := 40, kind := .call26, sym := "__syscall_ret" }]

def mallocng_blk20_memcpy : Obj.CodeBlock where
  code := mallocngWordsLE [
    0x8b020024#32, 0x8b020005#32, 0xf102005f#32, 0x540007a8#32, 0xf100805f#32, 0x540003e8#32, 0xf100405f#32, 0x540000c3#32, 0xa9401c26#32, 0xa97f348c#32,
    0xa9001c06#32, 0xa93f34ac#32, 0xd65f03c0#32, 0x361800e2#32, 0xf9400026#32, 0xf85f8087#32, 0xf9000006#32, 0xf81f80a7#32, 0xd65f03c0#32, 0xd503201f#32,
    0x361000c2#32, 0xb9400026#32, 0xb85fc088#32, 0xb9000006#32, 0xb81fc0a8#32, 0xd65f03c0#32, 0xb4000102#32, 0xd341fc4e#32, 0x39400026#32, 0x385ff08a#32,
    0x386e6828#32, 0x39000006#32, 0x382e6808#32, 0x381ff0aa#32, 0xd65f03c0#32, 0xd503201f#32, 0xa9401c26#32, 0xa9412428#32, 0xa97e2c8a#32, 0xa97f348c#32,
    0xf101005f#32, 0x540000e8#32, 0xa9001c06#32, 0xa9012408#32, 0xa93e2caa#32, 0xa93f34ac#32, 0xd65f03c0#32, 0xd503201f#32, 0xa9423c2e#32, 0xa9434430#32,
    0xf101805f#32, 0x540000a9#32, 0xa97c0c82#32, 0xa97d1081#32, 0xa93c0ca2#32, 0xa93d10a1#32, 0xa9001c06#32, 0xa9012408#32, 0xa9023c0e#32, 0xa9034410#32,
    0xa93e2caa#32, 0xa93f34ac#32, 0xd65f03c0#32, 0xd503201f#32, 0xa940342c#32, 0x92400c0e#32, 0x927cec03#32, 0xcb0e0021#32, 0x8b0e0042#32, 0xa9411c26#32,
    0xa900340c#32, 0xa9422428#32, 0xa9432c2a#32, 0xa9c4342c#32, 0xf1024042#32, 0x54000169#32, 0xa9011c66#32, 0xa9411c26#32, 0xa9022468#32, 0xa9422428#32,
    0xa9032c6a#32, 0xa9432c2a#32, 0xa984346c#32, 0xa9c4342c#32, 0xf1010042#32, 0x54fffee8#32, 0xa97c3c8e#32, 0xa9011c66#32, 0xa97d1c86#32, 0xa9022468#32,
    0xa97e2488#32, 0xa9032c6a#32, 0xa97f2c8a#32, 0xa904346c#32, 0xa93c3cae#32, 0xa93d1ca6#32, 0xa93e24a8#32, 0xa93f2caa#32, 0xd65f03c0#32]
  align := 4
  symbols := [("memcpy", 0)]
  relocs := []

def mallocng_blk21_memset : Obj.CodeBlock where
  code := mallocngWordsLE [
    0x4e010c20#32, 0x8b020004#32, 0xf101805f#32, 0x540003a8#32, 0xf100405f#32, 0x54000202#32, 0x4e083c01#32, 0x361800a2#32, 0xf9000001#32, 0xf81f8081#32,
    0xd65f03c0#32, 0xd503201f#32, 0x36100082#32, 0xb9000001#32, 0xb81fc081#32, 0xd65f03c0#32, 0xb4000082#32, 0x39000001#32, 0x36080042#32, 0x781fe081#32,
    0xd65f03c0#32, 0x3d800000#32, 0x373000c2#32, 0x3c9f0080#32, 0x36280062#32, 0x3d800400#32, 0x3c9e0080#32, 0xd65f03c0#32, 0x3d800400#32, 0xad010000#32,
    0xad3f0080#32, 0xd65f03c0#32, 0x12001c21#32, 0x927cec03#32, 0x3d800000#32, 0xf102805f#32, 0x7a402820#32, 0x54000241#32, 0xd53b00e5#32, 0x924010a5#32,
    0xf10010bf#32, 0x540001c1#32, 0x3d800460#32, 0xad010060#32, 0x927ae463#32, 0xcb030082#32, 0xd1020042#32, 0xd503201f#32, 0x91010063#32, 0xd50b7423#32,
    0xf1010042#32, 0x54ffffa8#32, 0xad3e0080#32, 0xad3f0080#32, 0xd65f03c0#32, 0xcb030082#32, 0xd1004063#32, 0xd1014042#32, 0xad010060#32, 0xad820060#32,
    0xf1010042#32, 0x54ffffa8#32, 0xad3e0080#32, 0xad3f0080#32, 0xd65f03c0#32]
  align := 4
  symbols := [("memset", 0)]
  relocs := []

def mallocng_blk22_lock : Obj.CodeBlock where
  code := mallocngWordsLE [
    0x90000003#32, 0x91000062#32, 0xaa0003e4#32, 0x320107e1#32, 0x39400c42#32, 0x13001c42#32, 0x34000402#32, 0x885ffc80#32, 0x350000e0#32, 0x8800fc81#32,
    0x35ffffa0#32, 0x36f80362#32, 0x91000063#32, 0x39000c7f#32, 0x14000018#32, 0xd5033bbf#32, 0x37f800a2#32, 0x52800143#32, 0x12b00006#32, 0x320107e5#32,
    0x1400000a#32, 0x91000063#32, 0x39000c7f#32, 0x17fffffa#32, 0x0b060002#32, 0x2a0003e1#32, 0x14000007#32, 0xd5033bbf#32, 0x71000463#32, 0x54000140#32,
    0x37ffff40#32, 0x0b050001#32, 0x2a0003e2#32, 0x885ffc80#32, 0x6b00005f#32, 0x54ffff01#32, 0x8800fc81#32, 0x35ffff80#32, 0xd65f03c0#32, 0x885ffc85#32,
    0x110004a5#32, 0x8800fc85#32, 0x35ffffa0#32, 0x12b00007#32, 0x52b00006#32, 0x14000011#32, 0xaa0403e0#32, 0x93407ca2#32, 0xd2800c48#32, 0xd2801001#32,
    0xd2800003#32, 0xd4000001#32, 0xb100981f#32, 0x54000060#32, 0x0b0700a5#32, 0x14000008#32, 0xaa0403e0#32, 0xd2800001#32, 0xd4000001#32, 0x17fffffb#32,
    0xd5033bbf#32, 0x2a0003e5#32, 0x37fffe05#32, 0x0b0600a1#32, 0x885ffc80#32, 0x6b0000bf#32, 0x54ffff41#32, 0x8800fc81#32, 0x35ffff80#32, 0x17ffffe1#32]
  align := 4
  symbols := [("__lock", 0)]
  relocs := [
    { off := 0, kind := .adrpHi21, sym := "__libc" },
    { off := 4, kind := .addLo12, sym := "__libc" },
    { off := 48, kind := .addLo12, sym := "__libc" },
    { off := 84, kind := .addLo12, sym := "__libc" }]

def mallocng_blk23_unlock : Obj.CodeBlock where
  code := mallocngWordsLE [
    0xaa0003e3#32, 0xb9400000#32, 0x37f80040#32, 0xd65f03c0#32, 0x12b00004#32, 0x885ffc61#32, 0x0b040020#32, 0x8802fc60#32, 0x35ffffa2#32, 0x320107e0#32,
    0x6b00003f#32, 0x54ffff00#32, 0xaa0303e0#32, 0xd2800c48#32, 0xd2801021#32, 0xd2800022#32, 0xd4000001#32, 0xb100981f#32, 0x54fffe21#32, 0xaa0303e0#32,
    0xaa0203e1#32, 0xd4000001#32, 0x17ffffed#32]
  align := 4
  symbols := [("__unlock", 0)]
  relocs := []

def mallocngMultiData : List Obj.SymDataInfo := [
  { sym := "__malloc_size_classes", align := 4, readOnly := true, zeroTail := 0, bytes := [
      0x01#8, 0x00#8, 0x02#8, 0x00#8, 0x03#8, 0x00#8, 0x04#8, 0x00#8, 0x05#8, 0x00#8, 0x06#8, 0x00#8, 0x07#8, 0x00#8, 0x08#8, 0x00#8,
      0x09#8, 0x00#8, 0x0a#8, 0x00#8, 0x0c#8, 0x00#8, 0x0f#8, 0x00#8, 0x12#8, 0x00#8, 0x14#8, 0x00#8, 0x19#8, 0x00#8, 0x1f#8, 0x00#8,
      0x24#8, 0x00#8, 0x2a#8, 0x00#8, 0x32#8, 0x00#8, 0x3f#8, 0x00#8, 0x48#8, 0x00#8, 0x54#8, 0x00#8, 0x66#8, 0x00#8, 0x7f#8, 0x00#8,
      0x92#8, 0x00#8, 0xaa#8, 0x00#8, 0xcc#8, 0x00#8, 0xff#8, 0x00#8, 0x24#8, 0x01#8, 0x54#8, 0x01#8, 0x99#8, 0x01#8, 0xff#8, 0x01#8,
      0x48#8, 0x02#8, 0xaa#8, 0x02#8, 0x32#8, 0x03#8, 0xff#8, 0x03#8, 0x91#8, 0x04#8, 0x54#8, 0x05#8, 0x65#8, 0x06#8, 0xff#8, 0x07#8,
      0x24#8, 0x09#8, 0xaa#8, 0x0a#8, 0xcc#8, 0x0c#8, 0xff#8, 0x0f#8, 0x48#8, 0x12#8, 0x54#8, 0x15#8, 0x98#8, 0x19#8, 0xff#8, 0x1f#8] },
  { sym := "debruijn32.4681", align := 1, readOnly := true, zeroTail := 0, bytes := [
      0x00#8, 0x01#8, 0x17#8, 0x02#8, 0x1d#8, 0x18#8, 0x13#8, 0x03#8, 0x1e#8, 0x1b#8, 0x19#8, 0x0b#8, 0x14#8, 0x08#8, 0x04#8, 0x0d#8,
      0x1f#8, 0x16#8, 0x1c#8, 0x12#8, 0x1a#8, 0x0a#8, 0x07#8, 0x0c#8, 0x15#8, 0x11#8, 0x09#8, 0x06#8, 0x10#8, 0x05#8, 0x0f#8, 0x0e#8] },
  { sym := "med_cnt_tab", align := 1, readOnly := true, zeroTail := 0, bytes := [
      0x1c#8, 0x18#8, 0x14#8, 0x20#8] },
  { sym := "small_cnt_tab", align := 1, readOnly := true, zeroTail := 0, bytes := [
      0x1e#8, 0x1e#8, 0x1e#8, 0x1f#8, 0x0f#8, 0x0f#8, 0x14#8, 0x0a#8, 0x0a#8, 0x1f#8, 0x0f#8, 0x07#8, 0x19#8, 0x0c#8, 0x06#8, 0x15#8,
      0x0a#8, 0x05#8, 0x12#8, 0x08#8, 0x04#8, 0x1f#8, 0x0f#8, 0x07#8, 0x1c#8, 0x0e#8, 0x06#8] },
  { sym := "debruijn32.5048", align := 1, readOnly := true, zeroTail := 0, bytes := [
      0x00#8, 0x01#8, 0x17#8, 0x02#8, 0x1d#8, 0x18#8, 0x13#8, 0x03#8, 0x1e#8, 0x1b#8, 0x19#8, 0x0b#8, 0x14#8, 0x08#8, 0x04#8, 0x0d#8,
      0x1f#8, 0x16#8, 0x1c#8, 0x12#8, 0x1a#8, 0x0a#8, 0x07#8, 0x0c#8, 0x15#8, 0x11#8, 0x09#8, 0x06#8, 0x10#8, 0x05#8, 0x0f#8, 0x0e#8] },
  { sym := "__malloc_lock", align := 4, readOnly := false, bytes := [], zeroTail := 4 },
  { sym := "__aligned_alloc_replaced", align := 4, readOnly := false, bytes := [], zeroTail := 4 },
  { sym := "__malloc_replaced", align := 4, readOnly := false, bytes := [], zeroTail := 4 },
  { sym := "__malloc_context", align := 8, readOnly := false, bytes := [], zeroTail := 928 }]

/-- Multi-block placed library (`mallocng_multi`) for musl 1.2.5 `mallocng` and its leaf helpers. -/
def mallocngLib : Obj.MultiPlacedLib where
  name := "mallocng_multi"
  blocks := [
    mallocng_blk00_errno_location, mallocng_blk01_syscall_ret, mallocng_blk02_calloc, mallocng_blk03_free,
    mallocng_blk04_default_malloc, mallocng_blk05_nontrivial_free, mallocng_blk06_libc_free, mallocng_blk07_malloc_alloc_meta,
    mallocng_blk08_alloc_slot, mallocng_blk09_libc_malloc_impl, mallocng_blk10_malloc_allzerop, mallocng_blk11_posix_memalign,
    mallocng_blk12_aligned_alloc, mallocng_blk13_realloc, mallocng_blk14_libc_realloc, mallocng_blk15_vm_wait,
    mallocng_blk16_mmap, mallocng_blk17_mprotect, mallocng_blk18_mremap, mallocng_blk19_munmap,
    mallocng_blk20_memcpy, mallocng_blk21_memset, mallocng_blk22_lock, mallocng_blk23_unlock]
  data := mallocngMultiData
  exports := ["malloc", "free", "calloc", "realloc", "aligned_alloc", "posix_memalign"]

end VerifiedLibraries
