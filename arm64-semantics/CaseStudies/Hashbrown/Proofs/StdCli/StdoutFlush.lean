/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.Layout
public import CaseStudies.Hashbrown.Proofs.StdCli.CoreFmtWrite
public import CaseStudies.Hashbrown.Proofs.StdCli.SyscallsAndStderr
public import ProofLib.StdStartup.CleanupAndExit
public import ProofLib.StdStartup.MemOps
public import ProofLib.StdStartup.OutlineAtomics
public import ProofLib.StdStartup.NonVmSteps
public import ProofLib.MallocngIface
public meta import ProofLib.LiteralFetchLint
public meta import ProofLib.SepLogic.Stack

/-!
# Buffered `STDOUT` and `__print` Proofs

Layout-generic machine-code bundle (`HbStdoutCode`), `WordTree` validator, and verification of
`BufWriter<StdoutRaw>::flush_buf` (empty and non-empty buffers) for the `hashbrown` CLI.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open CaseStudies.Hashbrown

/-! ## Symbolic Code Bundle and `WordTree` Validator -/

local macro "iAdrp " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr true $rd (adrpOff $pc $t))
local macro "iAdr " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr false $rd ($t - $pc))
local macro "iAddLo12 " rd:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.addSubImm .W64 .ADD $rd $rn (($t).truncate 12) false)
local macro "iLdr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.ldr .W64 .X64 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iLdrbLo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.ldr .W32 .B8 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.str .X64 $rt (.Offset $rn (pageLo12 $t)))
local macro "iBl " pc:term:arg t:term:arg : term => `(Instr.bl ($t - $pc))
local macro "iB " pc:term:arg t:term:arg : term => `(Instr.b ($t - $pc))

def hbStdoutOutlinedOnceCallChunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.outlinedOnceCallAddr
  [.words b [0x910043e2#32, 0x52800021#32, 0xa90027e8#32, 0xf9000bea#32],
   .instrs b 0x10 [iB (b + 0x10#64) C.std.onceCallAddr]]

def hbOutlinedFn72Chunks (C : HbCliLayout) : List CodeChunk :=
  let o := C.outlinedFn72Addr
  [.words o [0xd503201f#32],
   .instrs o 0x04 [iAdr .x4 (o + 0x04#64) C.onceLockPanicLocAddr],
   .words (o + 0x08#64) [0xd65f03c0#32]]

def hbStdoutInitChunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.stdoutInitAddr
  let g := C.std.stdoutGlobalAddr
  [.instrs0 b [iAdrp .x8 b (g + 0x38#64), iAddLo12 .x8 .x8 (g + 0x38#64)],
   .words (b + 0x08#64) [0x88dffd08#32, 0x35000048#32, 0xd65f03c0#32,
     0xd100c3ff#32, 0xa9027bfd#32, 0x910083fd#32, 0xd503201f#32],
   .instrs b 0x24 [iAdr .x8 (b + 0x24#64) g],
   .words (b + 0x28#64) [0xd10007a9#32, 0x910003ea#32, 0xd503201f#32],
   .instrs b 0x34 [iAdr .x3 (b + 0x34#64) C.stdoutInitVtableAddr,
     iBl (b + 0x38#64) C.outlinedFn72Addr],
   .words (b + 0x3c#64) [0x9100e100#32],
   .instrs b 0x40 [iBl (b + 0x40#64) C.outlinedOnceCallAddr],
   .words (b + 0x44#64) [0xa9427bfd#32, 0x9100c3ff#32, 0xd65f03c0#32]]

def hbStdoutInitClosureChunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.stdoutInitClosureAddr
  [.words b [0xa9be7bfd#32, 0xf9000bf3#32, 0x910003fd#32, 0xf9400008#32,
     0xf9400113#32, 0xf900011f#32, 0xb40001d3#32],
   .instrs b 0x1c [iBl (b + 0x1c#64) C.rustAllocShimAddr],
   .words (b + 0x20#64) [0x52808000#32, 0x52800021#32],
   .instrs b 0x28 [iBl (b + 0x28#64) C.rustAllocAddr],
   .words (b + 0x2c#64) [0xb4000180#32, 0x52808008#32, 0xa9007e7f#32,
     0xa901227f#32, 0xa9027e60#32, 0x3900c27f#32, 0xf9400bf3#32,
     0xa8c27bfd#32, 0xd65f03c0#32],
   .words C.rustAllocShimAddr [0xd65f03c0#32],
   .instrs0 C.rustAllocAddr [iB C.rustAllocAddr C.rdlAllocAddr],
   .words C.rdlAllocAddr [0xf100403f#32, 0xaa0003e2#32, 0x540000a8#32,
     0xeb02003f#32, 0x54000068#32, 0xaa0203e0#32],
   .instrs C.rdlAllocAddr 0x18 [iB (C.rdlAllocAddr + 0x18#64) C.mallocng.mallocAddr]]

def hbBufWriterFlushBufChunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.bufWriterFlushBufAddr
  [.words b [0xd101c3ff#32, 0xa9017bfd#32, 0xa9026ffc#32, 0xa90367fa#32,
     0xa9045ff8#32, 0xa90557f6#32, 0xa9064ff4#32, 0x910043fd#32,
     0xf9400818#32, 0xb4000618#32, 0xf9400417#32, 0xaa0003f3#32,
     0xaa1f03f4#32, 0x5280003b#32, 0xd503201f#32],
   .instrs b 0x3c [iAdr .x25 (b + 0x3c#64) C.defaultOsFunctionsAddr],
   .words (b + 0x40#64) [0x52800055#32, 0x14000003#32, 0xeb140316#32, 0x54000509#32,
     0x8b1402e1#32, 0xcb140302#32, 0x52800020#32, 0x3900627b#32,
     0xcb140316#32],
   .instrs b 0x64 [iBl (b + 0x64#64) C.writeAddr],
   .words (b + 0x68#64) [0xb100041f#32, 0x54000060#32, 0x3900627f#32, 0x14000016#32],
   .words (b + 0xcc#64) [0xb40001e0#32, 0x8b140014#32, 0x17ffffdd#32],
   .words (b + 0xe4#64) [0xaa1f03fc#32, 0x14000010#32, 0x54000303#32,
     0xf9400660#32, 0xaa1603e2#32, 0x8b140001#32],
   .instrs b 0xfc [iBl (b + 0xfc#64) C.memmoveAddr],
   .words (b + 0x100#64) [0xaa1f03fc#32, 0x14000008#32],
   .words (b + 0x124#64) [0xf9000a76#32, 0xaa1c03e0#32, 0xa9464ff4#32,
     0xa94557f6#32, 0xa9445ff8#32, 0xa94367fa#32, 0xa9426ffc#32,
     0xa9417bfd#32, 0x9101c3ff#32, 0xd65f03c0#32]]

def hbBufWriterWriteAllColdChunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.bufWriterWriteAllColdAddr
  [.words b [0xa9bd7bfd#32, 0xf9000bf5#32, 0xa9024ff4#32, 0x910003fd#32,
     0xf9400008#32, 0xf9400809#32, 0xaa0203f4#32, 0xaa0003f3#32,
     0xcb090109#32, 0xeb09005f#32, 0x54000169#32, 0xaa1303e0#32, 0xaa0103f5#32],
   .instrs b 0x34 [iBl (b + 0x34#64) C.bufWriterFlushBufAddr],
   .words (b + 0x38#64) [0xb40000a0#32, 0xa9424ff4#32, 0xf9400bf5#32, 0xa8c37bfd#32,
     0xd65f03c0#32, 0xf9400268#32, 0xaa1503e1#32, 0xeb08029f#32,
     0x54000182#32, 0xa940d668#32, 0xaa1403e2#32, 0x8b150100#32],
   .instrs b 0x68 [iBl (b + 0x68#64) C.std.memcpyAddr],
   .words (b + 0x6c#64) [0x8b1402a8#32, 0xaa1f03e0#32, 0xf9000a68#32,
     0xa9424ff4#32, 0xf9400bf5#32, 0xa8c37bfd#32, 0xd65f03c0#32]]

def hbStdoutRawWriteAllChunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.stdoutRawWriteAllAddr
  [.words b [0xd101c3ff#32, 0xa9017bfd#32, 0xa9026ffc#32, 0xa90367fa#32,
     0xa9045ff8#32, 0xa90557f6#32, 0xa9064ff4#32, 0x910043fd#32,
     0xb4000541#32],
   .instrs b 0x24 [iAdrp .x26 (b + 0x24#64) C.osFunctionsGotAddr],
   .words (b + 0x28#64) [0xaa0103f4#32, 0xaa0003f5#32],
   .instrs b 0x30 [iLdr64Lo12 .x26 .x26 C.osFunctionsGotAddr],
   .words (b + 0x34#64) [0x910003f8#32, 0xd503201f#32],
   .instrs b 0x3c [iAdr .x19 (b + 0x3c#64) C.writeZeroErrAddr],
   .words (b + 0x40#64) [0x52800039#32, 0xd503201f#32],
   .instrs b 0x48 [iAdr .x22 (b + 0x48#64) C.defaultOsFunctionsAddr],
   .words (b + 0x4c#64) [0x5280005b#32, 0x14000002#32,
     0xb40003b4#32, 0x52800020#32, 0xaa1503e1#32, 0xaa1403e2#32],
   .instrs b 0x64 [iBl (b + 0x64#64) C.writeAddr],
   .words (b + 0x68#64) [0xb100041f#32, 0x540000e0#32, 0xb40002e0#32,
     0xeb000288#32, 0x54000403#32, 0x8b0002b5#32, 0xaa0803f4#32, 0x17fffff4#32],
   .words (b + 0xc8#64) [0xaa1f03f3#32, 0xaa1303e0#32, 0xa9464ff4#32,
     0xa94557f6#32, 0xa9445ff8#32, 0xa94367fa#32, 0xa9426ffc#32,
     0xa9417bfd#32, 0x9101c3ff#32, 0xd65f03c0#32]]

def hbMemrchrWords : List (BitVec 32) :=
  [0xa9bf7bfd#32, 0x910003fd#32, 0x91001c29#32, 0x2a0003e8#32,
   0xaa0203e0#32, 0x927df129#32, 0xaa0203ea#32, 0xcb010129#32,
   0xeb09005f#32, 0x540000c3#32, 0x4b09004a#32, 0x92400d4a#32,
   0xeb0a0040#32, 0x54000723#32, 0xaa0903ea#32, 0x8b01004c#32,
   0xaa1f03eb#32, 0x12001d09#32, 0xcb000048#32, 0xd100058c#32,
   0xeb0b011f#32, 0x54000120#32, 0x385ff58d#32, 0x9100056b#32,
   0x6b0901bf#32, 0x54ffff61#32, 0xcb0b0041#32, 0x52800020#32,
   0xa8c17bfd#32, 0xd65f03c0#32, 0xb200c3e8#32, 0xb200c3ec#32,
   0xb201c3ed#32, 0x9b087d2b#32, 0xf280200c#32, 0xaa0003e8#32,
   0xeb0a001f#32, 0x540001a9#32, 0x8b08002e#32, 0xd1004100#32,
   0xa97f39cf#32, 0xca0b01ef#32, 0xca0b01ce#32, 0xcb0f0190#32,
   0xcb0e0191#32, 0xaa0f020f#32, 0xaa0e022e#32, 0x8a0e01ee#32,
   0xea2e01bf#32, 0x54fffe40#32, 0xeb02011f#32, 0x540001c8#32,
   0xd100042a#32, 0x52800020#32, 0xb4000108#32, 0x3868694b#32,
   0xd1000501#32, 0xaa0103e8#32, 0x6b09017f#32, 0x54ffff61#32,
   0xa8c17bfd#32, 0xd65f03c0#32, 0xaa1f03e0#32, 0xa8c17bfd#32,
   0xd65f03c0#32]

def hbMemrchrChunks (C : HbCliLayout) : List CodeChunk :=
  [.words C.memrchrAddr hbMemrchrWords]

def hbStdoutLockEntryWords : List (BitVec 32) :=
  [0xa9bc7bfd#32, 0xf9000bf7#32, 0xa90257f6#32, 0xa9034ff4#32,
   0x910003fd#32, 0xf9400016#32, 0xf9400ac8#32, 0xb5000a88#32,
   0xaa0203f3#32, 0xaa0103f4#32, 0x92800008#32, 0xf9000ac8#32,
   0x52800140#32]

def hbStdoutLockWriteAllChunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.stdoutLockWriteAllAddr
  [.words b hbStdoutLockEntryWords,
   .instrs b 0x34 [iBl (b + 0x34#64) C.memrchrAddr],
   .words (b + 0x38#64) [0xf100041f#32, 0x540002a1#32, 0x91000435#32,
     0xeb150273#32, 0x54000a23#32, 0xf94016d7#32, 0xb40004d7#32,
     0xf84182c8#32, 0xcb170108#32, 0xeb0802bf#32, 0x54000a42#32,
     0xf94012c8#32, 0xaa1403e1#32, 0xaa1503e2#32, 0x8b170100#32],
   .instrs b 0x74 [iBl (b + 0x74#64) C.std.memcpyAddr],
   .words (b + 0x78#64) [0x8b1502e8#32, 0xf90016c8#32, 0x910062c0#32],
   .instrs b 0x84 [iBl (b + 0x84#64) C.bufWriterFlushBufAddr],
   .words (b + 0x88#64) [0xb5000620#32, 0x14000022#32, 0xf94016d5#32,
     0xb4000155#32, 0xf94012c8#32, 0x8b150108#32, 0x385ff108#32,
     0x7100291f#32, 0x540000a1#32, 0x910062c0#32],
   .instrs b 0xb0 [iBl (b + 0xb0#64) C.bufWriterFlushBufAddr],
   .words (b + 0xb4#64) [0xb50004c0#32, 0xf94016d5#32, 0xf84182c8#32,
     0xcb150108#32, 0xeb08027f#32, 0x54000582#32, 0xf94012c8#32,
     0xaa1403e1#32, 0xaa1303e2#32, 0x8b150100#32],
   .instrs b 0xdc [iBl (b + 0xdc#64) C.std.memcpyAddr],
   .words (b + 0xe0#64) [0x8b1302a8#32, 0x14000018#32, 0xaa1403e0#32, 0xaa1503e1#32],
   .instrs b 0xf0 [iBl (b + 0xf0#64) C.stdoutRawWriteAllAddr],
   .words (b + 0xf4#64) [0xb4000100#32, 0x92400408#32, 0xf100091f#32,
     0x54000263#32, 0x54000241#32, 0xd360fc08#32, 0xf100251f#32,
     0x540001e1#32, 0xf9400ec8#32, 0xf94016d7#32, 0x8b150294#32,
     0xcb170108#32, 0xeb08027f#32, 0x54000282#32, 0xf94012c8#32,
     0xaa1403e1#32, 0xaa1303e2#32, 0x8b170100#32],
   .instrs b 0x13c [iBl (b + 0x13c#64) C.std.memcpyAddr],
   .words (b + 0x140#64) [0x8b1302e8#32, 0xaa1f03e0#32, 0xf90016c8#32,
     0xf9400ac8#32, 0x91000508#32, 0xf9000ac8#32, 0xa9434ff4#32,
     0xf9400bf7#32, 0xa94257f6#32, 0xa8c47bfd#32, 0xd65f03c0#32],
   .words (b + 0x178#64) [0x910062c0#32, 0xaa1403e1#32, 0xaa1303e2#32],
   .instrs b 0x184 [iBl (b + 0x184#64) C.bufWriterWriteAllColdAddr],
   .words (b + 0x188#64) [0x17fffff1#32],
   .words (b + 0x1a8#64) [0x910062c0#32, 0xaa1403e1#32, 0xaa1503e2#32],
   .instrs b 0x1b4 [iBl (b + 0x1b4#64) C.bufWriterWriteAllColdAddr],
   .words (b + 0x1b8#64) [0xb5fffca0#32, 0x17ffffb1#32]]

def hbAdapterWriteStrChunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.adapterWriteStrAddr
  [.words b [0xd100c3ff#32, 0xa9017bfd#32, 0xa9024ff4#32, 0x910043fd#32,
     0xaa0003f3#32, 0xf9400000#32],
   .instrs b 0x18 [iBl (b + 0x18#64) C.stdoutLockWriteAllAddr],
   .words (b + 0x1c#64) [0xaa0003f4#32, 0xb4000200#32],
   .words (b + 0x60#64) [0xf100029f#32, 0x1a9f07e0#32, 0xa9424ff4#32,
     0xa9417bfd#32, 0x9100c3ff#32, 0xd65f03c0#32]]

def hbPrintToBufferCaptureChunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.printToBufferCaptureAddr
  [.words b [0xd10183ff#32, 0xa9027bfd#32, 0xa9035ff8#32, 0xa90457f6#32,
     0xa9054ff4#32, 0x910083fd#32],
   .instrs b 0x18 [iAdrp .x8 (b + 0x18#64) C.captureUsedAddr,
     iLdrbLo12 .x8 .x8 C.captureUsedAddr],
   .words (b + 0x20#64) [0x34000a48#32],
   .words (b + 0x168#64) [0x2a1f03e0#32, 0xa9454ff4#32, 0xa94457f6#32,
     0xa9435ff8#32, 0xa9427bfd#32, 0x910183ff#32, 0xd65f03c0#32]]

def hbStdoutWriteFmtChunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.stdoutWriteFmtAddr
  [.words b [0xd10203ff#32, 0xa9037bfd#32, 0xa90467fa#32, 0xa9055ff8#32,
     0xa90657f6#32, 0xa9074ff4#32, 0x9100c3fd#32, 0xf9400008#32,
     0xaa0203f3#32, 0xaa0103f4#32, 0xf9400118#32, 0xd2a00000#32,
     0xf2800b00#32, 0xd503201f#32, 0xd503201f#32, 0xd53bd05a#32,
     0xf8606b59#32, 0xb4000159#32, 0xf9400308#32, 0xeb08033f#32,
     0x54000341#32],
   .instrs b 0x6c [iAdrp .x8 (b + 0x6c#64) C.std.threadIdCounterAddr],
   .words (b + 0x70#64) [0xaa0003f5#32],
   .instrs b 0x74 [iAdrp .x22 (b + 0x74#64) C.std.threadIdCounterAddr,
     iAddLo12 .x22 .x22 C.std.threadIdCounterAddr,
     iLdr64Lo12 .x23 .x8 C.std.threadIdCounterAddr],
   .words (b + 0x80#64) [0xb10006ff#32, 0x54000940#32, 0x910006e1#32,
     0xaa1703e0#32, 0xaa1603e2#32, 0x910006f9#32],
   .instrs b 0x98 [iBl (b + 0x98#64) C.std.cas8RelaxAddr],
   .words (b + 0x9c#64) [0xeb17001f#32, 0xaa0003f7#32, 0x54fffee1#32,
     0xf8356b59#32, 0xf9400308#32, 0xeb08033f#32, 0x54fffd00#32,
     0x91002302#32, 0x2a1f03e0#32, 0x52800021#32, 0x52800035#32],
   .instrs b 0xc8 [iBl (b + 0xc8#64) C.std.cas4AcqAddr],
   .words (b + 0xcc#64) [0x7100001f#32, 0x540007c1#32, 0xf9000319#32,
     0xb9000f15#32, 0x910023e8#32, 0xf9000fff#32, 0xa900a3f8#32,
     0xd503201f#32],
   .instrs b 0xec [iAdr .x1 (b + 0xec#64) C.adapterWriteVtableAddr],
   .words (b + 0xf0#64) [0x910043e0#32, 0xaa1403e2#32, 0xaa1303e3#32],
   .instrs b 0xfc [iBl (b + 0xfc#64) C.coreFmtWriteAddr],
   .words (b + 0x100#64) [0xf9400ff3#32, 0x34000120#32],
   .words (b + 0x128#64) [0xb40001d3#32],
   .words (b + 0x160#64) [0xf94007f4#32, 0xb9400e88#32, 0x71000508#32,
     0xb9000e88#32, 0x540000e1#32, 0x91002281#32, 0x2a1f03e0#32,
     0xf900029f#32],
   .instrs b 0x180 [iBl (b + 0x180#64) C.std.swp4RelAddr],
   .words (b + 0x184#64) [0x7100081f#32, 0x54000260#32, 0xaa1303e0#32,
     0xa9474ff4#32, 0xa94657f6#32, 0xa9455ff8#32, 0xa94467fa#32,
     0xa9437bfd#32, 0x910203ff#32, 0xd65f03c0#32]]

def hbStdioPrintChunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.stdioPrintAddr
  let g := C.std.stdoutGlobalAddr
  [.words b [0xd10183ff#32, 0xa9047bfd#32, 0xa9054ff4#32, 0x910103fd#32,
     0x528000c8#32, 0xd503201f#32],
   .instrs b 0x18 [iAdr .x9 (b + 0x18#64) C.stdoutLabelStrAddr],
   .words (b + 0x1c#64) [0xaa0103f3#32, 0xaa0003f4#32, 0xa90023e9#32],
   .instrs b 0x28 [iBl (b + 0x28#64) C.printToBufferCaptureAddr],
   .words (b + 0x2c#64) [0x370001e0#32],
   .instrs b 0x30 [iAdrp .x8 (b + 0x30#64) (g + 0x38#64),
     iAddLo12 .x8 .x8 (g + 0x38#64)],
   .words (b + 0x38#64) [0x88dffd08#32, 0x350001e8#32, 0xd503201f#32],
   .instrs b 0x44 [iAdr .x8 (b + 0x44#64) g],
   .words (b + 0x48#64) [0x910083e0#32, 0xf9000be8#32, 0x910043e8#32,
     0xaa1403e1#32, 0xaa1303e2#32, 0xf90013e8#32],
   .instrs b 0x60 [iBl (b + 0x60#64) C.stdoutWriteFmtAddr],
   .words (b + 0x64#64) [0xb50000e0#32, 0xa9454ff4#32, 0xa9447bfd#32,
     0x910183ff#32, 0xd65f03c0#32],
   .instrs b 0x78 [iBl (b + 0x78#64) C.stdoutInitAddr],
   .words (b + 0x7c#64) [0x17fffff1#32]]

def hbPrintBoolChunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.printBoolAddr
  [.words b [0x360000a0#32, 0xd503201f#32],
   .instrs b 0x08 [iAdr .x0 (b + 0x08#64) C.trueNlAddr],
   .words (b + 0x0c#64) [0x52800161#32],
   .instrs b 0x10 [iB (b + 0x10#64) C.stdioPrintAddr],
   .words (b + 0x14#64) [0xd503201f#32],
   .instrs b 0x18 [iAdr .x0 (b + 0x18#64) C.falseNlAddr],
   .words (b + 0x1c#64) [0x528001a1#32],
   .instrs b 0x20 [iB (b + 0x20#64) C.stdioPrintAddr]]

def hbPrintU64Chunks (C : HbCliLayout) : List CodeChunk :=
  let b := C.printU64Addr
  [.words b [0xd100c3ff#32, 0xa9027bfd#32, 0x910083fd#32, 0x910023e8#32, 0xd503201f#32],
   .instrs b 0x14 [iAdr .x9 (b + 0x14#64) C.u64DisplayFmtAddr],
   .words (b + 0x18#64) [0xa900a3e0#32, 0xd503201f#32],
   .instrs b 0x20 [iAdr .x0 (b + 0x20#64) C.nlByteAddr],
   .words (b + 0x24#64) [0x910043e1#32, 0xf9000fe9#32],
   .instrs b 0x2c [iBl (b + 0x2c#64) C.stdioPrintAddr],
   .words (b + 0x30#64) [0xa9427bfd#32, 0x9100c3ff#32, 0xd65f03c0#32]]

def hbStdoutChunks (C : HbCliLayout) : List CodeChunk :=
  hbStdoutOutlinedOnceCallChunks C ++
  (hbOutlinedFn72Chunks C ++
  (hbStdoutInitChunks C ++
  (hbStdoutInitClosureChunks C ++
  (hbBufWriterFlushBufChunks C ++
  (hbBufWriterWriteAllColdChunks C ++
  (hbStdoutRawWriteAllChunks C ++
  (hbMemrchrChunks C ++
  (hbStdoutLockWriteAllChunks C ++
  (hbAdapterWriteStrChunks C ++
  (hbPrintToBufferCaptureChunks C ++
  (hbStdoutWriteFmtChunks C ++
  (hbStdioPrintChunks C ++
  (hbPrintBoolChunks C ++
  hbPrintU64Chunks C)))))))))))))

def HbStdoutCode (P : Program) (C : HbCliLayout) : Prop :=
  CodeChunks P (hbStdoutChunks C)

def hbOnceCallPostChunks (C : HbCliLayout) : List CodeChunk :=
  let L := C.std; let oc := L.onceCallAddr
  [ .words oc [0xd10183ff#32, 0xa9027bfd#32, 0xa9035ff8#32, 0xa90457f6#32, 0xa9054ff4#32,
      0x910083fd#32, 0x910023e8#32, 0x88dffc16#32, 0xaa0303f5#32, 0xaa0203f4#32,
      0xaa0003f3#32, 0x91002118#32, 0x37000081#32, 0xaa0403f7#32, 0x14000049#32],
    .words (oc + 0x40#64) [0x120006d7#32, 0x51000ae8#32, 0x7100091f#32, 0x121e02c8#32,
      0x540001a2#32, 0x32000101#32, 0x2a1603e0#32, 0xaa1303e2#32],
    .instrs oc 0x60 [iBl (oc + 0x60#64) L.cas4AcqAddr],
    .words (oc + 0x64#64) [0x6b16001f#32, 0x540004a0#32],
    .words (oc + 0xfc#64) [0x71000aff#32, 0x1a9f17e8#32, 0xf94012a9#32, 0xb9000bff#32, 0x390033e8#32,
      0x910023e1#32, 0xaa1403e0#32, 0xd63f0120#32, 0xb9400be0#32, 0xaa1303e1#32],
    .instrs oc 0x124 [iBl (oc + 0x124#64) L.swp4RelAddr],
    .words (oc + 0x128#64) [0x361000c0#32],
    .words (oc + 0x140#64) [0xa9454ff4#32, 0xa94457f6#32, 0xa9435ff8#32, 0xa9427bfd#32, 0x910183ff#32, 0xd65f03c0#32],
    .words (oc + 0x15c#64) [0x120006c9#32, 0x121e02c8#32, 0x7100053f#32, 0x540003cc#32],
    .words (oc + 0x1e0#64) [0x71000d3f#32, 0x540001a1#32, 0x32000101#32, 0x2a1603e0#32, 0xaa1303e2#32],
    .instrs oc 0x1f4 [iBl (oc + 0x1f4#64) L.cas4AcqAddr],
    .words (oc + 0x1f8#64) [0x6b16001f#32, 0x540000a0#32],
    .words (oc + 0x210#64) [0x2a1f03e8#32, 0x17ffffbc#32] ]

abbrev HbOnceCallCode (P : Program) (C : HbCliLayout) : Prop :=
  CodeChunks P (hbOnceCallPostChunks C)

private theorem codeChunk_holds_withSvc {P : Program} (svc : State → State) :
    ∀ {c : CodeChunk}, c.holds P → c.holds (P.withSvc svc)
  | .words _ _, h => h
  | .instrs0 _ _, h => h
  | .instrs _ _ _, h => h

theorem codeChunks_withSvc {P : Program} (svc : State → State) :
    ∀ {cs : List CodeChunk}, CodeChunks P cs → CodeChunks (P.withSvc svc) cs
  | [], _ => trivial
  | [_], h => codeChunk_holds_withSvc svc h
  | _ :: _ :: _, ⟨h1, h2⟩ => ⟨codeChunk_holds_withSvc svc h1, codeChunks_withSvc svc h2⟩

theorem HbStdoutCode.withSvc {P : Program} {C : HbCliLayout} (svc : State → State)
    (hc : HbStdoutCode P C) : HbStdoutCode (P.withSvc svc) C :=
  codeChunks_withSvc svc hc

def checkHbStdoutCode (C : HbCliLayout) (base : BitVec 64) (t : WordTree) : Bool :=
  (hbStdoutChunks C).all (checkCodeChunk base t)

private theorem codeChunks_of_all {P : Program} {f : CodeChunk → Bool}
    (hf : ∀ {c : CodeChunk}, f c = true → c.holds P) :
    ∀ {cs : List CodeChunk}, cs.all f = true → CodeChunks P cs
  | [], _ => trivial
  | [_], h => hf (by simpa using h)
  | _ :: _ :: _, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact ⟨hf h.1, codeChunks_of_all hf (by simpa [List.all_cons] using h.2)⟩

theorem hbStdoutCode_of_wordTree {P : Program} {C : HbCliLayout} {t : WordTree}
    (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkHbStdoutCode C P.base t = true) :
    HbStdoutCode P C := by
  have hc : ∀ {c : CodeChunk}, checkCodeChunk P.base t c = true → c.holds P := by
    rintro (⟨a, ws⟩ | ⟨b, is⟩ | ⟨b, o, is⟩) h
    · simp only [checkCodeChunk, checkCleanupWordsAt, Bool.and_eq_true, decide_eq_true_eq] at h
      exact hasWords_of_wordTree n hcode hwf rfl h.1 hstubs hsyms h.2
    all_goals
      simp only [checkCodeChunk, checkCleanupInstrsAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact hasInstrs_of_wordTree n hcode hwf h.1.1 h.1.2 hext hovr h.2
  exact codeChunks_of_all hc hok

private theorem codeChunks_append {P : Program} :
    ∀ {xs ys : List CodeChunk}, CodeChunks P (xs ++ ys) → CodeChunks P xs ∧ CodeChunks P ys
  | [], _, h => ⟨trivial, h⟩
  | [_], [], h => ⟨h, trivial⟩
  | [_], _ :: _, ⟨h1, h2⟩ => ⟨h1, h2⟩
  | _ :: x2 :: xs, ys, ⟨h1, h2⟩ =>
    let ⟨ha, hb⟩ := codeChunks_append (xs := x2 :: xs) (ys := ys) h2
    ⟨⟨h1, ha⟩, hb⟩

theorem HbStdoutCode.outlinedOnceCall {P : Program} {C : HbCliLayout} (h : HbStdoutCode P C) :
    CodeChunks P (hbStdoutOutlinedOnceCallChunks C) := (codeChunks_append h).1

theorem HbStdoutCode.outlinedFn72 {P : Program} {C : HbCliLayout} (h : HbStdoutCode P C) :
    CodeChunks P (hbOutlinedFn72Chunks C) := (codeChunks_append (codeChunks_append h).2).1

theorem HbStdoutCode.stdoutInit {P : Program} {C : HbCliLayout} (h : HbStdoutCode P C) :
    CodeChunks P (hbStdoutInitChunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append h).2).2).1

theorem HbStdoutCode.stdoutInitClosure {P : Program} {C : HbCliLayout} (h : HbStdoutCode P C) :
    CodeChunks P (hbStdoutInitClosureChunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append h).2).2).2).1

theorem HbStdoutCode.bufWriterFlushBuf {P : Program} {C : HbCliLayout} (h : HbStdoutCode P C) :
    CodeChunks P (hbBufWriterFlushBufChunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
    (codeChunks_append h).2).2).2).2).1

theorem HbStdoutCode.bufWriterWriteAllCold {P : Program} {C : HbCliLayout} (h : HbStdoutCode P C) :
    CodeChunks P (hbBufWriterWriteAllColdChunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
    (codeChunks_append (codeChunks_append h).2).2).2).2).2).1

theorem HbStdoutCode.stdoutRawWriteAll {P : Program} {C : HbCliLayout} (h : HbStdoutCode P C) :
    CodeChunks P (hbStdoutRawWriteAllChunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
    (codeChunks_append (codeChunks_append (codeChunks_append h).2).2).2).2).2).2).1

theorem HbStdoutCode.memrchr {P : Program} {C : HbCliLayout} (h : HbStdoutCode P C) :
    CodeChunks P (hbMemrchrChunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
    (codeChunks_append (codeChunks_append (codeChunks_append
      (codeChunks_append h).2).2).2).2).2).2).2).1

theorem HbStdoutCode.stdoutLockWriteAll {P : Program} {C : HbCliLayout} (h : HbStdoutCode P C) :
    CodeChunks P (hbStdoutLockWriteAllChunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
    (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
      (codeChunks_append h).2).2).2).2).2).2).2).2).1

theorem HbStdoutCode.adapterWriteStr {P : Program} {C : HbCliLayout} (h : HbStdoutCode P C) :
    CodeChunks P (hbAdapterWriteStrChunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
    (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
      (codeChunks_append (codeChunks_append h).2).2).2).2).2).2).2).2).2).1

theorem HbStdoutCode.printToBufferCapture {P : Program} {C : HbCliLayout} (h : HbStdoutCode P C) :
    CodeChunks P (hbPrintToBufferCaptureChunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
    (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
      (codeChunks_append (codeChunks_append (codeChunks_append h).2).2).2).2).2).2).2).2).2).2).1

theorem HbStdoutCode.stdoutWriteFmt {P : Program} {C : HbCliLayout} (h : HbStdoutCode P C) :
    CodeChunks P (hbStdoutWriteFmtChunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
    (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
      (codeChunks_append (codeChunks_append (codeChunks_append
        (codeChunks_append h).2).2).2).2).2).2).2).2).2).2).2).1

theorem HbStdoutCode.stdioPrint {P : Program} {C : HbCliLayout} (h : HbStdoutCode P C) :
    CodeChunks P (hbStdioPrintChunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
    (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
      (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
        (codeChunks_append h).2).2).2).2).2).2).2).2).2).2).2).2).1

theorem HbStdoutCode.printBool {P : Program} {C : HbCliLayout} (h : HbStdoutCode P C) :
    CodeChunks P (hbPrintBoolChunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
    (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
      (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
        (codeChunks_append (codeChunks_append h).2).2).2).2).2).2).2).2).2).2).2).2).2).1

theorem HbStdoutCode.printU64 {P : Program} {C : HbCliLayout} (h : HbStdoutCode P C) :
    CodeChunks P (hbPrintU64Chunks C) :=
  (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
    (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
      (codeChunks_append (codeChunks_append (codeChunks_append (codeChunks_append
        (codeChunks_append (codeChunks_append h).2).2).2).2).2).2).2).2).2).2).2).2).2).2

/-! ## `BufWriter<StdoutRaw>::flush_buf` -/

def fetchAtAcc' (P : Program) (base : BitVec 64) : Nat → List Instr → Prop → Prop
  | _, [], acc => acc
  | off, x :: xs, acc =>
    P.fetch (base + BitVec.ofNat 64 off) = some x ∧ fetchAtAcc' P base (off + 4) xs acc

theorem fetchAtAcc'_of_fn {P : Program} {base : BitVec 64} {acc : Prop} (hacc : acc) :
    ∀ (off : Nat) (is : List Instr),
      (∀ i (hi : i < is.length), P.fetch (base + BitVec.ofNat 64 (off + 4 * i)) = some (is[i]'hi)) →
      fetchAtAcc' P base off is acc
  | _, [], _ => hacc
  | off, _ :: xs, h =>
    ⟨by simpa using h 0 (Nat.zero_lt_succ _),
     fetchAtAcc'_of_fn hacc (off + 4) xs fun i hi => by
       simpa [show off + 4 + 4 * i = off + 4 * (i + 1) by omega] using h (i + 1) (Nat.succ_lt_succ hi)⟩

def stdoutStepAcc (P : Program) (acc : Prop) : CodeChunk → Prop
  | .words a ws => P.hasCode a ws ∧ acc
  | .instrs0 b is => fetchAtAcc' P b 0 is acc
  | .instrs b o is => fetchAtAcc' P b o is acc

def stdoutStepFacts (P : Program) : List CodeChunk → Prop
  | [] => True
  | c :: cs => stdoutStepAcc P (stdoutStepFacts P cs) c

theorem stdoutToStepAcc {P : Program} {acc : Prop} (hacc : acc) :
    ∀ {c : CodeChunk}, c.holds P → stdoutStepAcc P acc c
  | .words _ _, h => ⟨h, hacc⟩
  | .instrs0 _ _, h => fetchAtAcc'_of_fn hacc 0 _ fun i hi => by simpa using h i hi
  | .instrs _ o _, h => fetchAtAcc'_of_fn hacc o _ fun i hi => by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]; exact h i hi

theorem stdoutToStepFacts {P : Program} :
    ∀ {cs : List CodeChunk}, CodeChunks P cs → stdoutStepFacts P cs
  | [], _ => trivial
  | [_], h => stdoutToStepAcc trivial h
  | _ :: _ :: _, ⟨h1, h2⟩ => stdoutToStepAcc (stdoutToStepFacts h2) h1

local macro "unpack_stdout_code " chunks:ident h:term : tactic => `(tactic| (
  have _hc := stdoutToStepFacts $h
  simp only [$chunks:ident, stdoutStepFacts, stdoutStepAcc, fetchAtAcc',
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

theorem bv64_add_sub_cancel' (a b : BitVec 64) : a + (b - a) = b := by bv_lin
local macro "norm_jmp" : tactic =>
  `(tactic| conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel'])

local macro "unpack_cells " k:num : tactic => `(tactic| (
  try simp only [Nat.reduceMul]
  cells_unfold
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate $k (apply SepWP.exists_left; intro _)))

local macro "repack_cells" : tactic => `(tactic| (
  try simp only [Nat.reduceMul]
  cells_unfold
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  sep_entail))

attribute [local simp] cpuAux_writeReg64 cpuAux_writeReg32 cpuAux_writeReg
  cpuAux_setPState cpuAux_advancePC cpuAux_setPC cpuAux_setMem

local macro "unpack_cs " h:ident : tactic =>
  `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := $h)
local macro "close_cs" : tactic =>
  `(tactic| simp [CalleeSavedPreserved.iff_regs, Reg.fp, wp_norm, arm64_norm, *])
local macro "wp_a" : term => `(by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)

def hbBufWriterFlushZeroSpec (_C : HbCliLayout) : Spec (BitVec 64) where
  pre := fun bwPtr s0 =>
    ⌜s0.readReg64 .x0 = bwPtr⌝ ∗ ((bwPtr + 0x10#64) ↦₆₄ 0#64) ∗ stackAt s0.sp 112
  post := fun bwPtr s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧ ProcessFieldsPreserved s0 sf⌝ ∗
      ((bwPtr + 0x10#64) ↦₆₄ 0#64) ∗ stackAt s0.sp 112

theorem hbBufWriterFlushZero_ok {P : Program} {C : HbCliLayout}
    (hc : HbStdoutCode P C)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.bufWriterFlushBufAddr (hbBufWriterFlushZeroSpec C) := by
  apply subroutine_ok_of_sepWP_init
  intro bwPtr R s0 hpc hrun hpre hsp
  dsimp only [hbBufWriterFlushZeroSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hmem⟩
  refine ⟨((bwPtr + 0x10#64) ↦₆₄ 0#64) ∗ stackAt s0.sp 112, hmem, ?_⟩
  refine SepWP.seq_noSyscalls (mid_pc := s0.readReg64 .lr)
    (Q := fun sf Pf =>
      (∀ R', sf.mem ⊨ Pf ∗ R' → sf.mem ⊨ (((bwPtr + 0x10#64) ↦₆₄ 0#64) ∗ stackAt s0.sp 112) ∗ R') ∧
      sf.readReg64 .x0 = 0#64 ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    hext ?_ (fun sf Pf hpcf hrunf hpure ⟨hPf, hx0f, hspf, hcsf⟩ => ?_)
  · have hcNo := (hc.withSvc noSyscalls).bufWriterFlushBuf
    unpack_stdout_code hbBufWriterFlushBufChunks hcNo
    conv => arg 4; rw [stackAt_eq_cells s0.sp 14]
    unpack_cells 14
    have haux0 : CpuAuxPreserved s0 s0 := ⟨rfl, rfl, rfl, rfl⟩
    wp_steps; wp_steps; wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp [haux0], ?_, by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm],
      by simp [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm]⟩
    intro R' hm'
    rw [stackAt_eq_cells s0.sp 14]
    exact (by repack_cells : _ → _) hm'
  · refine SepWP.done hpcf hrunf ⟨fun hm_f => ?_, hspf, hcsf⟩
    have hm_f' := hPf R hm_f
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0f, hpure.1⟩, hm_f'⟩

/-! ### `hbStdioSvc` Lifting -/

/-- Supervisor-call dispatcher restricted to `Syscall.stdioTable`. -/
def hbStdioSvc : State → State := Syscall.dispatch Syscall.stdioTable

@[simp 2100, arm64_norm 2100, wp_norm]
theorem Program.withSvc_hbStdioSvc_svc (prog : Program) :
    (prog.withSvc hbStdioSvc).svc = hbStdioSvc := Program.withSvc_svc prog hbStdioSvc

@[simp 2100, arm64_norm 2100, wp_norm]
theorem Program.withSvc_hbStdioSvc_fetch (prog : Program) (pc : BitVec 64) :
    (prog.withSvc hbStdioSvc).fetch pc = prog.fetch pc := Program.withSvc_fetch prog hbStdioSvc pc

@[simp 2100, arm64_norm 2100, wp_norm]
theorem Program.withSvc_hbStdioSvc_externAt? (prog : Program) (pc : BitVec 64) :
    (prog.withSvc hbStdioSvc).externAt? pc = prog.externAt? pc :=
  Program.withSvc_externAt? prog hbStdioSvc pc

@[simp 2100, arm64_norm 2100, wp_norm]
theorem Program.withSvc_hbStdioSvc_codeLoaded (prog : Program) (m : Memory) :
    (prog.withSvc hbStdioSvc).CodeLoaded m ↔ prog.CodeLoaded m :=
  Program.withSvc_codeLoaded prog hbStdioSvc m

private theorem nonVmTable_find_of_stdio_some {nr : BitVec 64} {p : BitVec 64 × (State → State)}
    (h : Syscall.stdioTable.find? (·.1 == nr) = some p) :
    nonVmSyscallTable.find? (·.1 == nr) = some p := by
  have heq : nonVmSyscallTable = Syscall.stdioTable ++
      (Syscall.fileIoOnlyTable ++ Syscall.pollTable ++ Syscall.signalsTable ++
       Syscall.timeTable ++ Syscall.randomTable ++ Syscall.miscTable) := by
    simp only [nonVmSyscallTable, List.append_assoc]
  rw [heq, List.find?_append, h]; rfl

theorem svcKeepsFrozen_hbStdioSvc : SvcKeepsFrozen hbStdioSvc := by
  intro s
  cases hfind : Syscall.stdioTable.find? (·.1 == s.readReg64 Reg.x8) with
  | none =>
    have hs : hbStdioSvc s = s.setStatus (.Exception "unmodeled syscall (svc)") := by
      dsimp [hbStdioSvc, Syscall.dispatch]; rw [hfind]
    rw [hs]; cases s; exact ⟨fun _ _ => rfl, rfl, rfl⟩
  | some p =>
    have hnv := nonVmTable_find_of_stdio_some hfind
    have hs : hbStdioSvc s = nonVmSvc s := by
      dsimp [hbStdioSvc, nonVmSvc, Syscall.dispatch]; rw [hfind, hnv]
    rw [hs]; exact svcKeepsFrozen_nonVmSvc s

@[simp, arm64_norm, wp_norm]
theorem evalSvc_hbStdioSvc (s : State) : evalSvc hbStdioSvc s = hbStdioSvc s :=
  evalSvc_eq_of_svcKeepsFrozen svcKeepsFrozen_hbStdioSvc s

@[simp, arm64_norm, wp_norm]
theorem hbStdioSvc_write (s : State) (h : s.readReg64 .x8 = 64#64) :
    hbStdioSvc s = execWrite s := by
  dsimp [hbStdioSvc, Syscall.dispatch, Syscall.stdioTable]; rw [h]; rfl

private def projOrSig (s : State) := (s.oracle, s.oracleIdx, s.sigActions)
private theorem projOrSig_adv (s : State) : projOrSig s.advancePC = projOrSig s := by cases s; rfl
private theorem projOrSig_pc (s : State) (p : BitVec 64) : projOrSig (s.setPC p) = projOrSig s := by cases s; rfl
private theorem projOrSig_w64 (s : State) (r : Reg) (v : BitVec 64) : projOrSig (s.writeReg64 r v) = projOrSig s := by
  cases s; cases r <;> rfl
private theorem projOrSig_w32 (s : State) (r : Reg) (v : BitVec 32) : projOrSig (s.writeReg32 r v) = projOrSig s :=
  projOrSig_w64 s r _
private theorem projOrSig_w (s : State) (w : Width) (r : Reg) (v : BitVec 64) : projOrSig (s.writeReg w r v) = projOrSig s :=
  projOrSig_w64 s r _
private theorem projOrSig_v128 (s : State) (r : BitVec 5) (v : BitVec 128) : projOrSig (s.writeVReg128 r v) = projOrSig s := by
  cases s; rfl
private theorem projOrSig_v64 (s : State) (r : BitVec 5) (v : BitVec 64) : projOrSig (s.writeVReg64 r v) = projOrSig s :=
  projOrSig_v128 s r _
private theorem projOrSig_v32 (s : State) (r : BitVec 5) (v : BitVec 32) : projOrSig (s.writeVReg32 r v) = projOrSig s :=
  projOrSig_v128 s r _
private theorem projOrSig_ps (s : State) (p : PState) : projOrSig (s.setPState p) = projOrSig s := by cases s; rfl
private theorem projOrSig_fp (s : State) (f : BitVec 32) : projOrSig (s.setFpsr f) = projOrSig s := by cases s; rfl
private theorem projOrSig_ofp (s : State) (f : BitVec 32) : projOrSig (s.orFpsr f) = projOrSig s := by cases s; rfl
private theorem projOrSig_st (s : State) (st : ExecStatus) : projOrSig (s.setStatus st) = projOrSig s := by cases s; rfl
private theorem projOrSig_wst (s : State) (st : ExecStatus) : projOrSig { s with status := st } = projOrSig s := by cases s; rfl
private theorem projOrSig_mem (s : State) (m : Memory) : projOrSig (s.setMem m) = projOrSig s := by cases s; rfl
private theorem projOrSig_fs (s : State) (fs : FsState) : projOrSig (s.setFs fs) = projOrSig s := by cases s; rfl
private theorem projOrSig_tr (s : State) (evs : List TraceEvent) : projOrSig (s.appendTrace evs) = projOrSig s := by cases s; rfl
private theorem projOrSig_tp (s : State) (v : BitVec 64) : projOrSig (setTpidrEl0 s v) = projOrSig s := by cases s; rfl
private theorem projOrSig_ex (s : State) : projOrSig s.stepExclOracle = projOrSig s := by cases s; rfl
private theorem projOrSig_as (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    projOrSig (applySimdResult s rd r) = projOrSig s := by cases s; cases r <;> rfl
private theorem projOrSig_ass (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) (sat : Option (BitVec 32)) :
    projOrSig (applySimdSatResult s rd r sat) = projOrSig s := by cases s; cases r <;> cases sat <;> rfl
private theorem projOrSig_slr (sz : SimdMemSize) (m : Memory) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State), projOrSig (simdLoadRegs sz m n vt ea s) = projOrSig s
  | 0, _, _, _ => rfl
  | n + 1, _, _, s => (projOrSig_slr sz m n _ _ _).trans (projOrSig_v128 s _ _)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem execInst_projOrSig_of_not_isSvc0 {inst : Instr} (h : inst.isSvc0 = false) (s : State) :
    projOrSig (execInst inst s) = projOrSig s := by
  cases inst
  case system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm; subst heq; simp [Instr.isSvc0] at h
      · dsimp only [execInst, execInstWithSvc]; simp [himm, projOrSig_st]
    · dsimp only [execInst, execInstWithSvc]; by_cases himm : imm == 1#16 <;> simp [himm, projOrSig_st]
  case simdThreeSame q u size rm opcode rn rd =>
    dsimp only [execInst, execInstWithSvc]
    by_cases hop : opcode == 0b00011#5
    · simp only [hop, ↓reduceIte]
      rcases size with ⟨_ | _ | _ | _ | _, _⟩ <;> try omega
      all_goals (cases u <;> first | exact (projOrSig_adv _).trans (projOrSig_v128 _ _ _) | exact projOrSig_ass _ _ _ _)
    · simp only [hop, Bool.false_eq_true, ↓reduceIte, projOrSig_adv, projOrSig_v128, projOrSig_st, projOrSig_wst,
        projOrSig_as, projOrSig_ass, apply_ite projOrSig, ite_self]
  case ldpSimd _ _ _ addr | stpSimd _ _ _ addr | ldrSimd _ _ addr | strSimd _ _ addr =>
    dsimp only [execInst, execInstWithSvc]
    rcases evalAddrMode s addr with ⟨_, _ | ⟨_, _⟩⟩ <;>
      simp [projOrSig_adv, projOrSig_mem, projOrSig_v128, projOrSig_w64, projOrSig_st, apply_ite projOrSig]
  case ldr | ldrLit | str | ldp | stp | ldnp | stnp | addSubImm | logicalImm | moveWide | bitfield
     | logicalShift | addSubShift | addSubExt | addSubCarry | condCompareReg | condCompareImm
     | condSelect | dataProc1 | dataProc2 | dataProc3 =>
    cases s; dsimp only [execInst, execInstWithSvc, execLdr, execLdrLit, execStr, execLdp, execStp,
      execAddSubImm, execLogicalImm, execMoveWide, execBitfield, execLogicalShift, execAddSubShift,
      execAddSubExt, execAddSubCarry, execCondCompare, execCondSelect, execDataProc1, execDataProc2,
      execDataProc3]; (repeat' split) <;> rfl
  all_goals
    dsimp only [execInst, execInstWithSvc]
    simp only [projOrSig_adv, projOrSig_pc, projOrSig_w64, projOrSig_w32, projOrSig_w, projOrSig_v128, projOrSig_v64,
      projOrSig_v32, projOrSig_ps, projOrSig_fp, projOrSig_ofp, projOrSig_st, projOrSig_wst, projOrSig_mem, projOrSig_tp,
      projOrSig_ex, projOrSig_as, projOrSig_ass, projOrSig_slr, apply_ite projOrSig, ite_self]
    try (cases s; (repeat' split) <;> rfl)

private theorem projOrSig_read (s : State) : projOrSig (execRead s) = projOrSig s := by
  dsimp (config := { zetaHave := true }) only [execRead, execReadCommon]
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0)) <;>
    simp only [apply_ite projOrSig, projOrSig_adv, projOrSig_w64, projOrSig_st, projOrSig_fs, projOrSig_mem, ite_self]

private theorem projOrSig_write (s : State) : projOrSig (execWrite s) = projOrSig s := by
  dsimp (config := { zetaHave := true }) only [execWrite]
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0)) with
  | none => simp only [apply_ite projOrSig, projOrSig_adv, projOrSig_w64, projOrSig_st, projOrSig_tr, ite_self]
  | some desc =>
    cases desc.kind <;>
      simp only [apply_ite projOrSig, projOrSig_adv, projOrSig_w64, projOrSig_st, projOrSig_tr, projOrSig_fs, ite_self]

private theorem projOrSig_rwvFrame : ProofLib.RwvFrame (fun a b => projOrSig b = projOrSig a) :=
  ProofLib.RwvFrame.eqOn projOrSig projOrSig_w64 projOrSig_adv projOrSig_st (fun s _ _ => by cases s; rfl)

private theorem stdioHandler_projOrSig {nr : BitVec 64} {fn : State → State}
    (hmem : (nr, fn) ∈ Syscall.stdioTable) (s : State) :
    projOrSig (fn s) = projOrSig s := by
  simp only [Syscall.stdioTable, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact projOrSig_read s
  · exact projOrSig_write s
  · exact ProofLib.execReadv_preserves projOrSig_rwvFrame projOrSig_read s
  · exact ProofLib.execWritev_preserves projOrSig_rwvFrame projOrSig_write s
  · cases s; rfl
  · cases s; rfl

structure StdioSvcPreserved (s0 sf : State) : Prop where
  vm           : VmFieldsPreserved s0 sf
  keepsFrozen  : s0.mem.KeepsFrozen sf.mem
  oracle_eq    : sf.oracle = s0.oracle
  oracleIdx_eq : sf.oracleIdx = s0.oracleIdx
  sig_eq       : sf.sigActions = s0.sigActions
  symtab_eq    : sf.symtab = s0.symtab

theorem StdioSvcPreserved.toHbNonVm {s0 sf : State} (h : StdioSvcPreserved s0 sf)
    (htid : sf.tpidrEl0 = s0.tpidrEl0) : HbNonVmPreserved s0 sf :=
  ⟨htid, h.sig_eq, h.vm, h.keepsFrozen⟩

theorem StdioSvcPreserved.toFmtIo {s0 sf : State} (h : StdioSvcPreserved s0 sf)
    (hfs : sf.fs = s0.fs) (htid : sf.tpidrEl0 = s0.tpidrEl0) : FmtIoStatePreserved s0 sf :=
  ⟨hfs, htid, h.sig_eq, h.vm.brk_eq, h.vm.brkStart_eq, h.vm.physMemAvail_eq,
   h.vm.perm_eq, h.oracle_eq, h.oracleIdx_eq, h.symtab_eq⟩

private theorem steps_stdioSvc_to_nonVm {prog : Program} {s sf : State}
    (hext : ∀ pc, prog.externAt? pc = none)
    (hsteps : Steps (prog.withSvc hbStdioSvc) s sf)
    (hrun_f : sf.status = .Running) :
    Steps (prog.withSvc nonVmSvc) s sf ∧ projOrSig sf = projOrSig s := by
  induction hsteps with
  | refl => exact ⟨.refl _, rfl⟩
  | @step s1 s2 s3 h1 hrest ih =>
    have hr2 : s2.status = .Running := by
      cases hrest with
      | refl => exact hrun_f
      | step hs2 _ => exact hs2.running_of_step
    rcases ih hrun_f with ⟨hsteps_rest, hor_rest⟩
    have hf_eq : (prog.withSvc hbStdioSvc).fetchMem s1.mem s1.pc =
        (prog.withSvc nonVmSvc).fetchMem s1.mem s1.pc := rfl
    cases h1 with
    | @exec inst hr1 hfe =>
      by_cases hsvc0 : inst.isSvc0 = true
      · have hinst : inst = .system false 0#16 := by
          cases inst <;> simp [Instr.isSvc0] at hsvc0
          rcases hsvc0 with ⟨rfl, rfl⟩; rfl
        subst hinst
        have hr_svc : (hbStdioSvc s1).status = .Running := by
          simpa [Program.evalInst, Program.withSvc, execInstWithSvc] using hr2
        dsimp [hbStdioSvc, Syscall.dispatch] at hr_svc
        cases hfind : Syscall.stdioTable.find? (·.1 == s1.readReg64 Reg.x8) with
        | none => rw [hfind] at hr_svc; cases s1; cases hr_svc
        | some p =>
          rcases p with ⟨nr, fn⟩
          have hnv := nonVmTable_find_of_stdio_some hfind
          have hmem := List.mem_of_find?_eq_some hfind
          have hs_eq : hbStdioSvc s1 = nonVmSvc s1 := by
            dsimp [hbStdioSvc, nonVmSvc, Syscall.dispatch]; rw [hfind, hnv]
          have hs_fn : hbStdioSvc s1 = fn s1 := by dsimp [hbStdioSvc, Syscall.dispatch]; rw [hfind]
          have hev_eq : (prog.withSvc hbStdioSvc).evalInst (.system false 0#16) s1 =
              (prog.withSvc nonVmSvc).evalInst (.system false 0#16) s1 := by
            simp only [Program.evalInst, Program.withSvc, execInstWithSvc,
              evalSvc_hbStdioSvc, evalSvc_nonVmSvc, hs_eq]
          have hor1 : projOrSig ((prog.withSvc hbStdioSvc).evalInst (.system false 0#16) s1) = projOrSig s1 := by
            simp only [Program.evalInst, Program.withSvc, execInstWithSvc, evalSvc_hbStdioSvc, hs_fn]
            exact stdioHandler_projOrSig hmem s1
          rw [hev_eq] at hsteps_rest hor_rest hor1
          exact ⟨.step (Step.exec hr1 (hf_eq ▸ hfe)) hsteps_rest, hor_rest.trans hor1⟩
      · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
        have hev1 := evalInst_eq_execInst_of_not_isSvc0 (prog.withSvc hbStdioSvc) hnsvc0 s1
        have hev2 := evalInst_eq_execInst_of_not_isSvc0 (prog.withSvc nonVmSvc) hnsvc0 s1
        rw [hev1] at hsteps_rest hor_rest
        have hstepNV : Step (prog.withSvc nonVmSvc) s1 (execInst inst s1) :=
          hev2 ▸ Step.exec hr1 (hf_eq ▸ hfe)
        exact ⟨.step hstepNV hsteps_rest,
          hor_rest.trans (execInst_projOrSig_of_not_isSvc0 hnsvc0 s1)⟩
    | halt_unmapped _ _ _ => cases s1; cases hr2
    | extern _ he _ _ => rw [Program.withSvc_externAt?, hext] at he; cases he
    | extern_fault _ he _ => rw [Program.withSvc_externAt?, hext] at he; cases he

theorem Steps.of_stdioSvc_running {prog : Program} {s sf : State}
    (hext : ∀ pc, prog.externAt? pc = none)
    (hsvc : prog.svc = Syscall.standard)
    (hsteps : Steps (prog.withSvc hbStdioSvc) s sf)
    (hrun_f : sf.status = .Running) :
    Steps prog s sf ∧ StdioSvcPreserved s sf := by
  obtain ⟨hsteps_nv, hor⟩ := steps_stdioSvc_to_nonVm hext hsteps hrun_f
  obtain ⟨hstepsP, hvm⟩ := Steps.of_nonVm_running hext hsvc hsteps_nv hrun_f
  unfold projOrSig at hor
  simp only [Prod.mk.injEq] at hor
  exact ⟨hstepsP, ⟨hvm, hstepsP.keepsFrozen, hor.1, hor.2.1, hor.2.2, hstepsP.symtab_eq⟩⟩

theorem SepWP.of_stdioSvc {prog : Program} {target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hext : ∀ pc, prog.externAt? pc = none)
    (hsvc : prog.svc = Syscall.standard)
    (h : SepWP (prog.withSvc hbStdioSvc) target s P
      (fun sf Pf => StdioSvcPreserved s sf → post sf Pf)) :
    SepWP prog target s P post oom := by
  unfold SepWP at *
  intro R hm hL
  have hL' : (prog.withSvc hbStdioSvc).CodeLoaded s.mem := (Program.withSvc_codeLoaded ..).mpr hL
  rcases h R hm hL' with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hp⟩ | ⟨_, hoom⟩⟩
  · rcases Steps.of_stdioSvc_running hext hsvc hsteps hrun with ⟨hstepsP, hpr⟩
    exact ⟨sf, hstepsP, Or.inl ⟨hpc, hrun, Pf, hmf, hp hpr⟩⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩; exact False.elim hf

theorem subroutine_ok_of_sepWP_stdioSvc {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α}
    (hext : ∀ pc, prog.externAt? pc = none)
    (hsvc : prog.svc = Syscall.standard)
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry_pc → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P_init : SepProp, (s0.mem ⊨ P_init ∗ R) ∧
        SepWP (prog.withSvc hbStdioSvc) (s0.readReg64 Reg.lr) s0 P_init (fun sf P_f =>
          (StdioSvcPreserved s0 sf → sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) :
    subroutine_ok prog entry_pc spec := by
  apply subroutine_ok_of_sepWP_init
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨P_init, hm, hwp⟩ := h x R s0 hpc hrun hpre hsp
  refine ⟨P_init, hm, SepWP.of_stdioSvc hext hsvc ?_⟩
  exact SepWP.mono hwp fun sf P_f _ _ ⟨hpost, hsp_f, hcs_f⟩ hpr => ⟨hpost hpr, hsp_f, hcs_f⟩

private theorem readBytes_canRead_ro' {m : Memory} {ptr : BitVec 64} {R : SepProp}
    (bs : List (BitVec 8)) (hlen : bs.length ≤ 2 ^ 64) (hm : m ⊨ (ptr ↦ᵣ bs) ∗ R) :
    m.canRead ptr bs.length = true ∧ m.readBytes ptr bs.length = bs := by
  induction bs generalizing ptr R with
  | nil => exact ⟨rfl, rfl⟩
  | cons b bs ih =>
    rw [pointsToBytesRO_cons, sepConj_assoc] at hm
    have hld : SepLoad8 ptr ((ptr ↦₈ᵣ b) ∗ (((ptr + 1#64) ↦ᵣ bs) ∗ R)) b :=
      SepLoad8.of_ro_eq_addr rfl rfl
    have hm_emp : m ⊨ ((ptr ↦₈ᵣ b) ∗ (((ptr + 1#64) ↦ᵣ bs) ∗ R)) ∗ emp := by
      simpa [sepConj_emp] using hm
    have hcr1 : m.canRead ptr 1 = true := hld.readable hm_emp
    have hr1 : m.read8 ptr = b := hld.load hm_emp
    have hm_tail : m ⊨ ((ptr + 1#64) ↦ᵣ bs) ∗ ((ptr ↦₈ᵣ b) ∗ R) := by
      rw [sepConj_left_comm] at hm; exact hm
    obtain ⟨hcr_tl, hr_tl⟩ := ih (by simp at hlen; omega) hm_tail
    refine ⟨?_, by simp only [List.length_cons, Memory.readBytes, hr1, hr_tl]⟩
    rw [Memory.canRead, Bool.and_eq_true, Memory.allPerm_iff, Memory.allNoLazyFree_iff] at hcr1 hcr_tl ⊢
    have hshift : ∀ i : Nat, i > 0 → ptr + 1#64 + BitVec.ofNat 64 (i - 1) = ptr + BitVec.ofNat 64 i := by
      intro i hpos
      rw [BitVec.add_assoc, show 1#64 + BitVec.ofNat 64 (i - 1) = BitVec.ofNat 64 i by
        change BitVec.ofNat 64 1 + BitVec.ofNat 64 (i - 1) = BitVec.ofNat 64 i
        rw [← BitVec.ofNat_add]; congr 1; omega]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact hcr1.1 0 (by omega)
      · have h := hcr_tl.1 (i - 1) (by simp at hi; omega)
        rwa [hshift i hpos] at h
    · rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact hcr1.2 0 (by omega)
      · have h := hcr_tl.2 (i - 1) (by simp at hi; omega)
        rwa [hshift i hpos] at h

private theorem step_svc_write_stdout_ro' {prog : Program} {target_pc : BitVec 64}
    {s : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc buf count : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hfd : s.readReg64 .x0 = 1#64) (hbuf : s.readReg64 .x1 = buf) (hcnt : s.readReg64 .x2 = count)
    (hlen : bs.length = count.toNat)
    (hsvc : prog.evalInst (.system false 0#16) s = execWrite s)
    (hmax : count.toNat ≤ Arm64.MAX_RW_COUNT := by simp only [Arm64.MAX_RW_COUNT] at *; omega)
    (hva : buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT := by simp only [Arm64.USER_VA_LIMIT] at *; omega)
    (hnext : SepWP prog target_pc
      (((s.appendTrace (TraceEvent.ofBytes .stdout bs)).writeReg64 .x0 count).setPC (pc + 4#64))
      ((buf ↦ᵣ bs) ∗ F) post oom) :
    SepWP prog target_pc s ((buf ↦ᵣ bs) ∗ F) post oom := by
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hm' : s.mem ⊨ (buf ↦ᵣ bs) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hlen64 : bs.length ≤ 2 ^ 64 := by rw [hlen]; exact Nat.le_of_lt count.isLt
  obtain ⟨hcr, hrd⟩ := readBytes_canRead_ro' bs hlen64 hm'
  rw [hlen] at hcr hrd
  have hva_f : decide (buf.toNat + count.toNat > Arm64.USER_VA_LIMIT) = false :=
    decide_eq_false (Nat.not_lt.mpr hva)
  have hmin : min count.toNat Arm64.MAX_RW_COUNT = count.toNat := Nat.min_eq_left hmax
  have hcnt_eq : BitVec.ofNat 64 count.toNat = count := by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hexec : execWrite s =
      ((s.appendTrace (TraceEvent.ofBytes .stdout bs)).writeReg64 .x0 count).advancePC := by
    rw [execWrite_stdout s hfd]
    by_cases h0 : count = 0#64
    · subst h0
      have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero hlen
      subst hbs0
      have hnotva : ¬ (Arm64.USER_VA_LIMIT < buf.toNat) := by simpa using Nat.not_lt.mpr hva
      simp [hbuf, hcnt, hnotva, TraceEvent.ofBytes, State.appendTrace]
    · have h0_f : (count == 0#64) = false := beq_false_of_ne h0
      simp only [hbuf, hcnt, hva_f, h0_f, hmin, hcnt_eq, hcr, hrd, Bool.false_eq_true, ↓reduceIte]
  have hadv : (((s.appendTrace (TraceEvent.ofBytes .stdout bs)).writeReg64 .x0 count).advancePC) =
      (((s.appendTrace (TraceEvent.ofBytes .stdout bs)).writeReg64 .x0 count).setPC (pc + 4#64)) := by
    subst hpc; rfl
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hsvc, hexec, hadv]
  exact SepWP.to_reaches_pc hnext (by simpa using hm)

macro "wp_arg" : tactic =>
  `(tactic| (try simp (config := { decide := true }) only [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin))

set_option linter.literalFetch false in
theorem hbWrite_stdioSvc_wp {P : Program} {C : HbCliLayout} {target_pc ret_pc sp0 : BitVec 64}
    (ro : Bool) (hcSys : HbSyscallsAndStderrCode P C)
    {bufPtr : BitVec 64} {bs : List (BitVec 8)}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlen_max : bs.length ≤ Arm64.MAX_RW_COUNT)
    (hbuf_va : bufPtr.toNat + bs.length ≤ Arm64.USER_VA_LIMIT)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (hbBytesSlice ro bufPtr bs ∗ stackAt sp0 32) ∗ (F ∗ R)))
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = BitVec.ofNat 64 bs.length →
      sf.fs = s.fs → sf.tpidrEl0 = s.tpidrEl0 →
      sf.trace = s.trace ++ TraceEvent.ofBytes .stdout bs →
      SepWP (P.withSvc hbStdioSvc) target_pc sf
        ((hbBytesSlice ro bufPtr bs ∗ stackAt sp0 32) ∗ F) post oom)
    (hpc : s.pc = C.writeAddr := by wp_arg)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp : s.sp = sp0 := by wp_arg)
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by wp_arg)
    (hx0 : s.readReg32 .x0 = 1#32 := by
      simp (config := { decide := true }) only [State.readReg32, arm64_norm, *]; try bv_bits)
    (hx1 : s.readReg64 .x1 = bufPtr := by wp_arg)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length := by wp_arg) :
    SepWP (P.withSvc hbStdioSvc) target_pc s Pre post oom := by
  have hc' := hcSys.withSvc hbStdioSvc
  unpack_stdout_code hbSyscallIoChunks hc'.io
  have hsvc_fn : (P.withSvc hbStdioSvc).fetch (C.std.sccpAddr + 0x1c#64) =
      some (.system false 0#16) :=
    Program.fetch_of_hasCode_decodeAt 7 (hex := sccpWords)
      (by with_reducible assumption) (by simp only [wp_norm]) (by decide)
  refine SepWP.weaken_pre_frame (P' := (hbBytesSlice ro bufPtr bs ∗ stackAt sp0 32) ∗ F)
    (fun R hm => by rw [sepConj_assoc]; exact hpre R hm) ?_
  conv => arg 4; rw [sepConj_comm (hbBytesSlice ro bufPtr bs) (stackAt sp0 32),
    sepConj_assoc, ← hsp, stackAt_eq_cells s.sp 4]
  unpack_cells 4
  wp_steps; norm_jmp; wp_steps; norm_jmp; wp_steps 7
  have hlen_lt : bs.length < 2 ^ 63 := by
    simp only [Arm64.MAX_RW_COUNT] at hlen_max; omega
  have hcnt_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hhi : ConditionHolds CondCode.HI (addsPState64 (BitVec.ofNat 64 bs.length) 4096#64) = false := by
    rw [conditionHolds_hi_addsPState64]
    have hult : BitVec.ult (BitVec.ofNat 64 bs.length + 4096#64) (BitVec.ofNat 64 bs.length) = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_add, BitVec.toNat_ofNat, hcnt_toNat]
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [hult, Bool.false_and]
  have hsvc_eval : ∀ st : State, st.readReg64 .x8 = 64#64 →
      (P.withSvc hbStdioSvc).evalInst (.system false 0#16) st = execWrite st := fun st hx8 => by
    simp [Program.evalInst, Program.withSvc, execInstWithSvc, wp_norm, arm64_norm, hx8]
  refine SepWP.weaken_pre (P' := hbBytesSlice ro bufPtr bs ∗ ?F_sl) (by sep_frame) ?_
  have htail : ∀ st : State, st.pc = C.std.syscallRetAddr → st.status = .Running →
      st.sp = sp0 → CalleeSavedPreserved s st →
      st.readReg64 Reg.lr = ret_pc →
      st.readReg64 .x0 = BitVec.ofNat 64 bs.length →
      st.fs = s.fs → st.tpidrEl0 = s.tpidrEl0 →
      st.trace = s.trace ++ TraceEvent.ofBytes .stdout bs →
      SepWP (P.withSvc hbStdioSvc) target_pc st
        (stackAt sp0 32 ∗ (hbBytesSlice ro bufPtr bs ∗ F)) post oom := by
    intro st hpc_t hrun_t hsp_t hcs_t hlr_t hx0_t hfs_t htid_t htr_t
    have hsp_al : st.spAligned = true := by unfold State.spAligned at *; rw [hsp_t, ← hsp]; exact hsp_align
    conv => arg 4; rw [← hsp_t, stackAt_eq_cells st.sp 4]
    unpack_cells 4
    wp_steps
    refine SepWP.weaken_pre_frame (P' := (hbBytesSlice ro bufPtr bs ∗ stackAt sp0 32) ∗ F)
      (fun _ _ => by rw [stackAt_eq_cells sp0 4]; repack_cells) ?_
    exact hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun_t])
      (by simp [wp_norm, arm64_norm])
      (by unpack_cs hcs_t; close_cs) wp_a
      (by simp [wp_norm, arm64_norm, hfs_t]) (by simp [wp_norm, arm64_norm, htid_t])
      (by simp [wp_norm, arm64_norm, htr_t])
  cases ro
  · dsimp only [hbBytesSlice] at htail ⊢
    apply (SepWP.step_svc_write_stdio true (pc := C.std.sccpAddr + 0x1c#64)
      (buf := bufPtr) (count := BitVec.ofNat 64 bs.length))
    · exact wp_a
    · simp [wp_norm, arm64_norm, hrun]
    · exact hsvc_fn
    · simp only [wp_norm, arm64_norm] at hx0 ⊢; bv_bits
    · exact wp_a
    · exact wp_a
    · exact hcnt_toNat.symm
    · exact hsvc_eval _ wp_a
    conv in State.setPC _ _ => arg 2; rw [BitVec.add_assoc]; simp only [BitVec.reduceAdd]
    wp_steps; wp_steps; norm_jmp
    refine SepWP.weaken_pre_frame (P' := stackAt sp0 32 ∗ ((bufPtr ↦ₛ bs) ∗ F))
      (fun _ _ => by rw [stackAt_eq_cells sp0 4]; repack_cells) ?_
    exact htail _ wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a (by close_cs)
      wp_a wp_a (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, State.appendTrace])
  · dsimp only [hbBytesSlice] at htail ⊢
    apply (step_svc_write_stdout_ro' (pc := C.std.sccpAddr + 0x1c#64)
      (buf := bufPtr) (count := BitVec.ofNat 64 bs.length))
    · exact wp_a
    · simp [wp_norm, arm64_norm, hrun]
    · exact hsvc_fn
    · simp only [wp_norm, arm64_norm] at hx0 ⊢; bv_bits
    · exact wp_a
    · exact wp_a
    · exact hcnt_toNat.symm
    · exact hsvc_eval _ wp_a
    conv in State.setPC _ _ => arg 2; rw [BitVec.add_assoc]; simp only [BitVec.reduceAdd]
    wp_steps; wp_steps; norm_jmp
    refine SepWP.weaken_pre_frame (P' := stackAt sp0 32 ∗ ((bufPtr ↦ᵣ bs) ∗ F))
      (fun _ _ => by rw [stackAt_eq_cells sp0 4]; repack_cells) ?_
    exact htail _ wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a (by close_cs)
      wp_a wp_a (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, State.appendTrace])

private theorem call_memmove_zero {P : Program} {memmoveAddr target_pc ret_pc dst src : BitVec 64}
    (hMemmove : subroutine_ok P memmoveAddr stdMemcpySpec)
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → sf.readReg64 .x0 = dst →
      sf.fs = s.fs → sf.tpidrEl0 = s.tpidrEl0 → sf.trace = s.trace →
      SepWP P target_pc sf Pre post oom)
    (hpc : s.pc = memmoveAddr := by wp_arg)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by wp_arg)
    (hx0 : s.readReg64 .x0 = dst := by wp_arg)
    (hx1 : s.readReg64 .x1 = src := by wp_arg)
    (hx2 : s.readReg64 .x2 = 0#64 := by wp_arg)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ stdMemcpySpec.onOom (dst, src, []) s sf ∗ (Pre ∗ R')) →
      (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame hMemmove (x := (dst, src, [])) (F := Pre)
    hpc hrun hsp_align hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ h_oom
  · intro R hm
    dsimp only [stdMemcpySpec, List.length_nil]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, by decide⟩, by simpa [memRegion_zero, pointsToBytes_nil, emp_sepConj] using hm⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f
    dsimp only [stdMemcpySpec]
    rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_f, hstd_f⟩
    simpa [pointsToBytes_nil, emp_sepConj] using
      hnext sf hpc_f hrun_f hsp_f hcs_f hx0_f hstd_f.1 hstd_f.2.2.1 hstd_f.2.1

theorem stackAt_split {sp : BitVec 64} (n1 n2 : Nat) (hn : n1 + n2 ≤ 2 ^ 64 := by decide) :
    stackAt sp (n1 + n2) = stackAt sp n1 ∗ stackAt (sp - BitVec.ofNat 64 n1) n2 := by
  rw [stackAt_eq_stackFrameAt sp (n1 + n2) hn, stackFrameAt_split sp n1 n2 hn,
      ← stackAt_eq_stackFrameAt sp n1 (by omega), ← stackAt_eq_stackFrameAt _ n2 (by omega)]

/-! ### Non-Empty `BufWriter<StdoutRaw>::flush_buf` -/

def hbBufWriterFlushBufRes (bwPtr bufPtr : BitVec 64) (len : BitVec 64)
    (pan : BitVec 8) (bs : List (BitVec 8)) : SepProp :=
  ((bwPtr + 0x08#64) ↦₆₄ bufPtr) ∗
  ((bwPtr + 0x10#64) ↦₆₄ len) ∗
  ((bwPtr + 0x18#64) ↦₈ pan) ∗
  (bufPtr ↦ₛ bs)

theorem hbBufWriterFlushBuf_stdioSvc_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc sp0 bwPtr bufPtr : BitVec 64} {pan0 : BitVec 8} {bs : List (BitVec 8)}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlen_lo : 1 ≤ bs.length) (hlen_hi : bs.length ≤ 1024)
    (hbuf_va : bufPtr.toNat + bs.length ≤ Arm64.USER_VA_LIMIT)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (hbBufWriterFlushBufRes bwPtr bufPtr (BitVec.ofNat 64 bs.length) pan0 bs ∗
        stackAt sp0 144) ∗ (F ∗ R)))
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      sf.fs = s.fs → sf.tpidrEl0 = s.tpidrEl0 →
      sf.trace = s.trace ++ TraceEvent.ofBytes .stdout bs →
      SepWP (P.withSvc hbStdioSvc) target_pc sf
        ((hbBufWriterFlushBufRes bwPtr bufPtr 0#64 0#8 bs ∗ stackAt sp0 144) ∗ F) post oom)
    (hpc : s.pc = C.bufWriterFlushBufAddr := by wp_arg)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp : s.sp = sp0 := by wp_arg)
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by wp_arg)
    (hx0 : s.readReg64 .x0 = bwPtr := by wp_arg) :
    SepWP (P.withSvc hbStdioSvc) target_pc s Pre post oom := by
  have hcFb := (hc.withSvc hbStdioSvc).bufWriterFlushBuf
  unpack_stdout_code hbBufWriterFlushBufChunks hcFb
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne0' : BitVec.ofNat 64 bs.length ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h
    rw [hlen_toNat] at this; change bs.length = 0 at this; omega
  have hne0 : (BitVec.ofNat 64 bs.length == 0#64) = false := beq_false_of_ne hne0'
  have hcmn : (BitVec.ofNat 64 bs.length + 1#64 == 0#64) = false :=
    beq_false_of_ne fun h => by
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_add, hlen_toNat, show (1#64).toNat = 1 from rfl,
          show (0#64).toNat = 0 from rfl, Nat.mod_eq_of_lt (by omega)] at this
      omega
  have hult_self : (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 bs.length) = false := by
    simp [BitVec.ult]
  refine SepWP.weaken_pre_frame
    (P' := stackAt sp0 112 ∗ (stackAt (sp0 - 112#64) 32 ∗
      hbBufWriterFlushBufRes bwPtr bufPtr (BitVec.ofNat 64 bs.length) pan0 bs ∗ F))
    (fun R hm => by
      have hm' := hpre R hm
      rw [show (144 : Nat) = 112 + 32 from rfl, stackAt_split 112 32] at hm'
      exact (by sep_entail : _ → _) hm') ?_
  dsimp only [hbBufWriterFlushBufRes]
  conv => arg 4; rw [← hsp, stackAt_eq_cells s.sp 14]
  unpack_cells 14
  wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; norm_jmp
  refine hbWrite_stdioSvc_wp false hcSys (sp0 := sp0 - 112#64) (bufPtr := bufPtr) (bs := bs)
    (ret_pc := C.bufWriterFlushBufAddr + 0x68#64) (by simp only [Arm64.MAX_RW_COUNT]; omega) hbuf_va
    (by dsimp only [hbBytesSlice]; rw [hsp]; sep_frame)
    fun s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hfs1 htid1 htr1 => ?_
  dsimp only [hbBytesSlice]
  have hsp1_al : s1.spAligned = true := by
    simp only [State.spAligned, hsp1, ← hsp]; exact s.spAligned_sub 112#64 hsp_align
  have hx19_1 : s1.readReg64 (.gpr 19#5) = bwPtr := by rw [hcs1.1]; exact wp_a
  have hx20_1 : s1.readReg64 (.gpr 20#5) = 0#64 := by rw [hcs1.2.1]; exact wp_a
  have hx24_1 : s1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 bs.length := by rw [hcs1.2.2.2.2.2.1]; exact wp_a
  have hx0_1' : s1.readReg64 (.gpr 0#5) = BitVec.ofNat 64 bs.length := hx0_1
  wp_steps; wp_steps; wp_steps; norm_jmp
  refine call_memmove_zero hMemmove (dst := bufPtr) (src := bufPtr + BitVec.ofNat 64 bs.length)
    (ret_pc := C.bufWriterFlushBufAddr + 0x100#64)
    fun s2 hpc2 hrun2 hsp2 hcs2 hx0_2 hfs2 htid2 htr2 => ?_
  have hsp2_eq : s2.sp = sp0 - 112#64 := by rw [hsp2]; simp [wp_norm, arm64_norm, hsp1]
  have hsp2_al : s2.spAligned = true := by
    simp only [State.spAligned, hsp2_eq, ← hsp]; exact s.spAligned_sub 112#64 hsp_align
  have hx19_2 : s2.readReg64 (.gpr 19#5) = bwPtr := by
    rw [hcs2.1]; simp [wp_norm, arm64_norm, hx19_1]
  have hx22_2 : s2.readReg64 (.gpr 22#5) = 0#64 := by
    rw [hcs2.2.2.2.1]; simp [wp_norm, arm64_norm]
  wp_steps; wp_steps
  refine SepWP.weaken_pre_frame
    (P' := (hbBufWriterFlushBufRes bwPtr bufPtr 0#64 0#8 bs ∗ stackAt sp0 144) ∗ F)
    (fun _ _ => by
      dsimp only [hbBufWriterFlushBufRes]
      rw [show (144 : Nat) = 112 + 32 from rfl, stackAt_split 112 32, ← hsp, stackAt_eq_cells s.sp 14, hsp]
      repack_cells) ?_
  exact hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun2])
    (by simp [wp_norm, arm64_norm])
    (by unpack_cs hcs1; unpack_cs hcs2; close_cs)
    wp_a
    (by simp [wp_norm, arm64_norm, hfs2, hfs1])
    (by simp [wp_norm, arm64_norm, htid2, htid1])
    (by simp [wp_norm, arm64_norm, htr2, htr1])

def hbBufWriterFlushBufSpec (_C : HbCliLayout) :
    Spec (BitVec 64 × BitVec 64 × BitVec 8 × List (BitVec 8)) where
  pre := fun (bwPtr, bufPtr, pan0, bs) s0 =>
    ⌜s0.readReg64 .x0 = bwPtr ∧ 1 ≤ bs.length ∧ bs.length ≤ 1024 ∧
      bufPtr.toNat + bs.length ≤ Arm64.USER_VA_LIMIT⌝ ∗
    (hbBufWriterFlushBufRes bwPtr bufPtr (BitVec.ofNat 64 bs.length) pan0 bs ∗ stackAt s0.sp 144)
  post := fun (bwPtr, bufPtr, _, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧
      sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout bs ∧
      FmtIoStatePreserved s0 sf ∧ HbNonVmPreserved s0 sf⌝ ∗
    (hbBufWriterFlushBufRes bwPtr bufPtr 0#64 0#8 bs ∗ stackAt s0.sp 144)

theorem hbBufWriterFlushBuf_ok {P : Program} {C : HbCliLayout}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.bufWriterFlushBufAddr (hbBufWriterFlushBufSpec C) := by
  refine subroutine_ok_of_sepWP_stdioSvc hext hsvc fun ⟨bwPtr, bufPtr, pan0, bs⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [hbBufWriterFlushBufSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlo, hhi, hbuf_va⟩, hm⟩
  refine ⟨(hbBufWriterFlushBufRes bwPtr bufPtr (BitVec.ofNat 64 bs.length) pan0 bs ∗
    stackAt s0.sp 144) ∗ emp, by simpa [sepConj_emp] using hm, ?_⟩
  refine hbBufWriterFlushBuf_stdioSvc_wp hc hcSys hMemmove hlo hhi hbuf_va
    (by sep_frame) (fun sf hpcf hrunf hspf hcsf hx0f hfsf htidf htrf => ?_)
    hpc hrun rfl hsp rfl hx0
  refine SepWP.done hpcf hrunf ⟨fun hpr hmf => ?_, hspf, hcsf⟩
  dsimp only [hbBufWriterFlushBufSpec]
  rw [sepConj_emp] at hmf
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0f, htrf, hpr.toFmtIo hfsf htidf, hpr.toHbNonVm htidf⟩, hmf⟩

end CaseStudies.Hashbrown.Proofs.StdCli
