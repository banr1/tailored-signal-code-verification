/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import CaseStudies.Hashbrown.Spec
import CaseStudies.Hashbrown.Generated.HashbrownElfObj
import CaseStudies.Hashbrown.Generated.HashbrownPlacedWitness
import CaseStudies.Hashbrown.Proofs.StdCli.Top
import VerifiedLibraries.Mallocng.Proofs.PlacedInterned
import ProofLib.ProgramReflection

/-!
# Concrete `hashbrown_cli.elf` Layout & `WordTree` Certificates (`CaseStudies.Hashbrown.Proofs.CliWitness`)

- **Role:** `Role::Proof` (concrete `hashbrown_cli.elf` placement witness and `decide +kernel`
  `WordTree` certificates, outside TCB).
-/

set_option autoImplicit false

namespace CaseStudies.Hashbrown

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
open CaseStudies.Hashbrown.Proofs CaseStudies.Hashbrown.Proofs.StdCli

/-! ## 1. Concrete `hashbrown_cli.elf` PHDR Bytes, `mallocngLib` Placement, and Layouts -/

/-- Exact 504-byte (`9 × 56` B) ELF64 PHDR table at `0x200040` in `hashbrown_cli.elf`. -/
def hbPhdrBytes : List (BitVec 8) :=
  [
    0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x04#8, 0x00#8, 0x00#8, 0x00#8, 0x40#8, 0x00#8, 0x00#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x40#8, 0x00#8, 0x20#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0x40#8, 0x00#8, 0x20#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xf8#8, 0x01#8, 0x00#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xf8#8, 0x01#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0x08#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x01#8, 0x00#8, 0x00#8, 0x00#8,
    0x04#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0x00#8, 0x00#8, 0x20#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x20#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xf4#8, 0x4d#8, 0x01#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0xf4#8, 0x4d#8, 0x01#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x01#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x01#8, 0x00#8, 0x00#8, 0x00#8, 0x05#8, 0x00#8, 0x00#8, 0x00#8,
    0x00#8, 0x4e#8, 0x01#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x4e#8, 0x22#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x4e#8, 0x22#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0xc8#8, 0xbf#8, 0x04#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xc8#8, 0xbf#8, 0x04#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x01#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0x01#8, 0x00#8, 0x00#8, 0x00#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0xc8#8, 0x0d#8, 0x06#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xc8#8, 0x0d#8, 0x28#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0xc8#8, 0x0d#8, 0x28#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x08#8, 0x1e#8, 0x00#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x38#8, 0x22#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0x00#8, 0x00#8, 0x01#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x01#8, 0x00#8, 0x00#8, 0x00#8,
    0x06#8, 0x00#8, 0x00#8, 0x00#8, 0xd0#8, 0x2b#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0xd0#8, 0x2b#8, 0x29#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xd0#8, 0x2b#8, 0x29#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x28#8, 0x0b#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0xf9#8, 0x22#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x01#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x07#8, 0x00#8, 0x00#8, 0x00#8, 0x04#8, 0x00#8, 0x00#8, 0x00#8,
    0xc8#8, 0x0d#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xc8#8, 0x0d#8, 0x28#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xc8#8, 0x0d#8, 0x28#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0x30#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x50#8, 0x00#8, 0x00#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x08#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0x52#8, 0xe5#8, 0x74#8, 0x64#8, 0x04#8, 0x00#8, 0x00#8, 0x00#8, 0xc8#8, 0x0d#8, 0x06#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0xc8#8, 0x0d#8, 0x28#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0xc8#8, 0x0d#8, 0x28#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x08#8, 0x1e#8, 0x00#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x38#8, 0x22#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0x01#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x50#8, 0xe5#8, 0x74#8, 0x64#8,
    0x04#8, 0x00#8, 0x00#8, 0x00#8, 0x14#8, 0xaf#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0x14#8, 0xaf#8, 0x20#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x14#8, 0xaf#8, 0x20#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x8c#8, 0x16#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0x8c#8, 0x16#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x04#8, 0x00#8, 0x00#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x51#8, 0xe5#8, 0x74#8, 0x64#8, 0x06#8, 0x00#8, 0x00#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
    0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8 ]

/-- Interned `Obj.Interned.MultiLayout` of `VerifiedLibraries.mallocngLib` in `hashbrown_cli.elf`. -/
def hbMallocngMly : Obj.Interned.MultiLayout where
  bases := [0x262748#64, 0x262a98#64, 0x262c0c#64, 0x262cec#64, 0x262cf0#64, 0x262cf4#64, 0x2631a4#64, 0x263500#64, 0x2637f8#64, 0x264130#64, 0x264588#64, 0x2646f4#64, 0x26474c#64, 0x264a3c#64, 0x264a40#64, 0x265458#64, 0x26545c#64, 0x265514#64, 0x26555c#64, 0x2655ec#64, 0x268900#64, 0x268a90#64, 0x26901c#64, 0x269134#64]
  addrs := [0x262748#64, 0x29378c#64, 0x262748#64, 0x293700#64, 0x2631a4#64, 0x262cf0#64, 0x264130#64, 0x264a40#64, 0x26901c#64, 0x263500#64, 0x264588#64, 0x2942a0#64, 0x293788#64, 0x293790#64, 0x2059a8#64, 0x26545c#64, 0x265514#64, 0x26555c#64, 0x2655ec#64, 0x262a98#64, 0x269134#64, 0x265458#64, 0x26474c#64, 0x2637f8#64, 0x262c0c#64, 0x205a08#64, 0x205a50#64, 0x262cf0#64, 0x262cec#64, 0x262cf0#64, 0x205a28#64, 0x268900#64, 0x268a90#64, 0x26545c#64, 0x26545c#64, 0x265514#64, 0x26555c#64, 0x2655ec#64, 0x262cf4#64, 0x2646f4#64, 0x264a3c#64, 0x205a30#64]
  relax := [[], [], [], [], [], [148, 188, 952], [272, 672, 784], [108], [340, 556, 704, 760], [104, 196, 372, 524, 816], [], [], [340, 420], [], [248, 328]]

/-- Concrete `Obj.MultiPlacement` of `VerifiedLibraries.mallocngLib` in `hashbrown_cli.elf`. -/
def hbMallocngMpl : Obj.MultiPlacement :=
  hbMallocngMly.toMultiPlacement mallocngMultiL.names

/-- Concrete `ProofLib.MallocngAddrs` of `hashbrown_cli.elf`. -/
def hbMallocngAddrs : ProofLib.MallocngAddrs where
  mallocAddr               := 0x262cf0#64
  freeAddr                 := 0x262cec#64
  callocAddr               := 0x262c0c#64
  reallocAddr              := 0x264a3c#64
  alignedAllocAddr         := 0x26474c#64
  posixMemalignAddr        := 0x2646f4#64
  roTablesAddr             := 0x2059a8#64
  libcNeedLocksAddr        := 0x293703#64
  libcAuxvAddr             := 0x293708#64
  libcPageSizeAddr         := 0x293730#64
  mallocLockAddr           := 0x293788#64
  alignedAllocReplacedAddr := 0x29378c#64
  mallocReplacedAddr       := 0x293790#64
  mallocCtxAddr            := 0x2942a0#64
  brkBase                  := 0x295000#64

/-- Concrete `HbCliLayout` of `hashbrown_cli.elf`. -/
def hbCliLayout : HbCliLayout where
  std :=
    { phdrSegIdx               := 0
      rxSegIdx                 := 1
      roSegIdx                 := 0
      rwSegIdx                 := 3
      brkStart                 := 0x295000#64
      startAddr                := 0x224e00#64
      startCAddr               := 0x224e1c#64
      libcStartMainAddr        := 0x262380#64
      initLibcAddr             := 0x26212c#64
      memsetAddr               := 0x268a90#64
      staticInitTlsAddr        := 0x262510#64
      copyTlsAddr              := 0x262464#64
      memcpyAddr               := 0x268900#64
      initTpAddr               := 0x2623d4#64
      setThreadAreaAddr        := 0x2691d0#64
      dummy1Addr               := 0x262128#64
      libcStartMainStage2Addr  := 0x262344#64
      libcStartInitAddr        := 0x262304#64
      initFnAddr               := 0x270da8#64
      initLseAddr              := 0x270d38#64
      detectAndInitializeAddr  := 0x270d58#64
      getauxvalAddr            := 0x264e30#64
      rustEnableLseAddr        := 0x270d38#64
      doInitAddr               := 0x224ec0#64
      cMainAddr                := 0x225630#64
      cas8RelaxAddr            := 0x270880#64
      pollAddr                 := 0x26562c#64
      syscallCpAddr            := 0x2691b4#64
      sccpAddr                 := 0x269190#64
      syscallRetAddr           := 0x262a98#64
      signalAddr               := 0x265a1c#64
      sigactionAddr            := 0x2658f4#64
      libcSigactionAddr        := 0x26574c#64
      restoreRtAddr            := 0x2659a8#64
      sysconfAddr              := 0x261ef0#64
      beginShortBacktraceAddr  := 0x224ef8#64
      userMainAddr             := 0x225238#64
      onceCallAddr             := 0x239a3c#64
      cas4AcqAddr              := 0x270850#64
      cleanupVtableShimAddr    := 0x237ddc#64
      cleanupClosureAddr       := 0x236bf0#64
      stdoutOnceLockInitAddr   := 0x228e6c#64
      stdoutVtableShimAddr     := 0x237d30#64
      stdoutCleanupClosureAddr := 0x236b44#64
      swp4RelAddr              := 0x270970#64
      errnoLocationAddr        := 0x262748#64
      cas8AcqAddr              := 0x2708b0#64
      exitAddr                 := 0x262840#64
      dummyExitAddr            := 0x262800#64
      libcExitFiniAddr         := 0x262804#64
      doFiniAddr               := 0x224e48#64
      finiFnAddr               := 0x270db8#64
      stdioExitNeededAddr      := 0x2660d8#64
      oflLockFnAddr            := 0x266374#64
      lockFnAddr               := 0x26901c#64
      closeFileAddr            := 0x266054#64
      sysExitAddr              := 0x262864#64
      hasArgcGlobal            := false
      argcGlobalAddr           := 0x293860#64
      userMainReturnsExitCode  := true
      phdrAddr                 := 0x200040#64
      phnum                    := 9
      tlsPhdrIdx               := 5
      tlsImageAddr             := 0x280dc8#64
      phdrBytes                := hbPhdrBytes
      emptyCStrAddr            := 0x203cc0#64
      sysconfValuesAddr        := 0x2057b0#64
      cleanupVtableAddr        := 0x280ed8#64
      stdoutVtableAddr         := 0x280e88#64
      devNullStdAddr           := 0x2019a1#64
      devNullLibcAddr          := 0x205500#64
      extraRoSlices            := []
      initArrayAddr            := 0x280e00#64
      finiArrayAddr            := 0x280df8#64
      gotAddr                  := 0x282a98#64
      stdoutGlobalAddr         := 0x292be0#64
      cleanupOnceAddr          := 0x293560#64
      defaultStacksizeAddr     := 0x2936e0#64
      stderrFileAddr           := 0x2935f0#64
      stderrUsedAddr           := 0x2936d8#64
      libcAddr                 := 0x293700#64
      threadListLockAddr       := 0x293768#64
      sysinfoAddr              := 0x293770#64
      hwcapAddr                := 0x293780#64
      finalizedAddr            := 0x293798#64
      initializedAddr          := 0x293799#64
      argvGlobalAddr           := 0x293868#64
      pageSizeGlobalAddr       := 0x2938a0#64
      threadIdCounterAddr      := 0x2938a8#64
      exitingThreadIdAddr      := 0x2938b0#64
      stdDetectCacheAddr       := 0x294ec0#64
      environAddr              := 0x294108#64
      builtinTlsAddr           := 0x294110#64
      mainTlsAddr              := 0x294260#64
      prognameAddr             := 0x294290#64
      prognameFullAddr         := 0x294298#64
      haveLseAtomicsAddr       := 0x294ec8#64
      stdinUsedAddr            := 0x294658#64
      stdoutUsedAddr           := 0x294650#64
      oflHeadAddr              := 0x294660#64
      oflLockAddr              := 0x294668#64
      extraRwAtoms             := [] }
  mallocng                   := hbMallocngAddrs
  hbMpl                      := hashbrownLy.toMultiPlacement hashbrownL.names
  roSegIdx                   := 0
  rxSegIdx                   := 1
  relroSegIdx                := 2
  rwSegIdx                   := 3
  rustAllocAddr              := 0x225670#64
  rustDeallocAddr            := 0x225674#64
  rustReallocAddr            := 0x225678#64
  rustAllocShimAddr          := 0x225680#64
  rdlAllocAddr               := 0x237f10#64
  rdlDeallocAddr             := 0x237f74#64
  rdlReallocAddr             := 0x237f78#64
  memmoveAddr                := 0x268c8c#64
  memrchrAddr                := 0x26daa8#64
  readAddr                   := 0x269fb0#64
  writeAddr                  := 0x26a048#64
  rawVecDoReserveAddr        := 0x2366dc#64
  rawVecFinishGrowAddr       := 0x23d990#64
  outlinedOnceCallAddr       := 0x24d678#64
  outlinedFn72Addr           := 0x24d8d4#64
  stdioStdinAddr             := 0x245c50#64
  stdinOnceLockInitAddr      := 0x228ed0#64
  stdinInitShimAddr          := 0x237d70#64
  stdinInitClosureAddr       := 0x236b84#64
  stdinReadToEndAddr         := 0x249414#64
  bufReaderReadToEndAddr     := 0x249524#64
  defaultReadToEndAddr       := 0x22e46c#64
  smallProbeReadAddr         := 0x236768#64
  stderrWriteAllAddr         := 0x24b53c#64
  refStderrWriteAllAddr      := 0x24b560#64
  unixStderrWriteAllAddr     := 0x24cd58#64
  cMainEntryAddr             := 0x225630#64
  langStartClosureAddr       := 0x224f0c#64
  langStartShimAddr          := 0x224f28#64
  langStartInternalAddr      := 0x24496c#64
  makeStackHandlerAddr       := 0x2482c8#64
  dropStackHandlerAddr       := 0x247ec8#64
  printToBufferCaptureAddr   := 0x245a30#64
  stdoutWriteFmtAddr         := 0x24a7b8#64
  stdoutInitShimAddr         := 0x237cc8#64
  stdoutInitClosureAddr      := 0x236adc#64
  stdoutRawWriteAllAddr      := 0x24cf44#64
  bufWriterFlushBufAddr      := 0x2411ec#64
  bufWriterWriteAllColdAddr  := 0x24111c#64
  stdoutLockWriteAllAddr     := 0x24ad34#64
  lineWriterDropAddr         := 0x22d344#64
  adapterDropShimAddr        := 0x22d4a4#64
  adapterWriteStrAddr        := 0x248d48#64
  adapterWriteCharAddr       := 0x24c788#64
  adapterWriteFmtAddr        := 0x24c8ec#64
  padIntegralWritePrefixAddr := 0x26e0bc#64
  padIntegralAddr            := 0x26b1d0#64
  u64FmtInnerAddr            := 0x26badc#64
  u64DisplayFmtAddr          := 0x26f50c#64
  coreFmtWriteAddr           := 0x26c614#64
  stdoutInitAddr             := 0x228e1c#64
  stdioPrintAddr             := 0x245c88#64
  bytesEqAddr                := 0x2255b8#64
  stripPrefixAddr            := 0x224f68#64
  splitOnceSpaceAddr         := 0x22516c#64
  parseDecimalU64Addr        := 0x2251cc#64
  parseCommandAddr           := 0x224fb4#64
  printBoolAddr              := 0x224f44#64
  printU64Addr               := 0x2255f4#64
  langStartVtableAddr        := 0x200240#64
  falseNlAddr                := 0x200270#64
  trueNlAddr                 := 0x200276#64
  pfxInsertAddr              := 0x20027b#64
  pfxRemoveAddr              := 0x200282#64
  pfxGetAddr                 := 0x2002a8#64
  pfxContainsAddr            := 0x2002d4#64
  pfxWithCapAddr             := 0x2002dd#64
  cmdLenAddr                 := 0x2002eb#64
  cmdIsEmptyAddr             := 0x2002f8#64
  cmdClearAddr               := 0x200328#64
  errInvalidCmdAddr          := 0x20032d#64
  noneNlAddr                 := 0x200344#64
  nlByteAddr                 := 0x2004ef#64
  errLineTooLongAddr         := 0x200349#64
  stdoutLabelStrAddr         := 0x202a74#64
  decDigitsLutAddr           := 0x2072cb#64
  stdoutInitVtableAddr       := 0x280e48#64
  stdinInitVtableAddr        := 0x280eb0#64
  adapterWriteVtableAddr     := 0x2810a0#64
  onceLockPanicLocAddr       := 0x280e70#64
  defaultOsFunctionsAddr     := 0x281188#64
  writeZeroErrAddr           := 0x2817c8#64
  osFunctionsGotAddr         := 0x282b08#64
  stdinGlobalAddr            := 0x293568#64
  osFunctionsAddr            := 0x2936f0#64
  captureUsedAddr            := 0x293808#64
  globalPanicCountAddr       := 0x293810#64
  stderrGlobalAddr           := 0x293820#64
  needAltstackAddr           := 0x29384c#64
  mainAltstackAddr           := 0x293898#64

/-- Concrete `HbStartupLayout` of `hashbrown_cli.elf`. -/
def hbStartupLayout : HbStartupLayout where
  fcntlAddr               := 0x262884#64
  openAddr                := 0x2629fc#64
  dupAddr                 := 0x269e94#64
  initCpuFeaturesAddr     := 0x270d58#64
  initCpuFeaturesCtorAddr := 0x270a30#64
  sigaltstackAddr         := 0x2659b0#64
  mmapWrapperAddr         := 0x26545c#64
  mprotectWrapperAddr     := 0x265514#64
  munmapWrapperAddr       := 0x2655ec#64
  vmWaitAddr              := 0x265458#64
  signalHandlerAddr       := 0x2485a4#64
  gotEnvironAddr          := 0x282b80#64
  gotPrognameFullAddr     := 0x282b88#64
  gotPrognameAddr         := 0x282b90#64
  gotInitArrayStartAddr   := 0x282b98#64
  gotInitArrayEndAddr     := 0x282ba0#64
  gotFiniArrayEndAddr     := 0x282ba8#64
  gotFiniArrayStartAddr   := 0x282bb0#64
  eintrValidFlagAddr      := 0x293794#64
  mainThreadAddr          := 0x293858#64
  threadInfoRootAddr      := 0x293870#64
  threadInfoLockAddr      := 0x293888#64
  handlerSetAddr          := 0x294640#64
  unmaskDoneAddr          := 0x294648#64
  cpuFeaturesGlobalAddr   := 0x294ec0#64

/-! ## 2. Reflected `WordTree` & Concrete Kernel-Check Theorems -/

/-- Executable `Program` extracted from `seg[1]` (`0x224000..0x271000`, `78,848` words) of `hashbrownElf`. -/
noncomputable def hbRxProg : Program :=
  hbCliLayout.std.rxProgram hashbrownElf

set_option maxRecDepth 2000000 in
/-- Reflected balanced `WordTree` of `hbRxProg` (`78,848` 32-bit words). -/
noncomputable def hbRxTree : WordTree :=
  word_tree_of% hbRxProg

set_option maxRecDepth 2000000 in
theorem hbRxProg_code : hbRxProg.code = hbRxTree.toBytes := by
  rfl_kernel

theorem hbRxProg_base : hbRxProg.base = 0x224000#64 := rfl

theorem hbRxTree_size : hbRxTree.checkSize? = some 78848 := by
  decide +kernel

theorem hbCliLayout_valid : hbCliLayout.Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide +kernel

theorem hbStartupLayout_valid : hbStartupLayout.Valid hbCliLayout := by
  refine ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  all_goals decide +kernel

set_option maxHeartbeats 2000000 in
theorem hbMatchesImage_eq :
    HbMatchesImage hbCliLayout hbStartupLayout hashbrownElf = true := by
  decide +kernel

theorem hbPreMainCode_check :
    checkHbPreMainCode hbCliLayout hbStartupLayout 0x224000#64 hbRxTree = true := by
  decide +kernel

theorem hbPostMainCode_check :
    checkHbPostMainCode hbCliLayout hbStartupLayout 0x224000#64 hbRxTree = true := by
  decide +kernel

theorem hbShimsCode_check :
    checkHbShimsCode hbCliLayout 0x224000#64 hbRxTree = true := by
  decide +kernel

theorem hbMemOpsCode_check :
    checkHbMemOpsCode hbCliLayout 0x224000#64 hbRxTree = true := by
  decide +kernel

theorem hbSyscallsAndStderrCode_check :
    checkHbSyscallsAndStderrCode hbCliLayout 0x224000#64 hbRxTree = true := by
  decide +kernel

theorem hbStdinAndVecCode_check :
    checkHbStdinAndVecCode hbCliLayout 0x224000#64 hbRxTree = true := by
  decide +kernel

theorem hbStdoutCode_check :
    checkHbStdoutCode hbCliLayout 0x224000#64 hbRxTree = true := by
  decide +kernel

theorem hbFmtCode_check :
    checkHbFmtCode hbCliLayout 0x224000#64 hbRxTree = true := by
  decide +kernel

theorem hbUserMainCode_check :
    checkHbUserMainCode hbCliLayout 0x224000#64 hbRxTree = true := by
  decide +kernel

theorem hbMainCmdCode_check :
    checkHbMainCmdCode hbCliLayout 0x224000#64 hbRxTree = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem hbMallocng_inElf :
    VerifiedLibraries.mallocngLib.Placeable hbMallocngMpl ∧
    VerifiedLibraries.mallocngLib.InElf hashbrownElf hbMallocngMpl ∧
    VerifiedLibraries.mallocngLib.DataDisjoint hbMallocngMpl := by
  rw [← mallocngMultiL_toMultiPlacedLib]
  exact Obj.Interned.checkMultiDisjoint_spec mallocngMultiL_names hashbrownElfSyms_eq (by decide +kernel)

theorem hbMallocng_placeable :
    VerifiedLibraries.mallocngLib.Placeable hbMallocngMpl :=
  hbMallocng_inElf.1

theorem hbExternWiring_ok : HbExternWiring hbCliLayout := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem hbMallocngInRx_ok :
    checkHbMallocngInRx hbCliLayout hbMallocngMpl hashbrownElf = true := by
  decide +kernel

set_option maxRecDepth 2000000 in
theorem hashbrownCli_parse : ElfImage.parse hashbrownCliBytes = .ok hashbrownElf := by
  rw [show hashbrownCliBytes = hashbrownElfBytes by rfl_kernel]
  exact hashbrownElf_parse

end CaseStudies.Hashbrown
