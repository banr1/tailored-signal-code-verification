/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Spec.Top
public import CaseStudies.Hashbrown.Proofs.PlacedCode
public import ProofLib.StdStartup.TopInit
public import ProofLib.StdStartup.StartupCompose
public import ProofLib.MallocngIface

/-!
# Symbolic Layout and Allocator Limits for `hashbrown-cli`

Defines the symbolic virtual-address record `HbCliLayout`, read-only `.rodata` and vtable
assertions, `STDOUT` and `ThreadId` global invariants, and the linear `MallocngLimits` budget
profile `hbStdLimits` instantiated in `CaseStudies/Hashbrown/Proofs/CliProof.lean`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open CaseStudies.Hashbrown

/-! ## Symbolic Address Configuration -/

/-- Symbolic virtual-address configuration for the `hashbrown-cli` runtime, `std::io`, decimal
formatter, allocator shims, and 13-block `hashbrownLib` placement. -/
structure HbCliLayout where
  /-- Standard `musl` and Rust `std` startup/teardown layout. -/
  std : StdBinaryLayout
  /-- `musl` 1.2.5 `mallocng` code and data addresses. -/
  mallocng : MallocngAddrs
  /-- 13-block placement of `hashbrownLib` in the linked executable. -/
  hbMpl : Obj.MultiPlacement
  /-- Segment indices for `.rodata`, `.text`, `.data.rel.ro`/`.got`, and `.data`/`.bss`. -/
  roSegIdx    : Nat
  rxSegIdx    : Nat
  relroSegIdx : Nat
  rwSegIdx    : Nat

  rustAllocAddr     : BitVec 64
  rustDeallocAddr   : BitVec 64
  rustReallocAddr   : BitVec 64
  rustAllocShimAddr : BitVec 64
  rdlAllocAddr      : BitVec 64
  rdlDeallocAddr    : BitVec 64
  rdlReallocAddr    : BitVec 64
  memmoveAddr       : BitVec 64
  memrchrAddr       : BitVec 64

  readAddr  : BitVec 64
  writeAddr : BitVec 64

  rawVecDoReserveAddr  : BitVec 64
  rawVecFinishGrowAddr : BitVec 64
  outlinedOnceCallAddr : BitVec 64
  outlinedFn72Addr     : BitVec 64

  stdioStdinAddr         : BitVec 64
  stdinOnceLockInitAddr  : BitVec 64
  stdinInitShimAddr      : BitVec 64
  stdinInitClosureAddr   : BitVec 64
  stdinReadToEndAddr     : BitVec 64
  bufReaderReadToEndAddr : BitVec 64
  defaultReadToEndAddr   : BitVec 64
  smallProbeReadAddr     : BitVec 64

  stderrWriteAllAddr     : BitVec 64
  refStderrWriteAllAddr  : BitVec 64
  unixStderrWriteAllAddr : BitVec 64

  cMainEntryAddr             : BitVec 64
  langStartClosureAddr       : BitVec 64
  langStartShimAddr          : BitVec 64
  langStartInternalAddr      : BitVec 64
  makeStackHandlerAddr       : BitVec 64
  dropStackHandlerAddr       : BitVec 64
  printToBufferCaptureAddr   : BitVec 64
  stdoutWriteFmtAddr         : BitVec 64
  stdoutInitShimAddr         : BitVec 64
  stdoutInitClosureAddr      : BitVec 64
  stdoutRawWriteAllAddr      : BitVec 64
  bufWriterFlushBufAddr      : BitVec 64
  bufWriterWriteAllColdAddr  : BitVec 64
  stdoutLockWriteAllAddr     : BitVec 64
  lineWriterDropAddr         : BitVec 64
  adapterDropShimAddr        : BitVec 64
  adapterWriteStrAddr        : BitVec 64
  adapterWriteCharAddr       : BitVec 64
  adapterWriteFmtAddr        : BitVec 64
  padIntegralWritePrefixAddr : BitVec 64
  padIntegralAddr            : BitVec 64
  u64FmtInnerAddr            : BitVec 64
  u64DisplayFmtAddr          : BitVec 64
  coreFmtWriteAddr           : BitVec 64
  stdoutInitAddr             : BitVec 64
  stdioPrintAddr             : BitVec 64

  bytesEqAddr         : BitVec 64
  stripPrefixAddr     : BitVec 64
  splitOnceSpaceAddr  : BitVec 64
  parseDecimalU64Addr : BitVec 64
  parseCommandAddr    : BitVec 64
  printBoolAddr       : BitVec 64
  printU64Addr        : BitVec 64

  langStartVtableAddr : BitVec 64
  falseNlAddr         : BitVec 64
  trueNlAddr          : BitVec 64
  pfxInsertAddr       : BitVec 64
  pfxRemoveAddr       : BitVec 64
  pfxGetAddr          : BitVec 64
  pfxContainsAddr     : BitVec 64
  pfxWithCapAddr      : BitVec 64
  cmdLenAddr          : BitVec 64
  cmdIsEmptyAddr      : BitVec 64
  cmdClearAddr        : BitVec 64
  errInvalidCmdAddr   : BitVec 64
  noneNlAddr          : BitVec 64
  nlByteAddr          : BitVec 64
  errLineTooLongAddr  : BitVec 64
  stdoutLabelStrAddr  : BitVec 64
  decDigitsLutAddr    : BitVec 64

  stdoutInitVtableAddr   : BitVec 64
  stdinInitVtableAddr    : BitVec 64
  adapterWriteVtableAddr : BitVec 64
  onceLockPanicLocAddr   : BitVec 64
  defaultOsFunctionsAddr : BitVec 64
  writeZeroErrAddr       : BitVec 64
  osFunctionsGotAddr     : BitVec 64

  stdinGlobalAddr      : BitVec 64
  osFunctionsAddr      : BitVec 64
  captureUsedAddr      : BitVec 64
  globalPanicCountAddr : BitVec 64
  stderrGlobalAddr     : BitVec 64
  needAltstackAddr     : BitVec 64
  mainAltstackAddr     : BitVec 64

abbrev HbCliLayout.hbPl (C : HbCliLayout) : Obj.Placement :=
  CaseStudies.Hashbrown.Proofs.mplAsPl C.hbMpl

/-! ## Read-Only `.rodata` Payloads and Vtables -/

def falseNlBytes : List (BitVec 8) := bytesOfString "false\n"
def trueNlBytes : List (BitVec 8) := bytesOfString "true\n"
def pfxInsertBytes : List (BitVec 8) := bytesOfString "insert "
def pfxRemoveBytes : List (BitVec 8) := bytesOfString "remove "
def pfxGetBytes : List (BitVec 8) := bytesOfString "get "
def pfxContainsBytes : List (BitVec 8) := bytesOfString "contains "
def pfxWithCapBytes : List (BitVec 8) := bytesOfString "with_capacity "
def cmdLenBytes : List (BitVec 8) := bytesOfString "len"
def cmdIsEmptyBytes : List (BitVec 8) := bytesOfString "is_empty"
def cmdClearBytes : List (BitVec 8) := bytesOfString "clear"
def errInvalidCmdBytes : List (BitVec 8) := bytesOfString "error: invalid command\n"
def noneNlBytes : List (BitVec 8) := bytesOfString "none\n"
def nlByteBytes : List (BitVec 8) := [0xc0#8, 0x01#8, 0x0a#8, 0x00#8]
def errLineTooLongBytes : List (BitVec 8) := bytesOfString "error: line too long\n"

/-- Rust `core::num::fmt` `DEC_DIGITS_LUT` (`200` ASCII bytes `"000102...9899"`). -/
def decDigitsLutBytes : List (BitVec 8) :=
  (List.range 100).flatMap fun i =>
    [BitVec.ofNat 8 (0x30 + i / 10), BitVec.ofNat 8 (0x30 + i % 10)]

@[simp] theorem falseNlBytes_length : falseNlBytes.length = 6 := rfl
@[simp] theorem trueNlBytes_length : trueNlBytes.length = 5 := rfl
@[simp] theorem pfxInsertBytes_length : pfxInsertBytes.length = 7 := rfl
@[simp] theorem pfxRemoveBytes_length : pfxRemoveBytes.length = 7 := rfl
@[simp] theorem pfxGetBytes_length : pfxGetBytes.length = 4 := rfl
@[simp] theorem pfxContainsBytes_length : pfxContainsBytes.length = 9 := rfl
@[simp] theorem pfxWithCapBytes_length : pfxWithCapBytes.length = 14 := rfl
@[simp] theorem cmdLenBytes_length : cmdLenBytes.length = 3 := rfl
@[simp] theorem cmdIsEmptyBytes_length : cmdIsEmptyBytes.length = 8 := rfl
@[simp] theorem cmdClearBytes_length : cmdClearBytes.length = 5 := rfl
@[simp] theorem errInvalidCmdBytes_length : errInvalidCmdBytes.length = 23 := rfl
@[simp] theorem noneNlBytes_length : noneNlBytes.length = 5 := rfl
@[simp] theorem nlByteBytes_length : nlByteBytes.length = 4 := rfl
@[simp] theorem errLineTooLongBytes_length : errLineTooLongBytes.length = 21 := rfl
@[simp] theorem decDigitsLutBytes_length : decDigitsLutBytes.length = 200 := by
  unfold decDigitsLutBytes
  rw [List.length_flatMap]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, List.map_const', List.length_range]
  rfl

/-- 48-byte `core::fmt::Write` vtable for `Adapter<StdoutLock>`:
`[drop_in_place, size = 16, align = 8, write_str, write_char, write_fmt]`. -/
def adapterWriteVtableBytes (C : HbCliLayout) : List (BitVec 8) :=
  unpack64 C.adapterDropShimAddr ++
  unpack64 16#64 ++
  unpack64 8#64 ++
  unpack64 C.adapterWriteStrAddr ++
  unpack64 C.adapterWriteCharAddr ++
  unpack64 C.adapterWriteFmtAddr

def HbAdapterWriteVtableRo (C : HbCliLayout) : SepProp :=
  let a := C.adapterWriteVtableAddr
  (a ↦₆₄ᵣ C.adapterDropShimAddr) ∗
  ((a + 0x08#64) ↦₆₄ᵣ 16#64) ∗
  ((a + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((a + 0x18#64) ↦₆₄ᵣ C.adapterWriteStrAddr) ∗
  ((a + 0x20#64) ↦₆₄ᵣ C.adapterWriteCharAddr) ∗
  ((a + 0x28#64) ↦₆₄ᵣ C.adapterWriteFmtAddr)

theorem HbAdapterWriteVtableRo_dup (C : HbCliLayout) :
    (HbAdapterWriteVtableRo C ∗ HbAdapterWriteVtableRo C) = HbAdapterWriteVtableRo C :=
  sepConj_dup (pointsTo64RO_dup _ _) (sepConj_dup (pointsTo64RO_dup _ _)
    (sepConj_dup (pointsTo64RO_dup _ _) (sepConj_dup (pointsTo64RO_dup _ _)
      (sepConj_dup (pointsTo64RO_dup _ _) (pointsTo64RO_dup _ _)))))

theorem StdVtableRo_dup (addr shimAddr closureAddr : BitVec 64) :
    (StdVtableRo addr shimAddr closureAddr ∗ StdVtableRo addr shimAddr closureAddr) =
      StdVtableRo addr shimAddr closureAddr :=
  sepConj_dup (pointsTo64RO_dup _ _) (sepConj_dup (pointsTo64RO_dup _ _)
    (sepConj_dup (pointsTo64RO_dup _ _) (sepConj_dup (pointsTo64RO_dup _ _)
      (pointsTo64RO_dup _ _))))

def HbCliRoData (C : HbCliLayout) : SepProp :=
  (C.falseNlAddr ↦ᵣ falseNlBytes) ∗ (C.trueNlAddr ↦ᵣ trueNlBytes) ∗
  (C.pfxInsertAddr ↦ᵣ pfxInsertBytes) ∗ (C.pfxRemoveAddr ↦ᵣ pfxRemoveBytes) ∗
  (C.pfxGetAddr ↦ᵣ pfxGetBytes) ∗ (C.pfxContainsAddr ↦ᵣ pfxContainsBytes) ∗
  (C.pfxWithCapAddr ↦ᵣ pfxWithCapBytes) ∗ (C.cmdLenAddr ↦ᵣ cmdLenBytes) ∗
  (C.cmdIsEmptyAddr ↦ᵣ cmdIsEmptyBytes) ∗ (C.cmdClearAddr ↦ᵣ cmdClearBytes) ∗
  (C.errInvalidCmdAddr ↦ᵣ errInvalidCmdBytes) ∗ (C.noneNlAddr ↦ᵣ noneNlBytes) ∗
  (C.nlByteAddr ↦ᵣ nlByteBytes) ∗ (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗
  (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
  StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
  StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
  HbAdapterWriteVtableRo C ∗
  (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
  (C.captureUsedAddr ↦₈ᵣ 0#8) ∗
  (C.globalPanicCountAddr ↦₆₄ᵣ 0#64)

theorem HbCliRoData_dup (C : HbCliLayout) :
    (HbCliRoData C ∗ HbCliRoData C) = HbCliRoData C :=
  sepConj_dup (pointsToBytesRO_dup _ _) (sepConj_dup (pointsToBytesRO_dup _ _)
    (sepConj_dup (pointsToBytesRO_dup _ _) (sepConj_dup (pointsToBytesRO_dup _ _)
      (sepConj_dup (pointsToBytesRO_dup _ _) (sepConj_dup (pointsToBytesRO_dup _ _)
        (sepConj_dup (pointsToBytesRO_dup _ _) (sepConj_dup (pointsToBytesRO_dup _ _)
          (sepConj_dup (pointsToBytesRO_dup _ _) (sepConj_dup (pointsToBytesRO_dup _ _)
            (sepConj_dup (pointsToBytesRO_dup _ _) (sepConj_dup (pointsToBytesRO_dup _ _)
              (sepConj_dup (pointsToBytesRO_dup _ _) (sepConj_dup (pointsToBytesRO_dup _ _)
                (sepConj_dup (pointsToBytesRO_dup _ _) (sepConj_dup (StdVtableRo_dup _ _ _)
                  (sepConj_dup (StdVtableRo_dup _ _ _) (sepConj_dup (HbAdapterWriteVtableRo_dup _)
                    (sepConj_dup (pointsTo64RO_dup _ _)
                      (sepConj_dup (pointsTo8RO_dup _ _) (pointsTo64RO_dup _ _))))))))))))))))))))

def HbStdinUninit (C : HbCliLayout) : SepProp :=
  (C.stdinGlobalAddr ↦ₛ List.replicate 48 0#8) ∗
  ((C.stdinGlobalAddr + 0x30#64) ↦₃₂ 3#32) ∗
  ((C.stdinGlobalAddr + 0x34#64) ↦₃₂ 0#32)

/-- Cached `ThreadId` invariant: `tid = 0#64` before initialization on the main thread, or
`tid = 1#64` cached at `[tp + 0x58]` after incrementing `threadIdCounterAddr`. -/
def HbThreadIdInv (C : HbCliLayout) (tp : BitVec 64) : SepProp :=
  ∃∗ tid : BitVec 64,
    ⌜tid = 0#64 ∨ tid = 1#64⌝ ∗
    ((tp + 0x58#64) ↦₆₄ tid) ∗
    (C.std.threadIdCounterAddr ↦₆₄ tid)

theorem HbThreadIdInv_zero (C : HbCliLayout) (tp : BitVec 64) :
    ((tp + 0x58#64) ↦₆₄ 0#64) ∗ (C.std.threadIdCounterAddr ↦₆₄ 0#64) ⊢
      HbThreadIdInv C tp := by
  unfold HbThreadIdInv
  exact Entails.trans (Entails.pure_right (Or.inl rfl) (Entails.refl _))
    (Entails.sepExists_right 0#64 (Entails.refl _))

def hbFlushZeroSpec (_C : HbCliLayout) : Spec (BitVec 64) where
  pre := fun bwPtr s0 => ⌜s0.readReg64 .x0 = bwPtr⌝ ∗ ((bwPtr + 0x10#64) ↦₆₄ 0#64) ∗ stackAt s0.sp 112
  post := fun bwPtr s0 sf => ⌜sf.readReg64 .x0 = 0#64 ∧ ProcessFieldsPreserved s0 sf⌝ ∗ ((bwPtr + 0x10#64) ↦₆₄ 0#64) ∗ stackAt s0.sp 112

/-- Process fields (`fs`, `trace`, `tpidrEl0`, `sigActions`) preserved across post-`main` cleanup,
including `M.free` (which may modify `brk`). -/
def HbExitFieldsPreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.sigActions = s0.sigActions

theorem HbExitFieldsPreserved.rfl (s : State) : HbExitFieldsPreserved s s :=
  ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩
theorem HbExitFieldsPreserved.trans {s0 s1 s2 : State}
    (h01 : HbExitFieldsPreserved s0 s1) (h12 : HbExitFieldsPreserved s1 s2) :
    HbExitFieldsPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1, h12.2.2.2.trans h01.2.2.2⟩
theorem HbExitFieldsPreserved.ofStd {s0 sf : State} (h : StdFieldsPreserved s0 sf) :
    HbExitFieldsPreserved s0 sf := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
theorem HbExitFieldsPreserved.ofState {s0 sf : State} (h : StdStatePreserved s0 sf) :
    HbExitFieldsPreserved s0 sf := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
theorem HbExitFieldsPreserved.ofMallocng {s0 sf : State} (h : MallocngStatePreserved s0 sf) :
    HbExitFieldsPreserved s0 sf := ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1⟩

/-! ## `STDOUT` Global Invariant -/

/-- Separation-logic invariant for `STDOUT` (`C.std.stdoutGlobalAddr`, 60 bytes `[g .. g + 0x3c)`):
when `init = false`, the `Once` state `[g + 0x38]` is `3#32` and `[g .. g + 0x38)` is zeroed; when
`init = true`, `STDOUT` holds an unlocked `ReentrantLock<RefCell<LineWriter<StdoutRaw>>>` with
`cap = 1024`, `len = 0` (flushed on every `'\n'`), `panicked = 0`, `[g + 0x38] = 0#32`, and one
1024-byte `mallocng` buffer `M.Block γ bufPtr 1024`. -/
def HbStdoutInv {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P addrs lim) (γ : GhostName)
    (init : Bool) : SepProp :=
  let g := C.std.stdoutGlobalAddr
  if init then
    ∃∗ bufPtr : BitVec 64,
      ⌜bufPtr ≠ 0#64 ∧ 16 ∣ bufPtr.toNat ∧ bufPtr.toNat + 1024 ≤ Arm64.USER_VA_LIMIT⌝ ∗
      (g ↦₆₄ 0#64) ∗
      ((g + 0x08#64) ↦₃₂ 0#32) ∗
      ((g + 0x0c#64) ↦₃₂ 0#32) ∗
      ((g + 0x10#64) ↦₆₄ 0#64) ∗
      ((g + 0x18#64) ↦₆₄ 1024#64) ∗
      ((g + 0x20#64) ↦₆₄ bufPtr) ∗
      ((g + 0x28#64) ↦₆₄ 0#64) ∗
      ((g + 0x30#64) ↦₈ 0#8) ∗
      memRegion (g + 0x31#64) 7 ∗
      ((g + 0x38#64) ↦₃₂ 0#32) ∗
      M.Block γ bufPtr 1024 ∗
      memRegion bufPtr 1024
  else
    ((g + 0x38#64) ↦₃₂ 3#32) ∗
    (g ↦ₛ List.replicate 56 0#8)

theorem HbStdoutInv_init {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P addrs lim) (γ : GhostName) :
    ((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 3#32) ∗
      (C.std.stdoutGlobalAddr ↦ₛ List.replicate 56 0#8) ⊢
      HbStdoutInv C M γ false :=
  Entails.refl _

def hbStdoutCost (init : Bool) : Nat :=
  if init then mallocngBlockCost 1024 else 0

def hbStdoutBlocks (init : Bool) : Nat :=
  if init then 1 else 0

/-! ## Layout Validity -/

/-- Alignment, non-wrap, and wiring conditions on `C : HbCliLayout`. -/
structure HbCliLayout.Valid (C : HbCliLayout) : Prop where
  hasArgc_false          : C.std.hasArgcGlobal = false
  returnsExitCode        : C.std.userMainReturnsExitCode = true
  brkBase_eq             : C.mallocng.brkBase = C.std.brkStart
  needLocks_eq           : C.mallocng.libcNeedLocksAddr = C.std.libcAddr + 3#64
  auxv_eq                : C.mallocng.libcAuxvAddr = C.std.libcAddr + 0x08#64
  pageSize_eq            : C.mallocng.libcPageSizeAddr = C.std.libcAddr + 0x30#64
  stdinGlobal_nz         : C.stdinGlobalAddr ≠ 0#64
  stdinGlobal_align      : C.stdinGlobalAddr.toNat % 8 = 0
  stdinGlobal_noWrap     : C.stdinGlobalAddr.toNat + 56 ≤ 2 ^ 48
  stderrGlobal_nz        : C.stderrGlobalAddr ≠ 0#64
  stderrGlobal_align     : C.stderrGlobalAddr.toNat % 8 = 0
  stderrGlobal_noWrap    : C.stderrGlobalAddr.toNat + 24 ≤ 2 ^ 48
  stdoutGlobal_nz        : C.std.stdoutGlobalAddr ≠ 0#64
  stdoutGlobal_align     : C.std.stdoutGlobalAddr.toNat % 8 = 0
  stdoutGlobal_noWrap    : C.std.stdoutGlobalAddr.toNat + 64 ≤ 2 ^ 48
  cleanupOnce_align      : C.std.cleanupOnceAddr.toNat % 4 = 0
  threadIdCtr_align      : C.std.threadIdCounterAddr.toNat % 8 = 0
  threadIdCtr_noWrap     : C.std.threadIdCounterAddr.toNat + 8 ≤ 2 ^ 48
  osFunctionsGot_align   : C.osFunctionsGotAddr.toNat % 8 = 0
  osFunctionsGot_noWrap  : C.osFunctionsGotAddr.toNat + 8 ≤ 2 ^ 48
  captureUsed_noWrap     : C.captureUsedAddr.toNat + 1 ≤ 2 ^ 48
  globalPanicCount_align : C.globalPanicCountAddr.toNat % 8 = 0
  globalPanicCount_noWrap : C.globalPanicCountAddr.toNat + 8 ≤ 2 ^ 48
  stdoutInitVt_align     : C.stdoutInitVtableAddr.toNat % 8 = 0
  stdoutInitVt_noWrap    : C.stdoutInitVtableAddr.toNat + 40 ≤ 2 ^ 48
  stdinInitVt_align      : C.stdinInitVtableAddr.toNat % 8 = 0
  stdinInitVt_noWrap     : C.stdinInitVtableAddr.toNat + 40 ≤ 2 ^ 48
  adapterVt_align        : C.adapterWriteVtableAddr.toNat % 8 = 0
  adapterVt_noWrap       : C.adapterWriteVtableAddr.toNat + 48 ≤ 2 ^ 48
  decLut_noWrap          : C.decDigitsLutAddr.toNat + 200 ≤ 2 ^ 48
  falseNl_nz             : C.falseNlAddr ≠ 0#64
  falseNl_noWrap         : C.falseNlAddr.toNat + 6 ≤ 2 ^ 48
  trueNl_nz              : C.trueNlAddr ≠ 0#64
  trueNl_noWrap          : C.trueNlAddr.toNat + 5 ≤ 2 ^ 48
  pfxInsert_nz           : C.pfxInsertAddr ≠ 0#64
  pfxInsert_noWrap       : C.pfxInsertAddr.toNat + 7 ≤ 2 ^ 48
  pfxRemove_nz           : C.pfxRemoveAddr ≠ 0#64
  pfxRemove_noWrap       : C.pfxRemoveAddr.toNat + 7 ≤ 2 ^ 48
  pfxGet_nz              : C.pfxGetAddr ≠ 0#64
  pfxGet_noWrap          : C.pfxGetAddr.toNat + 4 ≤ 2 ^ 48
  pfxContains_nz         : C.pfxContainsAddr ≠ 0#64
  pfxContains_noWrap     : C.pfxContainsAddr.toNat + 9 ≤ 2 ^ 48
  pfxWithCap_nz          : C.pfxWithCapAddr ≠ 0#64
  pfxWithCap_noWrap      : C.pfxWithCapAddr.toNat + 14 ≤ 2 ^ 48
  cmdLen_nz              : C.cmdLenAddr ≠ 0#64
  cmdLen_noWrap          : C.cmdLenAddr.toNat + 3 ≤ 2 ^ 48
  cmdIsEmpty_nz          : C.cmdIsEmptyAddr ≠ 0#64
  cmdIsEmpty_noWrap      : C.cmdIsEmptyAddr.toNat + 8 ≤ 2 ^ 48
  cmdClear_nz            : C.cmdClearAddr ≠ 0#64
  cmdClear_noWrap        : C.cmdClearAddr.toNat + 5 ≤ 2 ^ 48
  errInv_nz              : C.errInvalidCmdAddr ≠ 0#64
  errInv_noWrap          : C.errInvalidCmdAddr.toNat + 23 ≤ 2 ^ 48
  noneNl_nz              : C.noneNlAddr ≠ 0#64
  noneNl_noWrap          : C.noneNlAddr.toNat + 5 ≤ 2 ^ 48
  nlByte_nz              : C.nlByteAddr ≠ 0#64
  nlByte_noWrap          : C.nlByteAddr.toNat + 12 ≤ 2 ^ 48
  errLong_nz             : C.errLineTooLongAddr ≠ 0#64
  errLong_noWrap         : C.errLineTooLongAddr.toNat + 21 ≤ 2 ^ 48

/-! ## Allocator Budget Profile -/

/-- `MallocngCoreIface` extended with tight `realloc` (`newReq ≤ lim.maxReq`). -/
structure HbMallocngIface (P : Program) (addrs : MallocngAddrs) (lim : MallocngLimits)
    extends MallocngCoreIface P addrs lim where
  realloc_ok : ∀ (γ : GhostName),
    subroutine_ok P addrs.reallocAddr
      ({ pre := fun (lc, blk, oldBlk, newReq, e0) s0 =>
           let p := s0.readReg64 (.gpr 0#5)
           ⌜newReq = (s0.readReg64 (.gpr 1#5)).toNat ∧
             newReq ≤ lim.maxReq ∧
             lc + mallocngBlockCost newReq ≤ lim.maxPeakCost ∧
             blk + 1 ≤ lim.maxPeakBlocks⌝ ∗
           Heap γ lc blk s0 ∗
           (match oldBlk with
            | none => ⌜p = 0#64⌝
            | some (oldReq, bs) =>
                ⌜p ≠ 0#64 ∧ bs.length = oldReq⌝ ∗ Block γ p oldReq ∗ (p ↦ₛ bs)) ∗
           (muslErrnoAddr s0 ↦₃₂ e0) ∗
           stackAt s0.sp MallocngStackBytes
         post := fun (lc, blk, oldBlk, newReq, _) s0 sf =>
           let ret := sf.readReg64 (.gpr 0#5)
           let kept := match oldBlk with
             | none => []
             | some (_, bs) => bs.take newReq
           let lc' := match oldBlk with
             | none => lc + mallocngBlockCost newReq
             | some (oldReq, _) => (lc - mallocngBlockCost oldReq) + mallocngBlockCost newReq
           let blk' := match oldBlk with
             | none => blk + 1
             | some _ => blk
           ⌜MallocngStatePreserved s0 sf ∧
             ret ≠ 0#64 ∧
             16 ∣ ret.toNat ∧
             ret.toNat + newReq < 2 ^ 64⌝ ∗
           Heap γ lc' blk' sf ∗
           Block γ ret newReq ∗
           (ret ↦ₛ kept) ∗
           memRegion (ret + BitVec.ofNat 64 kept.length) (newReq - kept.length) ∗
           (∃∗ e1 : BitVec 32, muslErrnoAddr s0 ↦₃₂ e1) ∗
           stackAt s0.sp MallocngStackBytes } :
        Spec (Nat × Nat × Option (Nat × List (BitVec 8)) × Nat × BitVec 32))

/-- `MallocngLimits` profile for `hashbrown-std` on `stdin` of byte length `L`: covers `Vec`
reallocation up to `2 * L + 32`, `with_capacity` up to `8192` buckets (`139272` B), and SwissTable
`resize_inner` allocations `34 * B + 8` under `77 * B ≤ 8 * L + 308`, with at most 5 simultaneous
allocations (`STDIN`, `STDOUT`, `Vec`, and at most 2 coexisting table blocks). -/
def hbStdLimits (L : Nat) : MallocngLimits where
  maxReq        := (272 * L) / 77 + 139272
  maxPeakCost   := (562 * L) / 77 + 336000
  maxPeakBlocks := 5

theorem hbStdLimits_fitsVaSpace {L : Nat} (hL : L ≤ HashbrownCliMaxStdin) :
    (hbStdLimits L).FitsVaSpace = true := by
  unfold MallocngLimits.FitsVaSpace hbStdLimits HashbrownCliMaxStdin at *
  dsimp +zetaDelta only
  exact decide_eq_true (by omega)

/-- Dynamic physical-memory budget (`4185665 + 8 * L` bytes) ruling out `mallocng` `OutOfMemory`
across `malloc` and `realloc` under `hbStdLimits L`. -/
def hbDynPhysBudget (L : Nat) : Nat :=
  4185665 + 8 * L

end CaseStudies.Hashbrown.Proofs.StdCli
