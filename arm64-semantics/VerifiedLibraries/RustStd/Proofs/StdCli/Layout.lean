/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import ProofLib.StdStartup.TopInit
public import ProofLib.StdStartup.StartupCompose
public import ProofLib.MallocngIface

/-!
# Placement-Generic Layout for Prebuilt-`libstd` CLI Binaries

`StdCliLayout` represents every code entrypoint, `.rodata` constant, `.data.rel.ro`/`.got` slot,
and `.data`/`.bss` global symbolically (`std : StdBinaryLayout`, `mallocng : MallocngAddrs`, and
`std::io` / `core::fmt` / `lang_start_internal` addresses), alongside shared `Stdin`, `Stdout`, and
`ThreadId` separation-logic invariants.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.RustStd.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open VerifiedLibraries.RustStd

/-! ## Symbolic Address Configuration -/

/-- Symbolic virtual-address configuration for the prebuilt-`libstd` + `musl` 1.2.5 CLI runtime,
    `std::io` (`Stdin`, `Stdout`, `Stderr`), `u64` decimal `Display` formatter, and allocator
    shims, with zero concrete binary hex addresses. -/
structure StdCliLayout where
  /-- Standard `musl` + Rust `std` startup/teardown layout. -/
  std : StdBinaryLayout
  /-- `musl` 1.2.5 `mallocng` code and data addresses. -/
  mallocng : MallocngAddrs
  /-- Segment indices for `.rodata`, `.text`, `.data.rel.ro`/`.got`, and `.data`/`.bss`. -/
  roSegIdx    : Nat
  rxSegIdx    : Nat
  relroSegIdx : Nat
  rwSegIdx    : Nat

  -- Allocator shims, `memmove`, and `memrchr`
  rustAllocAddr     : BitVec 64
  rustDeallocAddr   : BitVec 64
  rustReallocAddr   : BitVec 64
  rustAllocShimAddr : BitVec 64
  rdlAllocAddr      : BitVec 64
  rdlDeallocAddr    : BitVec 64
  rdlReallocAddr    : BitVec 64
  memmoveAddr       : BitVec 64
  memrchrAddr       : BitVec 64

  -- `read` / `write` syscall wrappers
  readAddr  : BitVec 64
  writeAddr : BitVec 64

  -- `RawVecInner` growth helpers & outlined `OnceLock` helpers
  rawVecDoReserveAddr  : BitVec 64
  rawVecFinishGrowAddr : BitVec 64
  outlinedOnceCallAddr : BitVec 64
  outlinedFn72Addr     : BitVec 64

  -- `Stdin` initialization & `read_to_end`
  stdioStdinAddr         : BitVec 64
  stdinOnceLockInitAddr  : BitVec 64
  stdinInitShimAddr      : BitVec 64
  stdinInitClosureAddr   : BitVec 64
  stdinReadToEndAddr     : BitVec 64
  bufReaderReadToEndAddr : BitVec 64
  defaultReadToEndAddr   : BitVec 64
  smallProbeReadAddr     : BitVec 64

  -- `Stderr` locked writer
  stderrWriteAllAddr     : BitVec 64
  refStderrWriteAllAddr  : BitVec 64
  unixStderrWriteAllAddr : BitVec 64

  -- `Stdout` `LineWriter`, `u64` `Display` formatting, & `lang_start_internal` glue
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

  -- `std::io` & `core::fmt` read-only `.rodata` constants
  langStartVtableAddr : BitVec 64
  nlByteAddr          : BitVec 64
  stdoutLabelStrAddr  : BitVec 64
  decDigitsLutAddr    : BitVec 64

  -- `.data.rel.ro` vtables, error/location records, and `.got` slot
  stdoutInitVtableAddr   : BitVec 64
  stdinInitVtableAddr    : BitVec 64
  adapterWriteVtableAddr : BitVec 64
  onceLockPanicLocAddr   : BitVec 64
  defaultOsFunctionsAddr : BitVec 64
  writeZeroErrAddr       : BitVec 64
  osFunctionsGotAddr     : BitVec 64

  -- `.data` & `.bss` globals
  stdinGlobalAddr      : BitVec 64
  osFunctionsAddr      : BitVec 64
  captureUsedAddr      : BitVec 64
  globalPanicCountAddr : BitVec 64
  stderrGlobalAddr     : BitVec 64
  needAltstackAddr     : BitVec 64
  mainAltstackAddr     : BitVec 64

abbrev HbCliLayout := StdCliLayout

/-! ## Read-Only `.rodata` Payloads, Vtables, and Frozen Constants -/

def formatDecimalAux : Nat → Nat → List (BitVec 8) → List (BitVec 8)
  | 0, _, ds => ds
  | fuel + 1, n, ds =>
    let d : BitVec 8 := BitVec.ofNat 8 (0x30 + n % 10)
    let n' := n / 10
    if n' == 0 then d :: ds
    else formatDecimalAux fuel n' (d :: ds)

/-- Format `n : Nat` as its base-10 ASCII bytes (`'0'..'9'`), e.g. `0 ↦ "0"`, `42 ↦ "42"`. -/
def formatDecimal (n : Nat) : List (BitVec 8) :=
  formatDecimalAux (n + 1) n []

def nlByteBytes : List (BitVec 8) := [0xc0#8, 0x01#8, 0x0a#8, 0x00#8]

/-- Rust `core::num::fmt` `DEC_DIGITS_LUT` (`200` ASCII bytes `"000102...9899"`). -/
def decDigitsLutBytes : List (BitVec 8) :=
  (List.range 100).flatMap fun i =>
    [BitVec.ofNat 8 (0x30 + i / 10), BitVec.ofNat 8 (0x30 + i % 10)]

@[simp] theorem nlByteBytes_length : nlByteBytes.length = 4 := rfl
@[simp] theorem decDigitsLutBytes_length : decDigitsLutBytes.length = 200 := by
  unfold decDigitsLutBytes
  rw [List.length_flatMap]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, List.map_const', List.length_range]
  rfl

/-- 48-byte `core::fmt::Write` vtable for `Adapter<StdoutLock>`:
    `[drop_in_place, size = 16, align = 8, write_str, write_char, write_fmt]`. -/
def adapterWriteVtableBytes (C : StdCliLayout) : List (BitVec 8) :=
  unpack64 C.adapterDropShimAddr ++
  unpack64 16#64 ++
  unpack64 8#64 ++
  unpack64 C.adapterWriteStrAddr ++
  unpack64 C.adapterWriteCharAddr ++
  unpack64 C.adapterWriteFmtAddr

def HbAdapterWriteVtableRo (C : StdCliLayout) : SepProp :=
  let a := C.adapterWriteVtableAddr
  (a ↦₆₄ᵣ C.adapterDropShimAddr) ∗
  ((a + 0x08#64) ↦₆₄ᵣ 16#64) ∗
  ((a + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((a + 0x18#64) ↦₆₄ᵣ C.adapterWriteStrAddr) ∗
  ((a + 0x20#64) ↦₆₄ᵣ C.adapterWriteCharAddr) ∗
  ((a + 0x28#64) ↦₆₄ᵣ C.adapterWriteFmtAddr)

abbrev StdAdapterWriteVtableRo := HbAdapterWriteVtableRo

theorem HbAdapterWriteVtableRo_dup (C : StdCliLayout) :
    (HbAdapterWriteVtableRo C ∗ HbAdapterWriteVtableRo C) = HbAdapterWriteVtableRo C :=
  sepConj_dup (pointsTo64RO_dup _ _) (sepConj_dup (pointsTo64RO_dup _ _)
    (sepConj_dup (pointsTo64RO_dup _ _) (sepConj_dup (pointsTo64RO_dup _ _)
      (sepConj_dup (pointsTo64RO_dup _ _) (pointsTo64RO_dup _ _)))))

abbrev StdAdapterWriteVtableRo_dup := @HbAdapterWriteVtableRo_dup

theorem StdVtableRo_dup (addr shimAddr closureAddr : BitVec 64) :
    (StdVtableRo addr shimAddr closureAddr ∗ StdVtableRo addr shimAddr closureAddr) =
      StdVtableRo addr shimAddr closureAddr :=
  sepConj_dup (pointsTo64RO_dup _ _) (sepConj_dup (pointsTo64RO_dup _ _)
    (sepConj_dup (pointsTo64RO_dup _ _) (sepConj_dup (pointsTo64RO_dup _ _)
      (pointsTo64RO_dup _ _))))

/-- Duplicable read-only `.rodata` slices, closure/formatter vtables, and frozen constants
    for `std::io` and `core::fmt`. -/
def StdCliRoData (C : StdCliLayout) : SepProp :=
  (C.nlByteAddr ↦ᵣ nlByteBytes) ∗
  (C.decDigitsLutAddr ↦ᵣ decDigitsLutBytes) ∗
  StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
  StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
  HbAdapterWriteVtableRo C ∗
  (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
  (C.captureUsedAddr ↦₈ᵣ 0#8) ∗
  (C.globalPanicCountAddr ↦₆₄ᵣ 0#64)

theorem StdCliRoData_dup (C : StdCliLayout) :
    (StdCliRoData C ∗ StdCliRoData C) = StdCliRoData C :=
  sepConj_dup (pointsToBytesRO_dup _ _)
    (sepConj_dup (pointsToBytesRO_dup _ _) (sepConj_dup (StdVtableRo_dup _ _ _)
      (sepConj_dup (StdVtableRo_dup _ _ _) (sepConj_dup (HbAdapterWriteVtableRo_dup _)
        (sepConj_dup (pointsTo64RO_dup _ _)
          (sepConj_dup (pointsTo8RO_dup _ _) (pointsTo64RO_dup _ _)))))))

/-- Uninitialized `STDIN` `OnceLock<Mutex<BufReader<StdinRaw>>>` atoms at `userMain` entry. -/
def HbStdinUninit (C : StdCliLayout) : SepProp :=
  (C.stdinGlobalAddr ↦ₛ List.replicate 48 0#8) ∗
  ((C.stdinGlobalAddr + 0x30#64) ↦₃₂ 3#32) ∗
  ((C.stdinGlobalAddr + 0x34#64) ↦₃₂ 0#32)

abbrev StdStdinUninit := HbStdinUninit

/-- Shared cached `ThreadId` invariant across `<&Stdout as Write>::write_fmt`,
    `<&Stderr as Write>::write_all`, and post-`main` `cleanupClosure`:
    either `tid = 0#64` (not yet cached on the main thread) or `tid = 1#64`
    (cached at `[tp + 0x58]` after atomic increment of `threadIdCounterAddr`). -/
def HbThreadIdInv (C : StdCliLayout) (tp : BitVec 64) : SepProp :=
  ∃∗ tid : BitVec 64,
    ⌜tid = 0#64 ∨ tid = 1#64⌝ ∗
    ((tp + 0x58#64) ↦₆₄ tid) ∗
    (C.std.threadIdCounterAddr ↦₆₄ tid)

abbrev StdThreadIdInv := HbThreadIdInv

theorem HbThreadIdInv_zero (C : StdCliLayout) (tp : BitVec 64) :
    ((tp + 0x58#64) ↦₆₄ 0#64) ∗ (C.std.threadIdCounterAddr ↦₆₄ 0#64) ⊢
      HbThreadIdInv C tp := by
  unfold HbThreadIdInv
  exact Entails.trans (Entails.pure_right (Or.inl rfl) (Entails.refl _))
    (Entails.sepExists_right 0#64 (Entails.refl _))

abbrev StdThreadIdInv_zero := @HbThreadIdInv_zero

/-- Minimal `Spec` for `BufWriter<StdoutRaw>::flush_buf` on the empty-buffer fast path (`len == 0`). -/
def hbFlushZeroSpec (_C : StdCliLayout) : Spec (BitVec 64) where
  pre := fun bwPtr s0 => ⌜s0.readReg64 .x0 = bwPtr⌝ ∗ ((bwPtr + 0x10#64) ↦₆₄ 0#64) ∗ stackAt s0.sp 112
  post := fun bwPtr s0 sf => ⌜sf.readReg64 .x0 = 0#64 ∧ ProcessFieldsPreserved s0 sf⌝ ∗ ((bwPtr + 0x10#64) ↦₆₄ 0#64) ∗ stackAt s0.sp 112

abbrev stdFlushZeroSpec := hbFlushZeroSpec

/-- Process fields (`fs`, `trace`, `tpidrEl0`, `sigActions`) preserved across post-`main` cleanup,
    including `M.free` (which may modify `brk` via `munmap`/`madvise` without changing these). -/
def HbExitFieldsPreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.sigActions = s0.sigActions

abbrev StdExitFieldsPreserved := HbExitFieldsPreserved

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

/-! ## Shared `STDOUT` (`LineWriter<StdoutRaw>`) Global Invariant -/

/-- Shared separation-logic invariant for `STDOUT` (`C.std.stdoutGlobalAddr`, `60` bytes
    `[g .. g + 0x3c)`) across `userMain` (`__print`) and post-`main` `cleanupClosure`:
    - `init = false`: uninitialized (`Once` state `[g + 0x38] = 3#32`, `[g .. g + 0x38)` zeroed,
      `0` heap blocks).
    - `init = true`: initialized, unlocked `ReentrantLock<RefCell<LineWriter<StdoutRaw>>>` with
      `cap = 1024`, `len = 0` (flushed on every `'\n'`), `panicked = 0`, `[g + 0x38] = 0#32`,
      and `1` live `1024`-byte `mallocng` buffer `M.Block γ bufPtr 1024`. -/
def HbStdoutInv {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (C : StdCliLayout) (M : MallocngCoreIface P addrs lim) (γ : GhostName)
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

abbrev StdStdoutInv := @HbStdoutInv

theorem HbStdoutInv_init {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (C : StdCliLayout) (M : MallocngCoreIface P addrs lim) (γ : GhostName) :
    ((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 3#32) ∗
      (C.std.stdoutGlobalAddr ↦ₛ List.replicate 56 0#8) ⊢
      HbStdoutInv C M γ false :=
  Entails.refl _

abbrev StdStdoutInv_init := @HbStdoutInv_init

def hbStdoutCost (init : Bool) : Nat :=
  if init then mallocngBlockCost 1024 else 0

abbrev stdStdoutCost := hbStdoutCost

def hbStdoutBlocks (init : Bool) : Nat :=
  if init then 1 else 0

abbrev stdStdoutBlocks := hbStdoutBlocks

/-! ## Layout Validity (`StdCliLayout.Valid`) -/

/-- Alignment, non-wrap, and structural wiring conditions on `C : StdCliLayout`. -/
structure StdCliLayout.Valid (C : StdCliLayout) : Prop where
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
  nlByte_nz              : C.nlByteAddr ≠ 0#64
  nlByte_noWrap          : C.nlByteAddr.toNat + 12 ≤ 2 ^ 48

end VerifiedLibraries.RustStd.StdCli
