/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process
public import ProofLib.Process
public import ProofLib.Process.Assumptions
public import ProofLib.ProgramReflection
public import ProofLib.SepLogic.Bytes
public import ProofLib.SepLogic.Region
public import ProofLib.SepLogic.Stack
public import ProofLib.MallocngIface

/-!
# Parametric Binary Layout for Static `musl` and Rust `std` Executables

Parametric segment and virtual-address layout (`StdBinaryLayout`), initial writable and read-only
global bundles, and the kernel-decidable `MatchesImage` validator for static AArch64 `ET_EXEC`
binaries linked against `musl` and Rust `std`.
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib.StdStartup

open Arm64 Arm64.Process ProofLib

/-! ## Typed Writable-Global Atoms and Parametric Binary Layout -/

/-- Typed initial writable-segment slice specification supporting 8/32/64-bit scalars
    and arbitrary byte arrays with definitionally direct `SepProp` atoms. -/
inductive RwAtom where
  | u8 (addr : BitVec 64) (val : BitVec 8)
  | u32 (addr : BitVec 64) (val : BitVec 32)
  | u64 (addr : BitVec 64) (val : BitVec 64)
  | bytes (addr : BitVec 64) (bs : List (BitVec 8))
  deriving DecidableEq, Repr

@[inline] def RwAtom.addr : RwAtom → BitVec 64
  | .u8 a _ | .u32 a _ | .u64 a _ | .bytes a _ => a

def RwAtom.rawBytes : RwAtom → List (BitVec 8)
  | .u8 _ v => [v] | .u32 _ v => unpack32 v | .u64 _ v => unpack64 v | .bytes _ b => b

def RwAtom.align : RwAtom → Nat
  | .u8 _ _ => 1 | .u32 _ _ => 4 | .u64 _ _ => 8 | .bytes _ _ => 1

def RwAtom.toSepProp : RwAtom → SepProp
  | .u8 a v => a ↦₈ v | .u32 a v => a ↦₃₂ v | .u64 a v => a ↦₆₄ v | .bytes a b => a ↦ₛ b

/-- Separating conjunction of `RwAtom`s (without trailing `emp` on non-empty lists). -/
def rwAtomListSep : List RwAtom → SepProp
  | [] => emp | [x] => x.toSepProp | x :: y :: r => x.toSepProp ∗ rwAtomListSep (y :: r)

/-- Separating conjunction of read-only `(addr, bytes)` slices. -/
def roSliceListSep : List (BitVec 64 × List (BitVec 8)) → SepProp
  | [] => emp | [(a, bs)] => a ↦ᵣ bs | (a, bs) :: xs => (a ↦ᵣ bs) ∗ roSliceListSep xs

/-- Parametric virtual-address and segment-index layout for a static AArch64 `ET_EXEC` binary
    linked against `musl` and Rust `std` (`panic = "immediate-abort"`). -/
structure StdBinaryLayout where
  (phdrSegIdx rxSegIdx roSegIdx rwSegIdx : Nat)
  (brkStart startAddr startCAddr libcStartMainAddr initLibcAddr memsetAddr : BitVec 64)
  (staticInitTlsAddr copyTlsAddr memcpyAddr initTpAddr setThreadAreaAddr : BitVec 64)
  (dummy1Addr libcStartMainStage2Addr libcStartInitAddr initFnAddr : BitVec 64)
  (initLseAddr detectAndInitializeAddr getauxvalAddr rustEnableLseAddr doInitAddr : BitVec 64)
  (cMainAddr cas8RelaxAddr pollAddr syscallCpAddr sccpAddr syscallRetAddr : BitVec 64)
  (signalAddr sigactionAddr libcSigactionAddr restoreRtAddr sysconfAddr : BitVec 64)
  (beginShortBacktraceAddr userMainAddr onceCallAddr cas4AcqAddr cleanupVtableShimAddr : BitVec 64)
  (cleanupClosureAddr stdoutOnceLockInitAddr stdoutVtableShimAddr stdoutCleanupClosureAddr : BitVec 64)
  (swp4RelAddr errnoLocationAddr cas8AcqAddr exitAddr dummyExitAddr libcExitFiniAddr : BitVec 64)
  (doFiniAddr finiFnAddr stdioExitNeededAddr oflLockFnAddr lockFnAddr closeFileAddr sysExitAddr : BitVec 64)
  hasArgcGlobal : Bool
  argcGlobalAddr : BitVec 64
  userMainReturnsExitCode : Bool
  phdrAddr : BitVec 64
  (phnum tlsPhdrIdx : Nat)
  tlsImageAddr : BitVec 64
  phdrBytes : List (BitVec 8)
  (emptyCStrAddr sysconfValuesAddr cleanupVtableAddr stdoutVtableAddr devNullStdAddr devNullLibcAddr : BitVec 64)
  extraRoSlices : List (BitVec 64 × List (BitVec 8)) := []
  (initArrayAddr finiArrayAddr gotAddr stdoutGlobalAddr cleanupOnceAddr defaultStacksizeAddr : BitVec 64)
  (stderrFileAddr stderrUsedAddr libcAddr threadListLockAddr sysinfoAddr hwcapAddr : BitVec 64)
  (finalizedAddr initializedAddr argvGlobalAddr pageSizeGlobalAddr threadIdCounterAddr : BitVec 64)
  (exitingThreadIdAddr stdDetectCacheAddr environAddr builtinTlsAddr mainTlsAddr : BitVec 64)
  (prognameAddr prognameFullAddr haveLseAtomicsAddr stdinUsedAddr stdoutUsedAddr oflHeadAddr oflLockAddr : BitVec 64)
  extraRwAtoms : List RwAtom := []
  deriving DecidableEq, Repr

/-! ## Startup Global Bundles and Decidable `ElfImage` Validator -/

/-- Little-endian 40-byte Rust `Once` closure vtable `[0, 8, 8, shimAddr, closureAddr]`. -/
def vtableBytes (shimAddr closureAddr : BitVec 64) : List (BitVec 8) :=
  unpack64 0#64 ++ unpack64 8#64 ++ unpack64 8#64 ++ unpack64 shimAddr ++ unpack64 closureAddr

/-- Read-only `SepProp` assertion for a 40-byte Rust `Once` closure vtable. -/
def StdVtableRo (addr shimAddr closureAddr : BitVec 64) : SepProp :=
  (addr ↦₆₄ᵣ 0#64) ∗ ((addr + 0x08#64) ↦₆₄ᵣ 8#64) ∗ ((addr + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((addr + 0x18#64) ↦₆₄ᵣ shimAddr) ∗ ((addr + 0x20#64) ↦₆₄ᵣ closureAddr)

/-- NUL-terminated `"/dev/null\0"` byte literal (`10` B) in `.rodata`. -/
def devNullBytes : List (BitVec 8) :=
  [0x2f#8, 0x64#8, 0x65#8, 0x76#8, 0x2f#8, 0x6e#8, 0x75#8, 0x6c#8, 0x6c#8, 0x00#8]

/-- Read-only PHDR and `.rodata` constants accessed during startup, `sysconf`, and `Once` cleanup. -/
def StdRoConstants (L : StdBinaryLayout) : SepProp :=
  (L.phdrAddr ↦ᵣ L.phdrBytes) ∗ (L.emptyCStrAddr ↦₈ᵣ 0#8) ∗ ((L.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗
  (L.devNullStdAddr ↦ᵣ devNullBytes) ∗ (L.devNullLibcAddr ↦ᵣ devNullBytes) ∗
  StdVtableRo L.cleanupVtableAddr L.cleanupVtableShimAddr L.cleanupClosureAddr ∗
  StdVtableRo L.stdoutVtableAddr L.stdoutVtableShimAddr L.stdoutCleanupClosureAddr

/-- Caller-supplied extra read-only `.rodata` slices. -/
def StdExtraRo (L : StdBinaryLayout) : SepProp := roSliceListSep L.extraRoSlices

namespace StdBinaryLayout

/-- All 52 startup/exit code entrypoints required to lie 4-byte-aligned inside `rxSeg`. -/
def codeAddrs (L : StdBinaryLayout) : List (BitVec 64) :=
  [ L.startAddr, L.startCAddr, L.libcStartMainAddr, L.initLibcAddr, L.memsetAddr, L.staticInitTlsAddr,
    L.copyTlsAddr, L.memcpyAddr, L.initTpAddr, L.setThreadAreaAddr, L.dummy1Addr, L.libcStartMainStage2Addr,
    L.libcStartInitAddr, L.initFnAddr, L.initLseAddr, L.detectAndInitializeAddr, L.getauxvalAddr,
    L.rustEnableLseAddr, L.doInitAddr, L.cMainAddr, L.cas8RelaxAddr, L.pollAddr, L.syscallCpAddr, L.sccpAddr,
    L.syscallRetAddr, L.signalAddr, L.sigactionAddr, L.libcSigactionAddr, L.restoreRtAddr, L.sysconfAddr,
    L.beginShortBacktraceAddr, L.userMainAddr, L.onceCallAddr, L.cas4AcqAddr, L.cleanupVtableShimAddr,
    L.cleanupClosureAddr, L.stdoutOnceLockInitAddr, L.stdoutVtableShimAddr, L.stdoutCleanupClosureAddr,
    L.swp4RelAddr, L.errnoLocationAddr, L.cas8AcqAddr, L.exitAddr, L.dummyExitAddr, L.libcExitFiniAddr,
    L.doFiniAddr, L.finiFnAddr, L.stdioExitNeededAddr, L.oflLockFnAddr, L.lockFnAddr, L.closeFileAddr, L.sysExitAddr ]

def initFiniAtoms (L : StdBinaryLayout) : List RwAtom :=
  [.u64 L.initArrayAddr L.initLseAddr, .u64 (L.initArrayAddr + 8#64) L.doInitAddr, .u64 L.finiArrayAddr L.doFiniAddr]
def gotAtoms (L : StdBinaryLayout) : List RwAtom :=
  [ .u64 L.gotAddr 0#64, .u64 (L.gotAddr + 0x08#64) L.finiFnAddr, .u64 (L.gotAddr + 0x10#64) L.initFnAddr,
    .u64 (L.gotAddr + 0x18#64) L.cMainAddr, .u64 (L.gotAddr + 0x20#64) 0#64, .u64 (L.gotAddr + 0x28#64) 0#64,
    .u64 (L.gotAddr + 0x30#64) 0#64, .u64 (L.gotAddr + 0x38#64) L.environAddr,
    .u64 (L.gotAddr + 0x40#64) L.prognameFullAddr, .u64 (L.gotAddr + 0x48#64) L.prognameAddr,
    .u64 (L.gotAddr + 0x50#64) L.initArrayAddr, .u64 (L.gotAddr + 0x58#64) (L.initArrayAddr + 0x10#64),
    .u64 (L.gotAddr + 0x60#64) (L.finiArrayAddr + 0x08#64), .u64 (L.gotAddr + 0x68#64) L.finiArrayAddr ]
def stderrFileAtoms (L : StdBinaryLayout) : List RwAtom :=
  [ .u64 (L.stderrFileAddr + 0x08#64) 0#64, .u64 (L.stderrFileAddr + 0x10#64) 0#64,
    .u64 (L.stderrFileAddr + 0x28#64) 0#64, .u64 (L.stderrFileAddr + 0x38#64) 0#64,
    .u32 (L.stderrFileAddr + 0x8c#64) 0xffffffff#32 ]
def dataNoStderrAtoms (L : StdBinaryLayout) : List RwAtom :=
  [ .bytes L.stdoutGlobalAddr (List.replicate 56 0#8), .u32 (L.stdoutGlobalAddr + 0x38#64) 3#32,
    .u32 (L.stdoutGlobalAddr + 0x3c#64) 0#32, .u32 L.cleanupOnceAddr 3#32,
    .u32 L.defaultStacksizeAddr 0x20000#32, .u64 L.stderrUsedAddr L.stderrFileAddr ]
def libcAtoms (L : StdBinaryLayout) : List RwAtom :=
  [ .u8 L.libcAddr 0#8, .u8 (L.libcAddr + 1#64) 0#8, .u8 (L.libcAddr + 2#64) 0#8, .u8 (L.libcAddr + 3#64) 0#8,
    .u32 (L.libcAddr + 4#64) 0#32, .u64 (L.libcAddr + 0x08#64) 0#64, .u64 (L.libcAddr + 0x10#64) 0#64,
    .u64 (L.libcAddr + 0x18#64) 0#64, .u64 (L.libcAddr + 0x20#64) 0#64, .u64 (L.libcAddr + 0x28#64) 0#64,
    .u64 (L.libcAddr + 0x30#64) 0#64, .bytes (L.libcAddr + 0x38#64) (List.replicate 48 0#8) ]
def tlsAtoms (L : StdBinaryLayout) : List RwAtom :=
  [ .bytes L.builtinTlsAddr (List.replicate 0x150 0#8),
    .u64 L.mainTlsAddr 0#64, .u64 (L.mainTlsAddr + 0x08#64) 0#64, .u64 (L.mainTlsAddr + 0x10#64) 0#64,
    .u64 (L.mainTlsAddr + 0x18#64) 0#64, .u64 (L.mainTlsAddr + 0x20#64) 0#64, .u64 (L.mainTlsAddr + 0x28#64) 0#64 ]

def bssAtoms (L : StdBinaryLayout) : List RwAtom :=
  [ .u32 L.threadListLockAddr 0#32, .u64 L.sysinfoAddr 0#64, .u64 L.hwcapAddr 0#64,
    .u8 L.finalizedAddr 0#8, .u8 L.initializedAddr 0#8 ] ++
  (if L.hasArgcGlobal then [.u64 L.argcGlobalAddr 0#64] else []) ++
  [ .u64 L.argvGlobalAddr 0#64, .u64 L.pageSizeGlobalAddr 0#64, .u64 L.threadIdCounterAddr 0#64,
    .u64 L.exitingThreadIdAddr 0#64, .u64 L.stdDetectCacheAddr 0#64, .u64 L.environAddr 0#64,
    .u64 L.prognameAddr 0#64, .u64 L.prognameFullAddr 0#64, .u8 L.haveLseAtomicsAddr 0#8,
    .u64 L.stdinUsedAddr 0#64 ] ++
  (if L.stdoutUsedAddr == L.stdinUsedAddr then [] else [.u64 L.stdoutUsedAddr 0#64]) ++
  [ .u64 L.oflHeadAddr 0#64, .u32 L.oflLockAddr 0#32 ]

def nonStderrAtoms (L : StdBinaryLayout) : List RwAtom :=
  L.initFiniAtoms ++ L.gotAtoms ++ L.dataNoStderrAtoms ++ L.libcAtoms ++ L.tlsAtoms ++ L.bssAtoms ++ L.extraRwAtoms
def stdRwAtoms (L : StdBinaryLayout) : List RwAtom :=
  L.initFiniAtoms ++ L.gotAtoms ++ L.dataNoStderrAtoms ++ L.stderrFileAtoms ++ L.libcAtoms ++ L.tlsAtoms ++ L.bssAtoms
def allRwAtoms (L : StdBinaryLayout) : List RwAtom := L.stdRwAtoms ++ L.extraRwAtoms
end StdBinaryLayout

def StdInitFiniGlobals (L : StdBinaryLayout) : SepProp := rwAtomListSep L.initFiniAtoms
def StdGotGlobals (L : StdBinaryLayout) : SepProp := rwAtomListSep L.gotAtoms
def StdStderrFile (L : StdBinaryLayout) : SepProp := rwAtomListSep L.stderrFileAtoms
def StdDataGlobals (L : StdBinaryLayout) : SepProp := rwAtomListSep L.dataNoStderrAtoms ∗ StdStderrFile L
def StdLibcGlobals (L : StdBinaryLayout) : SepProp := rwAtomListSep L.libcAtoms
def StdTlsGlobals (L : StdBinaryLayout) : SepProp := rwAtomListSep L.tlsAtoms
def StdBssGlobals (L : StdBinaryLayout) : SepProp := rwAtomListSep L.bssAtoms
def StdInitGlobals (L : StdBinaryLayout) : SepProp :=
  StdInitFiniGlobals L ∗ StdGotGlobals L ∗ StdDataGlobals L ∗ StdLibcGlobals L ∗ StdTlsGlobals L ∗ StdBssGlobals L
def StdExtraRw (L : StdBinaryLayout) : SepProp := rwAtomListSep L.extraRwAtoms

/-- Kernel-speed check that `[addr, addr + expected.length)` lies within `seg` and equals `expected`. -/
def checkSegSlice (seg : Snapshot.Region) (segLen : Nat) (addr : BitVec 64) (expected : List (BitVec 8)) : Bool :=
  seg.start.toNat ≤ addr.toNat && addr.toNat + expected.length ≤ seg.start.toNat + segLen &&
  fastTake expected.length (fastDrop (addr.toNat - seg.start.toNat) seg.bytes) == expected
def intervalDisjoint (iv1 iv2 : Nat × Nat) : Bool :=
  iv1.2 == 0 || iv2.2 == 0 || iv1.1 + iv1.2 ≤ iv2.1 || iv2.1 + iv2.2 ≤ iv1.1
def intervalsPairwiseDisjoint : List (Nat × Nat) → Bool
  | [] => true | x :: xs => xs.all (intervalDisjoint x) && intervalsPairwiseDisjoint xs

namespace StdBinaryLayout

/-- Validate the `phnum × 56` B program header table scanned by `static_init_tls`. -/
def checkPhdrTable (L : StdBinaryLayout) : Bool :=
  0 < L.phnum && L.phdrAddr.toNat % 8 == 0 && L.phdrBytes.length == L.phnum * 56 &&
  L.tlsPhdrIdx < L.phnum && L.tlsImageAddr.toNat % 8 == 0 &&
  listReadU32LE L.phdrBytes 0 == 6 && listReadU64LE L.phdrBytes 16 == L.phdrAddr.toNat &&
  (List.range L.phnum).all fun i =>
    let off := i * 56; let ptype := listReadU32LE L.phdrBytes off
    let pvaddr := listReadU64LE L.phdrBytes (off + 16); let pfilesz := listReadU64LE L.phdrBytes (off + 32)
    let pmemsz := listReadU64LE L.phdrBytes (off + 40); let palign := listReadU64LE L.phdrBytes (off + 48)
    ptype != 2 && (if ptype == 6 then pvaddr == L.phdrAddr.toNat else true) &&
    (if ptype == 0x6474e551 then pmemsz == 0 else true) &&
    (if i == L.tlsPhdrIdx then
      ptype == 7 && pvaddr == L.tlsImageAddr.toNat && pfilesz == 0 && pmemsz == 8 && palign == 8
     else ptype != 7)

/-- Executable `Program` extracted from `L.rxSegIdx` of `img` with `Syscall.standard`. -/
def rxProgram (L : StdBinaryLayout) (img : ElfImage) : Program :=
  match img.segments[L.rxSegIdx]? with
  | some rxSeg => { base := rxSeg.start, code := rxSeg.bytes, svc := Syscall.standard }
  | none       => { base := 0#64, code := [], svc := Syscall.standard }

/-- Validate `.rodata` slices, vtable alignments, and `"/dev/null\0"` constants in `roSeg`. -/
def checkRoSegment (L : StdBinaryLayout) (roSeg : Snapshot.Region) (roLen : Nat) : Bool :=
  roSeg.perm == Perm.ro && L.sysconfValuesAddr.toNat % 2 == 0 &&
  L.cleanupVtableAddr.toNat % 8 == 0 && L.stdoutVtableAddr.toNat % 8 == 0 &&
  checkSegSlice roSeg roLen L.emptyCStrAddr [0#8] &&
  checkSegSlice roSeg roLen (L.sysconfValuesAddr + 60#64) [0x04#8, 0xff#8] &&
  checkSegSlice roSeg roLen L.devNullStdAddr devNullBytes &&
  checkSegSlice roSeg roLen L.devNullLibcAddr devNullBytes &&
  checkSegSlice roSeg roLen L.cleanupVtableAddr (vtableBytes L.cleanupVtableShimAddr L.cleanupClosureAddr) &&
  checkSegSlice roSeg roLen L.stdoutVtableAddr (vtableBytes L.stdoutVtableShimAddr L.stdoutCleanupClosureAddr) &&
  L.extraRoSlices.all (fun (a, bs) => checkSegSlice roSeg roLen a bs)

/-- Validate `.init_array`/`.fini_array`/`.got`/`.data`/`.bss` alignments, slices, and disjointness. -/
def checkRwSegment (L : StdBinaryLayout) (rwSeg : Snapshot.Region) (rwLen : Nat) : Bool :=
  rwSeg.perm == Perm.rw && L.builtinTlsAddr.toNat % 8 == 0 && L.mainTlsAddr.toNat % 8 == 0 &&
  L.libcAddr.toNat % 8 == 0 && L.stdoutGlobalAddr.toNat % 8 == 0 && L.stderrFileAddr.toNat % 8 == 0 &&
  L.initArrayAddr.toNat % 8 == 0 && L.finiArrayAddr.toNat % 8 == 0 && L.gotAddr.toNat % 8 == 0 &&
  rwSeg.start.toNat ≤ L.stderrFileAddr.toNat && L.stderrFileAddr.toNat + 0xe8 ≤ rwSeg.start.toNat + rwLen &&
  L.allRwAtoms.all (fun x => x.addr.toNat % x.align == 0 && checkSegSlice rwSeg rwLen x.addr x.rawBytes) &&
  L.nonStderrAtoms.all (fun x =>
    intervalDisjoint (L.stderrFileAddr.toNat, 0xe8) (x.addr.toNat, x.rawBytes.length)) &&
  intervalsPairwiseDisjoint (L.allRwAtoms.map fun x => (x.addr.toNat, x.rawBytes.length))

/-- Kernel-decidable validator checking that `img` conforms to `L` across all segments,
    alignment constraints, PHDR entries, `.rodata` slices, and disjoint `.data`/`.got`/`.bss` globals. -/
def MatchesImage (L : StdBinaryLayout) (img : ElfImage) : Bool :=
  fastWellFormed img && img.entry == L.startAddr && img.phdrVaddr == L.phdrAddr &&
  img.phnum == L.phnum && img.brkStart == L.brkStart &&
  (0x10000 ≤ L.brkStart.toNat && L.brkStart.toNat ≤ 2 ^ 30) &&
  match img.segments[L.phdrSegIdx]?, img.segments[L.rxSegIdx]?,
        img.segments[L.roSegIdx]?, img.segments[L.rwSegIdx]? with
  | some phdrSeg, some rxSeg, some roSeg, some rwSeg =>
    withForcedNat (fastLen512 4096 phdrSeg.bytes) fun phdrLen =>
    withForcedNat (fastLen512 4096 rxSeg.bytes) fun rxLen =>
    withForcedNat (fastLen512 4096 roSeg.bytes) fun roLen =>
    withForcedNat (fastLen512 4096 rwSeg.bytes) fun rwLen =>
      phdrSeg.perm == Perm.ro && rxSeg.perm == Perm.rx &&
      L.codeAddrs.all (fun a => a.toNat % 4 == 0 &&
        rxSeg.start.toNat ≤ a.toNat && a.toNat + 4 ≤ rxSeg.start.toNat + rxLen) &&
      L.checkPhdrTable && checkSegSlice phdrSeg phdrLen L.phdrAddr L.phdrBytes &&
      L.checkRoSegment roSeg roLen && L.checkRwSegment rwSeg rwLen
  | _, _, _, _ => false

@[simp] theorem rxProgram_svc (L : StdBinaryLayout) (img : ElfImage) :
    (L.rxProgram img).svc = Syscall.standard := by unfold rxProgram; split <;> rfl
@[simp] theorem rxProgram_externAt? (L : StdBinaryLayout) (img : ElfImage) :
    (L.rxProgram img).externAt? = fun _ => none := by unfold rxProgram; split <;> rfl

end StdBinaryLayout

/-! ## Segment Extraction and `SupportedOn` Global Ownership Theorems -/

theorem rwAtomListSep_cons (x : RwAtom) : (xs : List RwAtom) →
    rwAtomListSep (x :: xs) = x.toSepProp ∗ rwAtomListSep xs
  | [] => (sepConj_emp _).symm | _ :: _ => rfl
theorem rwAtomListSep_append (xs ys : List RwAtom) :
    rwAtomListSep (xs ++ ys) = rwAtomListSep xs ∗ rwAtomListSep ys := by
  induction xs with
  | nil => simp [rwAtomListSep, emp_sepConj]
  | cons x xs ih => rw [List.cons_append, rwAtomListSep_cons, rwAtomListSep_cons, ih, sepConj_assoc]
theorem roSliceListSep_cons (a : BitVec 64) (bs : List (BitVec 8)) :
    (xs : List (BitVec 64 × List (BitVec 8))) → roSliceListSep ((a, bs) :: xs) = (a ↦ᵣ bs) ∗ roSliceListSep xs
  | [] => (sepConj_emp _).symm | _ :: _ => rfl
theorem StdBinaryLayout.allRwAtoms_sep_eq (L : StdBinaryLayout) :
    rwAtomListSep L.allRwAtoms = StdInitGlobals L ∗ StdExtraRw L := by
  simp only [StdBinaryLayout.allRwAtoms, StdBinaryLayout.stdRwAtoms, StdInitGlobals,
    StdInitFiniGlobals, StdGotGlobals, StdDataGlobals, StdStderrFile, StdLibcGlobals,
    StdTlsGlobals, StdBssGlobals, StdExtraRw, rwAtomListSep_append, sepConj_assoc]
theorem RwAtom.toSepProp_eq_pointsToBytes : (x : RwAtom) → x.toSepProp = (x.addr ↦ₛ x.rawBytes)
  | .u8 a v => (pointsToBytes_singleton a v).symm | .u32 a v => pointsTo32_eq_pointsToBytes a v
  | .u64 a v => pointsTo64_eq_pointsToBytes a v | .bytes _ _ => rfl

private theorem regionAlignedValid_bounds {r : Snapshot.Region} (hv : regionAlignedValid r = true) :
    Obj.pageSize ≤ r.start.toNat ∧ r.start.toNat % Obj.pageSize = 0 ∧
      0 < r.bytes.length ∧ r.start.toNat + r.bytes.length ≤ 2 ^ 48 := by
  unfold regionAlignedValid at hv; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
  exact ⟨hv.1.1.1.1.1.1, hv.1.1.1.1.1.2, hv.1.1.1.1.2, hv.1.1.2⟩

private theorem regionAlignedValid_of_disjoint {regions : List Snapshot.Region}
    (hd : regionsDisjointAndAligned regions = true) {r : Snapshot.Region} (hr : r ∈ regions) :
    regionAlignedValid r = true := by
  match regions with
  | [] => nomatch hr | [_] => rw [List.mem_singleton.mp hr]; exact hd
  | r1 :: r2 :: rest =>
    simp only [regionsDisjointAndAligned, Bool.and_eq_true] at hd
    rcases List.mem_cons.mp hr with rfl | hr'; · exact hd.1.1
    exact regionAlignedValid_of_disjoint hd.2 hr'

private theorem start_lt_tail_of_disjoint {r1 : Snapshot.Region} {tail : List Snapshot.Region}
    (hd : regionsDisjointAndAligned (r1 :: tail) = true) {q : Snapshot.Region} (hq : q ∈ tail) :
    r1.start.toNat + r1.bytes.length ≤ q.start.toNat := by
  match tail with
  | [] => nomatch hq
  | r2 :: rest =>
    simp only [regionsDisjointAndAligned, Bool.and_eq_true, decide_eq_true_eq] at hd
    rcases List.mem_cons.mp hq with rfl | hq'; · exact hd.1.2
    have ⟨_, _, hpos, _⟩ := regionAlignedValid_bounds (regionAlignedValid_of_disjoint hd.2 (List.mem_cons.mpr (Or.inl rfl)))
    have ih := start_lt_tail_of_disjoint hd.2 hq'; omega

private theorem take_below_of_disjoint {regions : List Snapshot.Region}
    (hd : regionsDisjointAndAligned regions = true) (k : Nat) (hk : k < regions.length) :
    (regions.take k).all (Snapshot.Below regions[k].start) = true := by
  induction k generalizing regions with
  | zero => rfl
  | succ k ih =>
    match regions with
    | [] => nomatch hk | [_] => simp at hk
    | r1 :: r2 :: rest =>
      simp only [regionsDisjointAndAligned, Bool.and_eq_true] at hd
      have hk' : k < (r2 :: rest).length := Nat.lt_of_succ_lt_succ hk
      have hhead : Snapshot.Below (r2 :: rest)[k].start r1 = true := by
        simp only [Snapshot.Below, decide_eq_true_eq]
        exact start_lt_tail_of_disjoint (by simp only [regionsDisjointAndAligned, Bool.and_eq_true]; exact hd) (List.getElem_mem hk')
      simp only [List.take_succ_cons, List.getElem_cons_succ, List.all_cons, hhead, Bool.true_and]
      exact ih hd.2 hk'

theorem holdsBytes_of_checkSegSlice {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    {idx : Nat} {seg : Snapshot.Region} {addr : BitVec 64} {bs : List (BitVec 8)}
    (hwf : img.WellFormed = true) (hload : img.loadState inputs = .ok s0)
    (hseg : img.segments[idx]? = some seg)
    (hslice : checkSegSlice seg seg.bytes.length addr bs = true) :
    Obj.HoldsBytes s0.mem addr bs (fun _ => seg.perm.rwx) ∧
      Obj.pageSize ≤ addr.toNat ∧ addr.toNat + bs.length ≤ 2 ^ 48 := by
  obtain ⟨hidx, rfl⟩ := List.getElem?_eq_some_iff.mp hseg
  have hd : regionsDisjointAndAligned img.segments = true := by
    unfold ElfImage.WellFormed at hwf; simp only [Bool.and_eq_true] at hwf; exact hwf.1.1.1.2
  have ⟨hlo_seg, _, _, hhi_seg⟩ :=
    regionAlignedValid_bounds (regionAlignedValid_of_disjoint hd (List.getElem_mem hidx))
  unfold checkSegSlice at hslice; rw [fastTake_eq_take, fastDrop_eq_drop] at hslice
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hslice
  obtain ⟨⟨hlo, hhi⟩, hbs⟩ := hslice
  have hhb := ElfImage.holdsBytes_of_segment_slice img hload idx hidx
    (take_below_of_disjoint hd idx hidx) (by omega) (addr.toNat - img.segments[idx].start.toNat) bs hbs
  have haddr : img.segments[idx].start +
      BitVec.ofNat 64 (addr.toNat - img.segments[idx].start.toNat) = addr := by bv_omega
  rw [haddr] at hhb; exact ⟨hhb, by omega, by omega⟩

theorem pointsToBytesRO_vtableBytes (addr shimAddr closureAddr : BitVec 64) :
    (addr ↦ᵣ vtableBytes shimAddr closureAddr) = StdVtableRo addr shimAddr closureAddr := by
  unfold vtableBytes StdVtableRo
  simp only [List.append_assoc, pointsToBytesRO_append, unpack64_length, ← pointsTo64RO_eq_pointsToBytesRO]
  rw [show BitVec.ofNat 64 8 = 0x08#64 from rfl,
      show addr + 0x08#64 + 0x08#64 = addr + 0x10#64 by bv_arith,
      show addr + 0x10#64 + 0x08#64 = addr + 0x18#64 by bv_arith,
      show addr + 0x18#64 + 0x08#64 = addr + 0x20#64 by bv_arith]

private theorem satisfies_ro_of_holdsBytes {m : Memory} {addr : BitVec 64} {bs : List (BitVec 8)}
    {P : SepProp} (hhb : Obj.HoldsBytes m addr bs (fun _ => Perm.ro))
    (hlen : bs.length ≤ 2 ^ 64) (hP : m ⊨ P) : m ⊨ (addr ↦ᵣ bs) ∗ P :=
  Satisfies.rodata_intro (holdsBytes_ro hhb).1 (holdsBytes_ro hhb).2 hlen hP

private theorem satisfies_roSliceList {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    {idx : Nat} {roSeg : Snapshot.Region} {slices : List (BitVec 64 × List (BitVec 8))} {P : SepProp}
    (hwf : img.WellFormed = true) (hload : img.loadState inputs = .ok s0)
    (hseg : img.segments[idx]? = some roSeg) (hperm : roSeg.perm = Perm.ro)
    (hall : slices.all (fun (a, bs) => checkSegSlice roSeg roSeg.bytes.length a bs) = true)
    (hP : s0.mem ⊨ P) : s0.mem ⊨ roSliceListSep slices ∗ P := by
  induction slices with
  | nil => rw [roSliceListSep, emp_sepConj]; exact hP
  | cons hd tl ih =>
    rcases hd with ⟨a, bs⟩; simp only [List.all_cons, Bool.and_eq_true] at hall
    have ⟨hhb, _, hhi⟩ := holdsBytes_of_checkSegSlice hwf hload hseg hall.1
    rw [hperm] at hhb; rw [roSliceListSep_cons, sepConj_assoc]
    exact satisfies_ro_of_holdsBytes hhb (by omega) (ih hall.2)

private theorem supportedOn_emp (b : BitVec 64) (S : Nat → Prop) (m : Memory) :
    SupportedOn b S m emp := by
  have hs := SupportedOn.of_holdsBytes_rw (b := b) (off := 0) (bs := []) (by decide)
    (m := m) (fun _ hi => nomatch hi)
  rw [pointsToBytes_nil] at hs; exact hs.widen (fun _ ⟨_, hk⟩ => nomatch hk)

theorem RwAtom.supportedOn_of_holdsBytes (x : RwAtom) {m : Memory}
    (hbnd : x.addr.toNat + x.rawBytes.length < 2 ^ 64)
    (hhb : Obj.HoldsBytes m x.addr x.rawBytes (fun _ => Perm.rw)) :
    SupportedOn 0#64 (fun k => x.addr.toNat ≤ k ∧ k < x.addr.toNat + x.rawBytes.length) m x.toSepProp := by
  have haddr : (0#64 : BitVec 64) + BitVec.ofNat 64 x.addr.toNat = x.addr := by
    rw [BitVec.zero_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hs := SupportedOn.of_holdsBytes_rw (b := 0#64) (off := x.addr.toNat) (bs := x.rawBytes) hbnd (haddr.symm ▸ hhb)
  rw [haddr, ← x.toSepProp_eq_pointsToBytes] at hs; exact hs

theorem supportedOn_rwAtomList {m : Memory} (atoms : List RwAtom)
    (hhb : ∀ x ∈ atoms, x.addr.toNat + x.rawBytes.length < 2 ^ 64 ∧ Obj.HoldsBytes m x.addr x.rawBytes (fun _ => Perm.rw))
    (hdisj : intervalsPairwiseDisjoint (atoms.map fun x => (x.addr.toNat, x.rawBytes.length)) = true) :
    SupportedOn 0#64 (fun k => ∃ x ∈ atoms, x.addr.toNat ≤ k ∧ k < x.addr.toNat + x.rawBytes.length)
      m (rwAtomListSep atoms) := by
  induction atoms with
  | nil => exact supportedOn_emp 0#64 _ m
  | cons x xs ih =>
    simp only [List.map_cons, intervalsPairwiseDisjoint, Bool.and_eq_true] at hdisj
    have ⟨hx_bnd, hx_hb⟩ := hhb x (List.mem_cons.mpr (Or.inl rfl))
    have hs_xs := ih (fun y hy => hhb y (List.mem_cons.mpr (Or.inr hy))) hdisj.2
    refine (SupportedOn.congr_prop (rwAtomListSep_cons x xs).symm
      (SupportedOn.sepConj (x.supportedOn_of_holdsBytes hx_bnd hx_hb) hs_xs ?_)).widen ?_
    · rintro k ⟨hx1, hx2⟩ ⟨y, hy, hy1, hy2⟩
      have hd := List.all_eq_true.mp hdisj.1 _ (List.mem_map_of_mem hy)
      unfold intervalDisjoint at hd; simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hd; omega
    · rintro k (hk | ⟨y, hy, hk⟩)
      · exact ⟨x, List.mem_cons.mpr (Or.inl rfl), hk⟩
      · exact ⟨y, List.mem_cons.mpr (Or.inr hy), hk⟩

namespace StdBinaryLayout

theorem MatchesImage.segments {L : StdBinaryLayout} {img : ElfImage} (h : L.MatchesImage img = true) :
    img.WellFormed = true ∧ img.entry = L.startAddr ∧ img.phdrVaddr = L.phdrAddr ∧
    img.phnum = L.phnum ∧ img.brkStart = L.brkStart ∧
    (0x10000 ≤ L.brkStart.toNat ∧ L.brkStart.toNat ≤ 2 ^ 30) ∧
    ∃ phdrSeg rxSeg roSeg rwSeg,
      img.segments[L.phdrSegIdx]? = some phdrSeg ∧ img.segments[L.rxSegIdx]? = some rxSeg ∧
      img.segments[L.roSegIdx]? = some roSeg ∧ img.segments[L.rwSegIdx]? = some rwSeg ∧
      phdrSeg.perm = Perm.ro ∧ rxSeg.perm = Perm.rx ∧
      (L.codeAddrs.all fun a => a.toNat % 4 == 0 &&
        rxSeg.start.toNat ≤ a.toNat && a.toNat + 4 ≤ rxSeg.start.toNat + rxSeg.bytes.length) = true ∧
      L.checkPhdrTable = true ∧
      checkSegSlice phdrSeg phdrSeg.bytes.length L.phdrAddr L.phdrBytes = true ∧
      L.checkRoSegment roSeg roSeg.bytes.length = true ∧
      L.checkRwSegment rwSeg rwSeg.bytes.length = true := by
  unfold MatchesImage at h; rw [fastWellFormed_eq] at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hwf, hent⟩, hphv⟩, hphn⟩, hbrk⟩, hbrkle⟩, hm⟩ := h
  refine ⟨hwf, hent, hphv, hphn, hbrk, hbrkle, ?_⟩
  split at hm <;> try contradiction
  rename_i phdrSeg rxSeg roSeg rwSeg h0 h1 h2 h3
  simp only [withForcedNat_eq, fastLen512_eq_length, Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨hp0, hp1⟩, hcode⟩, hphdrT⟩, hphdrS⟩, hro⟩, hrw⟩ := hm
  exact ⟨phdrSeg, rxSeg, roSeg, rwSeg, h0, h1, h2, h3, hp0, hp1, hcode, hphdrT, hphdrS, hro, hrw⟩

theorem MatchesImage.wellFormed {L : StdBinaryLayout} {img : ElfImage} (h : L.MatchesImage img = true) :
    img.WellFormed = true := (MatchesImage.segments h).1
theorem MatchesImage.entry_eq {L : StdBinaryLayout} {img : ElfImage} (h : L.MatchesImage img = true) :
    img.entry = L.startAddr := (MatchesImage.segments h).2.1
theorem MatchesImage.phdrVaddr_eq {L : StdBinaryLayout} {img : ElfImage} (h : L.MatchesImage img = true) :
    img.phdrVaddr = L.phdrAddr := (MatchesImage.segments h).2.2.1
theorem MatchesImage.phnum_eq {L : StdBinaryLayout} {img : ElfImage} (h : L.MatchesImage img = true) :
    img.phnum = L.phnum := (MatchesImage.segments h).2.2.2.1
theorem MatchesImage.brkStart_eq {L : StdBinaryLayout} {img : ElfImage} (h : L.MatchesImage img = true) :
    img.brkStart = L.brkStart := (MatchesImage.segments h).2.2.2.2.1
theorem MatchesImage.brkStart_ge_mmapMin {L : StdBinaryLayout} {img : ElfImage} (h : L.MatchesImage img = true) :
    0x10000 ≤ L.brkStart.toNat := (MatchesImage.segments h).2.2.2.2.2.1.1
theorem MatchesImage.brkStart_le_gib {L : StdBinaryLayout} {img : ElfImage} (h : L.MatchesImage img = true) :
    L.brkStart.toNat ≤ 2 ^ 30 := (MatchesImage.segments h).2.2.2.2.2.1.2
theorem MatchesImage.brkStart_le {L : StdBinaryLayout} {img : ElfImage} (h : L.MatchesImage img = true) :
    L.brkStart.toNat ≤ STACK_BASE_MIN := by have := MatchesImage.brkStart_le_gib h; unfold STACK_BASE_MIN; omega
theorem MatchesImage.segments_below_brkStart {L : StdBinaryLayout} {img : ElfImage} (h : L.MatchesImage img = true) :
    img.segments.all (Snapshot.Below L.brkStart) = true := by
  have hwf := MatchesImage.wellFormed h; unfold ElfImage.WellFormed at hwf
  simp only [Bool.and_eq_true] at hwf; rw [← MatchesImage.brkStart_eq h]; exact hwf.2

theorem MatchesImage.codeLoaded {L : StdBinaryLayout} {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (h : L.MatchesImage img = true) (hload : img.loadState inputs = .ok s0) :
    (L.rxProgram img).CodeLoaded s0.mem := by
  obtain ⟨hwf, _, _, _, _, _, _, rxSeg, _, _, _, hrx, _, _, _, hperm, _⟩ := MatchesImage.segments h
  unfold rxProgram; rw [hrx]; dsimp only []; obtain ⟨hidx, rfl⟩ := List.getElem?_eq_some_iff.mp hrx
  have hd : regionsDisjointAndAligned img.segments = true := by
    unfold ElfImage.WellFormed at hwf; simp only [Bool.and_eq_true] at hwf; exact hwf.1.1.1.2
  have ⟨_, hal, _, hhi⟩ := regionAlignedValid_bounds (regionAlignedValid_of_disjoint hd (List.getElem_mem hidx))
  have hhb := ElfImage.holdsBytes_of_segment_slice img hload L.rxSegIdx hidx
    (take_below_of_disjoint hd L.rxSegIdx hidx) (by omega) 0 img.segments[L.rxSegIdx].bytes
    (by rw [List.drop_zero, List.take_length])
  rw [BitVec.add_zero, hperm] at hhb
  exact Program.CodeLoaded.intro (by dsimp only []; unfold Obj.pageSize at hal; omega) (by dsimp only []; omega) hhb

theorem MatchesImage.holdsBytes_ro_slice {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State} {seg : Snapshot.Region} {addr : BitVec 64} {bs : List (BitVec 8)}
    (h : L.MatchesImage img = true) (hload : img.loadState inputs = .ok s0)
    (hseg : img.segments[L.roSegIdx]? = some seg ∨ img.segments[L.phdrSegIdx]? = some seg)
    (hslice : checkSegSlice seg seg.bytes.length addr bs = true) :
    Obj.HoldsBytes s0.mem addr bs (fun _ => Perm.ro) ∧ Obj.pageSize ≤ addr.toNat ∧ addr.toNat + bs.length ≤ 2 ^ 48 := by
  obtain ⟨hwf, _, _, _, _, _, phdrSeg, _, roSeg, _, hph, _, hro, _, hp0, _, _, _, _, hroC, _⟩ := MatchesImage.segments h
  rcases hseg with hs | hs
  · cases hro.symm.trans hs; unfold checkRoSegment at hroC; simp only [Bool.and_eq_true, beq_iff_eq] at hroC
    have hres := holdsBytes_of_checkSegSlice hwf hload hs hslice
    rw [hroC.1.1.1.1.1.1.1.1.1.1] at hres; exact hres
  · cases hph.symm.trans hs
    have hres := holdsBytes_of_checkSegSlice hwf hload hs hslice
    rw [hp0] at hres; exact hres

theorem MatchesImage.satisfies_roConstants {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State} {P : SepProp}
    (h : L.MatchesImage img = true) (hload : img.loadState inputs = .ok s0) (hP : s0.mem ⊨ P) :
    s0.mem ⊨ StdRoConstants L ∗ StdExtraRo L ∗ P := by
  obtain ⟨hwf, _, _, _, _, _, phdrSeg, _, roSeg, _, hph, _, hro, _, hp0, _, _, _, hphS, hroC, _⟩ := MatchesImage.segments h
  unfold checkRoSegment at hroC; simp only [Bool.and_eq_true, beq_iff_eq] at hroC
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpro, _⟩, _⟩, _⟩, hempS⟩, hsysS⟩, hdn1S⟩, hdn2S⟩, hcvS⟩, hsvS⟩, hexS⟩ := hroC
  have addRo {addr bs Q} (hs : checkSegSlice roSeg roSeg.bytes.length addr bs = true) (hQ : s0.mem ⊨ Q) :
      s0.mem ⊨ (addr ↦ᵣ bs) ∗ Q := by
    have ⟨hb, _, hi⟩ := holdsBytes_of_checkSegSlice hwf hload hro hs; rw [hpro] at hb
    exact satisfies_ro_of_holdsBytes hb (by omega) hQ
  have h1 := addRo hsvS (satisfies_roSliceList hwf hload hro hpro hexS hP); rw [pointsToBytesRO_vtableBytes] at h1
  have h2 := addRo hcvS h1; rw [pointsToBytesRO_vtableBytes] at h2
  have h5 := addRo hsysS (addRo hdn1S (addRo hdn2S h2))
  rw [pointsToBytesRO2_eq_pointsTo16RO] at h5; change s0.mem ⊨ ((L.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ _ at h5
  have h6 := addRo hempS h5; rw [pointsToBytesRO_singleton] at h6
  have ⟨hb_ph, _, hi_ph⟩ := holdsBytes_of_checkSegSlice hwf hload hph hphS; rw [hp0] at hb_ph
  simpa only [StdRoConstants, StdExtraRo, sepConj_assoc] using satisfies_ro_of_holdsBytes hb_ph (by omega) h6

theorem MatchesImage.holdsBytes_rw_slice {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State} {seg : Snapshot.Region} {addr : BitVec 64} {bs : List (BitVec 8)}
    (h : L.MatchesImage img = true) (hload : img.loadState inputs = .ok s0)
    (hseg : img.segments[L.rwSegIdx]? = some seg) (hslice : checkSegSlice seg seg.bytes.length addr bs = true) :
    Obj.HoldsBytes s0.mem addr bs (fun _ => Perm.rw) ∧ Obj.pageSize ≤ addr.toNat ∧ addr.toNat + bs.length ≤ 2 ^ 48 := by
  obtain ⟨hwf, _, _, _, _, _, _, _, _, rwSeg, _, _, _, hrw, _, _, _, _, _, _, hrwC⟩ := MatchesImage.segments h
  cases hrw.symm.trans hseg; unfold checkRwSegment at hrwC; simp only [Bool.and_eq_true, beq_iff_eq] at hrwC
  have hres := holdsBytes_of_checkSegSlice hwf hload hseg hslice
  rw [hrwC.1.1.1.1.1.1.1.1.1.1.1.1.1] at hres; exact hres

theorem MatchesImage.supportedOn_initGlobals {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State} {rwSeg : Snapshot.Region}
    (h : L.MatchesImage img = true) (hload : img.loadState inputs = .ok s0) (hrw : img.segments[L.rwSegIdx]? = some rwSeg) :
    SupportedOn 0#64 (fun k => rwSeg.start.toNat ≤ k ∧ k < rwSeg.start.toNat + rwSeg.bytes.length)
      s0.mem (StdInitGlobals L ∗ StdExtraRw L) := by
  obtain ⟨hwf, _, _, _, _, _, _, _, _, rwSeg', _, _, _, hrw', _, _, _, _, _, _, hrwC⟩ := MatchesImage.segments h
  cases hrw'.symm.trans hrw; unfold checkRwSegment at hrwC; simp only [Bool.and_eq_true, beq_iff_eq] at hrwC
  have hs := supportedOn_rwAtomList L.allRwAtoms (fun x hx => by
    have hxC := List.all_eq_true.mp hrwC.1.1.2 x hx; simp only [Bool.and_eq_true] at hxC
    have ⟨hhb, _, hhi⟩ := holdsBytes_of_checkSegSlice hwf hload hrw hxC.2
    rw [hrwC.1.1.1.1.1.1.1.1.1.1.1.1.1] at hhb; exact ⟨by omega, hhb⟩) hrwC.2
  refine (SupportedOn.congr_prop L.allRwAtoms_sep_eq hs).widen fun k ⟨x, hx, hk1, hk2⟩ => ?_
  have hxC := List.all_eq_true.mp hrwC.1.1.2 x hx; simp only [Bool.and_eq_true] at hxC
  have hb := hxC.2; unfold checkSegSlice at hb; simp only [Bool.and_eq_true, decide_eq_true_eq] at hb; omega

theorem MatchesImage.supportedOn_initGlobals_below_brk {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State} (h : L.MatchesImage img = true) (hload : img.loadState inputs = .ok s0) :
    SupportedOn 0#64 (fun k => 0 ≤ k ∧ k < L.brkStart.toNat) s0.mem (StdInitGlobals L ∗ StdExtraRw L) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, rwSeg, _, _, _, hrw, _⟩ := MatchesImage.segments h
  have hbel := List.all_eq_true.mp (MatchesImage.segments_below_brkStart h) rwSeg (List.mem_of_getElem? hrw)
  simp only [Snapshot.Below, decide_eq_true_eq] at hbel
  exact (MatchesImage.supportedOn_initGlobals h hload hrw).widen (fun _ ⟨_, hk⟩ => by omega)

end StdBinaryLayout
end ProofLib.StdStartup
