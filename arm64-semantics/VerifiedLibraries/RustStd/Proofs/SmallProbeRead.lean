/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Generated.RustStdIoPlacedObj
public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.VecBridge
public import VerifiedLibraries.RustStd.Proofs.ExecSeg
public import VerifiedLibraries.RustStd.Proofs.CoreIo
public import ProofLib.GenPlacedFetches
public meta import ProofLib.ProgramReflection

/-!
# Placement-Generic `small_probe_read::<File>`

Proves `rustSmallProbeRead_ok` for `std::io::default_read_to_end::small_probe_read::<File>`
(block `13` of `rustStdIoMultiLib`), covering fast EOF, fast in-place `memcpy` into spare capacity,
and slow `RawVecInner::do_reserve_and_handle` growth or `.OutOfMemory`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.literalFetch false

namespace VerifiedLibraries.RustStd.Io

open Arm64 Arm64.Obj Arm64.Process ProofLib VerifiedLibraries.Musl
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup

/-! ## Symbols, `Vec<u8>` Representation, and `do_reserve_and_handle` Contract -/

abbrev smallProbeReadFileSym : String :=
  "std::io::default_read_to_end::small_probe_read::<std::fs::File> [rust_std_io]"

abbrev doReserveAndHandleIoSym : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [rust_std_io]"

/-- Default stack budget below `sp` at entry to `do_reserve_and_handle`
    (`64` B `do_reserve_and_handle` + `48` B `finish_grow` + `4096` B `Rust.hookStack`). -/
abbrev defaultReserveStack : Nat := 4208

/-- Amortized capacity computed by `RawVecInner::do_reserve_and_handle` for `elem_size = 1`:
    `max (max (len + additional) (2 * cap)) 8` (`min_non_zero_cap(1) = 8`). -/
def rustVecGrowCap (cap len additional : Nat) : Nat :=
  max (max (len + additional) (2 * cap)) 8

/-- Updated budget units `lb'` after `RawVecInner::do_reserve_and_handle` grows a `u8` buffer
    from `cap` to `growCap` (`alloc` when `cap = 0`, `realloc` when `0 < cap`, matching
    `AllocSeqFits` in `VerifiedLibraries.RustStd.Spec.Alloc`). -/
def rustVecGrowLb {oom : State → State → Prop} (A : RustStdAlloc oom)
    (lb cap growCap : Nat) : Nat :=
  if cap = 0 then lb + A.cost growCap 1
  else lb + A.cost growCap 1 - A.cost cap 1

/-- Updated live-block count `lk'` after `RawVecInner::do_reserve_and_handle` grows a `u8` buffer
    from `cap` to `growCap`. -/
def rustVecGrowLk (lk cap : Nat) : Nat :=
  if cap = 0 then lk + 1 else lk

/-- Heap backing buffer of a `Vec<u8>` at `ptr` with capacity `cap` and initialized prefix `bs`
    over `RustStdAlloc oom` (`align = 1`). When `cap = 0`, owns `emp` with non-null dangling `ptr`. -/
def rustStdVecBuf {oom : State → State → Prop} (A : RustStdAlloc oom)
    (cap : Nat) (ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap ∧ cap < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap - bs.length))

/-- A `Vec<u8>` at `v` over `RustStdAlloc oom` with initialized contents `bs` and capacity `cap`. -/
def rustStdVecU8At {oom : State → State → Prop} (A : RustStdAlloc oom)
    (v : BitVec 64) (bs : List (BitVec 8)) (cap : Nat) : SepProp :=
  ∃∗ ptr : BitVec 64,
    vecHeader v (BitVec.ofNat 64 cap) ptr (BitVec.ofNat 64 bs.length) ∗
      rustStdVecBuf A cap ptr bs

theorem rustStdVecU8At_eq_ioResultVecOk {oom : State → State → Prop} (A : RustStdAlloc oom)
    (v : BitVec 64) (bs : List (BitVec 8)) (cap : Nat) (hcap : cap < 2 ^ 63) :
    rustStdVecU8At A v bs cap =
      (∃∗ ptr : BitVec 64, ioResultVecOk A v (BitVec.ofNat 64 cap) ptr bs) := by
  have htoNat : (BitVec.ofNat 64 cap).toNat = cap := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cap < 2 ^ 64)]
  have hzero : (BitVec.ofNat 64 cap = 0#64) ↔ cap = 0 := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simpa [htoNat] using this
    · rintro rfl; rfl
  simp only [rustStdVecU8At, ioResultVecOk, rustStdVecBuf, ioVecBuf, htoNat, hzero]

/-- Rest of `StdErrCells addrs tp` after splitting off `StdErrnoCell tp`. -/
abbrev StdOsErrCells (addrs : RustStdIoAddrs) : SepProp :=
  (∃∗ f : BitVec 64, addrs.osFunctions ↦₆₄ f) ∗
    ((addrs.errorFunctions + 16#64) ↦₆₄ᵣ addrs.isInterrupted)

theorem stdErrCells_eq (addrs : RustStdIoAddrs) (tp : BitVec 64) :
    StdErrCells addrs tp = (StdErrnoCell tp ∗ StdOsErrCells addrs) := rfl

/-- Ok-or-OOM contract for `RawVecInner::do_reserve_and_handle(vecPtr, len, additional, 1, 1)`
    (`doReserveAndHandleIoSym`, `elem_align = 1`, `elem_size = 1`), generic in `oom` and `A`.
    Ghost: `(vecPtr, ptr, cap, bs, additional, lb, lk)`. -/
def rustDoReserveAndHandleSpec {oom : State → State → Prop} (A : RustStdAlloc oom)
    (reserveStack : Nat := defaultReserveStack) :
    Spec (BitVec 64 × BitVec 64 × Nat × List (BitVec 8) × Nat × Nat × Nat) where
  pre := fun (vecPtr, ptr, cap, bs, additional, lb, lk) s0 =>
    let growCap := rustVecGrowCap cap bs.length additional
    ⌜s0.readReg64 .x0 = vecPtr ∧
      s0.readReg64 .x1 = BitVec.ofNat 64 bs.length ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 additional ∧
      s0.readReg64 .x3 = 1#64 ∧
      s0.readReg64 .x4 = 1#64 ∧
      cap - bs.length < additional ∧
      ¬ NullAllowed growCap 1 ∧
      A.CanAlloc lb lk growCap 1⌝ ∗
    (stackAt s0.sp reserveStack ∗
      (vecPtr ↦₆₄ BitVec.ofNat 64 cap) ∗ ((vecPtr + 8#64) ↦₆₄ ptr) ∗
      rustStdVecBuf A cap ptr bs ∗
      A.pool lb lk s0 ∗
      StdErrnoCell s0.tpidrEl0)
  post := fun (vecPtr, _, cap, bs, additional, lb, lk) s0 sf =>
    let growCap := rustVecGrowCap cap bs.length additional
    ∃∗ newPtr : BitVec 64,
      ⌜AllocCallPreserved s0 sf⌝ ∗
      (stackAt s0.sp reserveStack ∗
        (vecPtr ↦₆₄ BitVec.ofNat 64 growCap) ∗ ((vecPtr + 8#64) ↦₆₄ newPtr) ∗
        rustStdVecBuf A growCap newPtr bs ∗
        A.pool (rustVecGrowLb A lb cap growCap) (rustVecGrowLk lk cap) sf ∗
        StdErrnoCell s0.tpidrEl0)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ s0 sf => ⌜∃ sm, IoFrame s0 sm ∧ sm.fs = s0.fs ∧ oom sm sf⌝

/-- Ok-or-OOM contract for `std::io::default_read_to_end::small_probe_read::<std::fs::File>`
    (block `13` of `rustStdIoMultiLib`, `smallProbeReadFileSym`, `376` B), generic in `oom` and `A`.
    Covers both `chunk.length ≤ cap - bs.length` (fast EOF and fast `memcpy`) and
    `cap - bs.length < chunk.length` (slow `do_reserve_and_handle` growth or `.OutOfMemory`).
    Ghost: `(vecPtr, cap, bs, desc, lb, lk)`. -/
def rustSmallProbeReadSpec {oom : State → State → Prop} (A : RustStdAlloc oom)
    (fd : BitVec 64 := 3#64) (reserveStack : Nat := defaultReserveStack) :
    Spec (BitVec 64 × Nat × List (BitVec 8) × FdEntry × Nat × Nat) where
  pre := fun (vecPtr, cap, bs, desc, lb, lk) s0 =>
    let chunk := ((s0.fs.fdBytes desc).drop desc.offset).take 32
    let growCap := rustVecGrowCap cap bs.length chunk.length
    ⌜s0.readReg32 .x0 = fd.truncate 32 ∧
      s0.readReg64 .x1 = vecPtr ∧
      s0.fs.fds fd = some desc ∧
      3 ≤ fd.toNat ∧ fd.toNat < 2 ^ 31 ∧
      desc.kind = .localFile ∧ desc.accMode.canRead = true ∧
      144 + reserveStack ≤ s0.sp.toNat ∧ s0.sp.toNat ≤ Arm64.USER_VA_LIMIT ∧
      desc.offset + 32 ≤ Arm64.MAX_LFS_FILESIZE ∧
      (cap - bs.length < chunk.length →
        ¬ NullAllowed growCap 1 ∧ A.CanAlloc lb lk growCap 1)⌝ ∗
    (stackAt s0.sp (144 + reserveStack) ∗
      rustStdVecU8At A vecPtr bs cap ∗
      A.pool lb lk s0 ∗
      StdErrnoCell s0.tpidrEl0)
  post := fun (vecPtr, cap, bs, desc, lb, lk) s0 sf =>
    let chunk := ((s0.fs.fdBytes desc).drop desc.offset).take 32
    let grew := decide (cap - bs.length < chunk.length)
    let growCap := rustVecGrowCap cap bs.length chunk.length
    let cap' := if grew then growCap else cap
    let lb' := if grew then rustVecGrowLb A lb cap growCap else lb
    let lk' := if grew then rustVecGrowLk lk cap else lk
    ⌜sf.readReg64 .x0 = 0#64 ∧
      sf.readReg64 .x1 = BitVec.ofNat 64 chunk.length ∧
      sf.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }) ∧
      IoFrame s0 sf ∧
      sf.tpidrEl0 = s0.tpidrEl0 ∧
      sf.brkStart = s0.brkStart ∧
      (grew = false → SyscallPreserved s0 sf)⌝ ∗
    (stackAt s0.sp (144 + reserveStack) ∗
      rustStdVecU8At A vecPtr (bs ++ chunk) cap' ∗
      A.pool lb' lk' sf ∗
      StdErrnoCell s0.tpidrEl0)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun (_, cap, bs, desc, _, _) s0 sf =>
    let chunk := ((s0.fs.fdBytes desc).drop desc.offset).take 32
    ⌜cap - bs.length < chunk.length ∧
      ∃ sm, IoFrame s0 sm ∧
        sm.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }) ∧
        oom sm sf⌝

/-! ## Block `13` Fetch and `no-svc0` Generation -/

private class SmallProbeReadPlacement where
  mpl : MultiPlacement
  placeable : rustStdIoMultiLib.Placeable mpl

private def sprLib13 : PlacedLib := rustStdIoMultiLib.blockLib 13
private def sprPl13 [SmallProbeReadPlacement] : Placement :=
  rustStdIoMultiLib.blockPlacement SmallProbeReadPlacement.mpl 13
private theorem sprPlaceable13 [SmallProbeReadPlacement] : sprLib13.Placeable sprPl13 :=
  rustStdIoMultiLib.placeable_blockLib (by decide) SmallProbeReadPlacement.placeable
private def sprPC13 [SmallProbeReadPlacement] : Program := sprLib13.program sprPl13

private def sprProg13 : Program :=
  { code := (rustStdIoMultiLib.blockLib 13).text.code
    symbols := (rustStdIoMultiLib.blockLib 13).text.symbols }
private def sprTree13 : WordTree := word_tree_of% sprProg13
private theorem spr13_code_eq : sprLib13.text.code = sprTree13.toBytes := by rfl_kernel
private theorem spr13_tree_size : sprTree13.checkSize? = some 94 := by rfl_kernel
private def sprSymChars13 : List (List Char × Nat) := sym_chars_of% sprProg13
private theorem spr13_symbols_eq : sprLib13.text.symbols = toStringSymbols sprSymChars13 := by
  rfl_kernel
private theorem spr13_symbols_fresh : allFreshCharSymbols sprSymChars13 = true := by rfl_kernel

gen_placed_fetches sprPC13 sprLib13 sprTree13 spr13_code_eq spr13_tree_size
  via_placement sprPl13 sprPlaceable13 [0x0 → 0xac, 0x140 → 0x15c]
gen_placed_fnOffs sprPC13 sprLib13 sprSymChars13 spr13_symbols_eq spr13_symbols_fresh

theorem rustIoBlockNoSvc0_13 : checkBlockNoSvc0 (rustStdIoMultiLib.blockLib 13).text = true := by
  decide

/-! ## Proof of `rustSmallProbeRead_ok` -/

section
arm64_proof_prelude

private theorem poolPreserved_of_syscall {s s' : State} (h : SyscallPreserved s s') :
    PoolPreserved s s' :=
  ⟨h.2.2.brkStart_eq, h.2.2.brk_eq, h.1⟩

private theorem rustVecGrowCap_ge (cap len additional : Nat) :
    len + additional ≤ rustVecGrowCap cap len additional := by
  unfold rustVecGrowCap; omega

private theorem satisfies_rustStdVecBuf_bounds {oom : State → State → Prop} {A : RustStdAlloc oom}
    {m : Memory} {cap : Nat} {ptr : BitVec 64} {bs : List (BitVec 8)} {R : SepProp}
    (h : m ⊨ rustStdVecBuf A cap ptr bs ∗ R) :
    bs.length ≤ cap ∧ cap < 2 ^ 63 ∧ ptr ≠ 0#64 := by
  unfold rustStdVecBuf at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.1

private theorem rustPointsTo64_sp144_zero (sp : BitVec 64) :
    (((sp - 144#64) ↦₆₄ 0#64) ∗ ((sp - 136#64) ↦₆₄ 0#64) ∗
      ((sp - 128#64) ↦₆₄ 0#64) ∗ ((sp - 120#64) ↦₆₄ 0#64)) =
      ((sp - 144#64) ↦ₛ List.replicate 32 0#8) := by
  have h32 : List.replicate 32 0#8 =
      (unpack64 0#64 ++ unpack64 0#64) ++ (unpack64 0#64 ++ unpack64 0#64) := by decide
  rw [h32, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [List.length_append, unpack64_length, Nat.reduceAdd,
    ← pointsTo64_eq_pointsToBytes, bv_lin_norm, sepConj_assoc]

private theorem rustExists_sp144_quad (sp : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64, ((sp - 144#64) ↦ₛ bs) =
      (((sp - 144#64) ↦₆₄ w0) ∗ ((sp - 136#64) ↦₆₄ w1) ∗
        ((sp - 128#64) ↦₆₄ w2) ∗ ((sp - 120#64) ↦₆₄ w3)) := by
  obtain ⟨w0, w1, w2, w3, _, hq⟩ := exists_unpack64_of_length_32 h
  exact ⟨w0, w1, w2, w3, by simpa only [bv_lin_norm, sepConj_assoc] using hq (sp - 144#64)⟩

private abbrev rustSprSavedSlots (s0 : State) (st4 st5 : BitVec 64) : SepProp :=
  ((s0.sp - 112#64) ↦₆₄ st4) ∗ ((s0.sp - 104#64) ↦₆₄ st5) ∗
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

private theorem sprRead_pc [SmallProbeReadPlacement] :
    sprPl13.base + 56#64 + (sprPl13.ρ "read" - sprPl13.base - 56#64) =
      rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl "read" := by
  change sprPl13.base + 56#64 +
    (rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl "read" - sprPl13.base - 56#64) =
    rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl "read"
  bv_lin

private theorem sprMemcpy_pc [SmallProbeReadPlacement] :
    sprPl13.base + 120#64 + (sprPl13.ρ "memcpy" - sprPl13.base - 120#64) =
      rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl "memcpy" := by
  change sprPl13.base + 120#64 +
    (rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl "memcpy" - sprPl13.base - 120#64) =
    rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl "memcpy"
  bv_lin

private theorem sprReserve_pc [SmallProbeReadPlacement] :
    sprPl13.base + 340#64 + (sprPl13.ρ doReserveAndHandleIoSym - sprPl13.base - 340#64) =
      rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl doReserveAndHandleIoSym := by
  change sprPl13.base + 340#64 +
    (rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl doReserveAndHandleIoSym -
      sprPl13.base - 340#64) =
    rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl doReserveAndHandleIoSym
  bv_lin

private def errnoCell (tp : BitVec 64) : SepProp := StdErrnoCell tp
private theorem errnoCell_eq (tp : BitVec 64) : StdErrnoCell tp = errnoCell tp := rfl

private theorem rustSmallProbeRead_epilogue [SmallProbeReadPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext : ∀ pc, P.externAt? pc = none)
    {s0 s_ep : State} {vecPtr ptr' st4 st5 : BitVec 64}
    {cap' lb' lk' reserveStack : Nat} {bs chunk pbuf : List (BitVec 8)}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hstk_top : 144 + reserveStack ≤ 2 ^ 64)
    (hcl : rustStdIoMultiLib.CodeLoaded SmallProbeReadPlacement.mpl s_ep.mem)
    (hpc : s_ep.pc = sprPl13.base + 124#64)
    (hrun : s_ep.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : s_ep.sp = s0.sp - 144#64)
    (hx19 : s_ep.readReg64 (.gpr 19#5) = vecPtr)
    (hx20 : s_ep.readReg64 (.gpr 20#5) = BitVec.ofNat 64 chunk.length)
    (hx21 : s_ep.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length)
    (hvregs : calleeSavedVRegs s_ep = calleeSavedVRegs s0)
    (hpbuf_len : pbuf.length = 32)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf → SyscallPreserved s_ep sf →
      sf.fs = s_ep.fs → sf.trace = s_ep.trace →
      sf.readReg64 .x0 = 0#64 → sf.readReg64 .x1 = BitVec.ofNat 64 chunk.length →
      post sf (stackAt s0.sp (144 + reserveStack) ∗
        rustStdVecU8At A vecPtr (bs ++ chunk) cap' ∗ A.pool lb' lk' sf ∗
        errnoCell s0.tpidrEl0)) :
    SepWP P (s0.readReg64 .lr) s_ep
      (stackAt (s0.sp - 144#64) reserveStack ∗ ((s0.sp - 144#64) ↦ₛ pbuf) ∗
        rustSprSavedSlots s0 st4 st5 ∗
        (vecPtr ↦₆₄ BitVec.ofNat 64 cap') ∗ ((vecPtr + 8#64) ↦₆₄ ptr') ∗
        ((vecPtr + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        rustStdVecBuf A cap' ptr' (bs ++ chunk) ∗ A.pool lb' lk' s_ep ∗
        errnoCell s0.tpidrEl0)
      post oomProp := by
  obtain ⟨w0, w1, w2, w3, hquad⟩ := rustExists_sp144_quad s0.sp hpbuf_len
  wp_conv_pre => rw [hquad]
  apply sepWP_seg_rebase_pure (lib := rustStdIoMultiLib) (mpl := SmallProbeReadPlacement.mpl)
    hext 13 (by decide) rustIoBlockNoSvc0_13 hcl (mid := s0.readReg64 .lr)
  intro se' hcpu_e; change SepWP (sprPC13.rebase sprPl13.base (fun _ => none)) _ _ _ _
  have hpc_e' : se'.pc = sprPl13.base + 124#64 := hcpu_e.pc_eq.trans hpc
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 144#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_e_in]; exact s0.spAligned_sub 144#64 hsp0
  have hx19_e' : se'.readReg64 (.gpr 19#5) = vecPtr := (hcpu_e.readReg64 (.gpr 19#5)).trans hx19
  have hx20_e' : se'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 chunk.length :=
    (hcpu_e.readReg64 (.gpr 20#5)).trans hx20
  have hx21_e' : se'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length :=
    (hcpu_e.readReg64 (.gpr 21#5)).trans hx21
  wp_conv_pre => simp only [rustSprSavedSlots, ← hsp_e_in,
    show s0.sp - 136#64 = se'.sp + 8#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 128#64 = se'.sp + 16#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 120#64 = se'.sp + 24#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 112#64 = se'.sp + 32#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 104#64 = se'.sp + 40#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 96#64 = se'.sp + 48#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 88#64 = se'.sp + 56#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 80#64 = se'.sp + 64#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 72#64 = se'.sp + 72#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 64#64 = se'.sp + 80#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 56#64 = se'.sp + 88#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 48#64 = se'.sp + 96#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 40#64 = se'.sp + 104#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 32#64 = se'.sp + 112#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 24#64 = se'.sp + 120#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 16#64 = se'.sp + 128#64 by rw [hsp_e_in]; bv_lin,
    show s0.sp - 8#64 = se'.sp + 136#64 by rw [hsp_e_in]; bv_lin]
  wp_sym_steps
  refine SepWP.done (by rfl) (by simpa [arm64_norm] using hrun_e') fun sf hcpu_f _hcl_f hnsp_f => ?_
  have hpres_ef : SyscallPreserved s_ep sf :=
    syscallPreserved_of_seg hcpu_e hcpu_f hnsp_f (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq : A.pool lb' lk' s_ep = A.pool lb' lk' sf :=
    (A.pool_transport lb' lk' s_ep sf (poolPreserved_of_syscall hpres_ef)).symm
  have hcs_f : CalleeSavedPreserved s0 sf := by
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨by rw [hcpu_f.readReg64 .x19]; simp [arm64_norm],
      by rw [hcpu_f.readReg64 .x20]; simp [arm64_norm],
      by rw [hcpu_f.readReg64 .x21]; simp [arm64_norm],
      by rw [hcpu_f.readReg64 .x22]; simp [arm64_norm],
      by rw [hcpu_f.readReg64 .x23]; simp [arm64_norm],
      by rw [hcpu_f.readReg64 .x24]; simp [arm64_norm],
      by rw [hcpu_f.readReg64 .x25]; simp [arm64_norm],
      by rw [hcpu_f.readReg64 .x26]; simp [arm64_norm],
      by rw [hcpu_f.readReg64 .x27]; simp [arm64_norm],
      by rw [hcpu_f.readReg64 .x28]; simp [arm64_norm],
      by rw [hcpu_f.readReg64 .fp]; simp [arm64_norm], ?_⟩
    rw [hcpu_f.calleeSavedVRegs]; simp only [arm64_norm]; exact hcpu_e.calleeSavedVRegs.trans hvregs
  have hpc_f : sf.pc = s0.readReg64 .lr := by rw [hcpu_f.pc_eq]; rfl
  have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun_e'
  have hsp_f : sf.sp = s0.sp := by rw [hcpu_f.sp_eq]; simp [arm64_norm]
  have hx0_f : sf.readReg64 .x0 = 0#64 := by rw [hcpu_f.readReg64 .x0]; simp [arm64_norm]
  have hx1_f : sf.readReg64 .x1 = BitVec.ofNat 64 chunk.length := by
    rw [hcpu_f.readReg64 .x1]; simp [arm64_norm]
  have hadd_len : BitVec.ofNat 64 bs.length + BitVec.ofNat 64 chunk.length =
      BitVec.ofNat 64 (bs ++ chunk).length := by
    rw [List.length_append, ← BitVec.ofNat_add]
  refine SepWP.weaken_pre ?_ (SepWP.done hpc_f hrun_f
    (hcont sf hpc_f hrun_f hsp_f hcs_f hpres_ef hnsp_f.2.2.2.2.2.2 hnsp_f.1 hx0_f hx1_f))
  rw [hpool_eq, hadd_len, show 144 + reserveStack = reserveStack + 8 * 18 by omega,
      stackAt_split_cells s0.sp reserveStack 18 (by omega)]
  dsimp only [cells, rustStdVecU8At, vecHeader]
  simp only [Nat.reduceMul, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    hsp_e_in, bv_lin_norm]
  refine Entails.sepExists_right ptr' <|
    Entails.sepExists_right w0 <| Entails.sepExists_right w1 <|
    Entails.sepExists_right w2 <| Entails.sepExists_right w3 <|
    Entails.sepExists_right st4 <| Entails.sepExists_right st5 <|
    Entails.sepExists_right (s0.readReg64 (.gpr 29#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 30#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 28#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 27#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 26#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 25#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 24#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 23#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 22#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 21#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 20#5)) <|
    Entails.sepExists_right (s0.readReg64 (.gpr 19#5)) (by sep_entail)

private theorem rustSmallProbeRead_copy_and_epilogue [SmallProbeReadPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext : ∀ pc, P.externAt? pc = none)
    (hmemcpy : subroutine_ok P (rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl "memcpy")
      (rustStdIoMultiLib.withCodeLoaded SmallProbeReadPlacement.mpl stdMemcpySpec))
    {s0 s_cp : State} {vecPtr ptr' st4 st5 : BitVec 64}
    {cap' lb' lk' reserveStack : Nat} {bs chunk : List (BitVec 8)}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hstk_top : 144 + reserveStack ≤ 2 ^ 64)
    (hcl : rustStdIoMultiLib.CodeLoaded SmallProbeReadPlacement.mpl s_cp.mem)
    (hpc : s_cp.pc = sprPl13.base + 104#64)
    (hrun : s_cp.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : s_cp.sp = s0.sp - 144#64)
    (hx19 : s_cp.readReg64 (.gpr 19#5) = vecPtr)
    (hx20 : s_cp.readReg64 (.gpr 20#5) = BitVec.ofNat 64 chunk.length)
    (hx21 : s_cp.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length)
    (hvregs : calleeSavedVRegs s_cp = calleeSavedVRegs s0)
    (hclen_pos : 0 < chunk.length)
    (hclen_le32 : chunk.length ≤ 32)
    (hfit : chunk.length ≤ cap' - bs.length)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf → SyscallPreserved s_cp sf →
      sf.fs = s_cp.fs → sf.trace = s_cp.trace →
      sf.readReg64 .x0 = 0#64 → sf.readReg64 .x1 = BitVec.ofNat 64 chunk.length →
      post sf (stackAt s0.sp (144 + reserveStack) ∗
        rustStdVecU8At A vecPtr (bs ++ chunk) cap' ∗ A.pool lb' lk' sf ∗
        errnoCell s0.tpidrEl0)) :
    SepWP P (s0.readReg64 .lr) s_cp
      (stackAt (s0.sp - 144#64) reserveStack ∗
        ((s0.sp - 144#64) ↦ₛ (chunk ++ (List.replicate 32 0#8).drop chunk.length)) ∗
        rustSprSavedSlots s0 st4 st5 ∗
        (vecPtr ↦₆₄ BitVec.ofNat 64 cap') ∗ ((vecPtr + 8#64) ↦₆₄ ptr') ∗
        ((vecPtr + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        rustStdVecBuf A cap' ptr' bs ∗ A.pool lb' lk' s_cp ∗
        errnoCell s0.tpidrEl0)
      post oomProp := by
  have hcap'_ne : cap' ≠ 0 := by omega
  refine SepWP.weaken_pre (P' := rustStdVecBuf A cap' ptr' bs ∗
    (stackAt (s0.sp - 144#64) reserveStack ∗
      ((s0.sp - 144#64) ↦ₛ (chunk ++ (List.replicate 32 0#8).drop chunk.length)) ∗
      rustSprSavedSlots s0 st4 st5 ∗
      (vecPtr ↦₆₄ BitVec.ofNat 64 cap') ∗ ((vecPtr + 8#64) ↦₆₄ ptr') ∗
      ((vecPtr + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ A.pool lb' lk' s_cp ∗
      errnoCell s0.tpidrEl0))
    (by sep_entail) ?_
  wp_conv_pre => simp only [rustStdVecBuf, hcap'_ne, ↓reduceIte, sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨_hbs_le, hcap'_lt, hptr'_ne⟩
  apply sepWP_seg_rebase_pure (lib := rustStdIoMultiLib) (mpl := SmallProbeReadPlacement.mpl)
    hext 13 (by decide) rustIoBlockNoSvc0_13 hcl
    (mid := rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl "memcpy")
  intro sc' hcpu_c; change SepWP (sprPC13.rebase sprPl13.base (fun _ => none)) _ _ _ _
  have hpc_c' : sc'.pc = sprPl13.base + 104#64 := hcpu_c.pc_eq.trans hpc
  have hrun_c' : sc'.status = .Running := hcpu_c.status_eq.trans hrun
  have hsp_c_in : sc'.sp = s0.sp - 144#64 := hcpu_c.sp_eq.trans hsp_eq
  have hsp_c' : sc'.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_c_in]; exact s0.spAligned_sub 144#64 hsp0
  have hx19_c' : sc'.readReg64 (.gpr 19#5) = vecPtr := (hcpu_c.readReg64 (.gpr 19#5)).trans hx19
  have hx20_c' : sc'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 chunk.length :=
    (hcpu_c.readReg64 (.gpr 20#5)).trans hx20
  have hx21_c' : sc'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length :=
    (hcpu_c.readReg64 (.gpr 21#5)).trans hx21
  wp_sym_steps
  refine SepWP.done sprMemcpy_pc (by simpa [arm64_norm] using hrun_c') fun sm_mc hcpu_mc hcl_mc hnsp_mc => ?_
  have hpres_mc : SyscallPreserved s_cp sm_mc :=
    syscallPreserved_of_seg hcpu_c hcpu_mc hnsp_mc (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_mc : A.pool lb' lk' s_cp = A.pool lb' lk' sm_mc :=
    (A.pool_transport lb' lk' s_cp sm_mc (poolPreserved_of_syscall hpres_mc)).symm
  have hpc_mc : sm_mc.pc = rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl "memcpy" :=
    hcpu_mc.pc_eq.trans sprMemcpy_pc
  have hrun_mc : sm_mc.status = .Running := hcpu_mc.status_eq.trans hrun_c'
  have hsp_mc_eq : sm_mc.sp = s0.sp - 144#64 :=
    (hcpu_mc.sp_eq.trans (by simp [arm64_norm])).trans hsp_c_in
  have hsp_mc : sm_mc.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_mc_eq]; exact s0.spAligned_sub 144#64 hsp0
  have hlr_mc : sm_mc.readReg64 .lr =
      sprPl13.base + (reloc_call_off% sprLib13.text.relocs "memcpy" + 4#64) := by
    rw [hcpu_mc.readReg64 .lr]; simp [arm64_norm]
  have hx0_mc : sm_mc.readReg64 .x0 = ptr' + BitVec.ofNat 64 bs.length := by
    rw [hcpu_mc.readReg64 .x0]; simp [arm64_norm]
  have hx1_mc : sm_mc.readReg64 .x1 = s0.sp - 144#64 := by
    rw [hcpu_mc.readReg64 .x1]; simp [arm64_norm]
  have hx2_mc : sm_mc.readReg64 .x2 = BitVec.ofNat 64 chunk.length := by
    rw [hcpu_mc.readReg64 .x2]; simp [arm64_norm]
  wp_conv_pre =>
    rw [hpool_mc,
        memRegion_split_le (ptr' + BitVec.ofNat 64 bs.length) chunk.length (cap' - bs.length) hfit (by omega),
        pointsToBytes_append (a := s0.sp - 144#64)]
  apply seqCodeLoaded hcl_mc (mid := sprPl13.base + (reloc_call_off% sprLib13.text.relocs "memcpy" + 4#64))
  apply (SepWP.call_subroutine_frame hmemcpy
    (x := (ptr' + BitVec.ofNat 64 bs.length, s0.sp - 144#64, chunk))
    hpc_mc hrun_mc hsp_mc hlr_mc
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [MultiPlacedLib.withCodeLoaded, stdMemcpySpec]
    rw [sepConj_comm _ ⌜rustStdIoMultiLib.CodeLoaded SmallProbeReadPlacement.mpl sm_mc.mem⌝,
        sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl_mc, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_mc, hx1_mc, hx2_mc, by omega⟩, Satisfies.mono (by sep_frame) hm'⟩
  · intro sf_mc hpc_sfmc hrun_sfmc hsp_sfmc hcs_sfmc
    refine SepWP.done hpc_sfmc hrun_sfmc fun hcl_sfmc => ?_
    dsimp only [MultiPlacedLib.withCodeLoaded, stdMemcpySpec]
    wp_conv_pre => simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨_, hstd_mc⟩
    have hpres_sfmc : SyscallPreserved sm_mc sf_mc := SyscallPreserved.of_std hstd_mc
    have hpool_sfmc : A.pool lb' lk' sm_mc = A.pool lb' lk' sf_mc :=
      (A.pool_transport lb' lk' sm_mc sf_mc (poolPreserved_of_syscall hpres_sfmc)).symm
    have hsp_sfmc_eq : sf_mc.sp = s0.sp - 144#64 := hsp_sfmc.trans hsp_mc_eq
    have hx19_sfmc : sf_mc.readReg64 (.gpr 19#5) = vecPtr :=
      hcs_sfmc.readReg64_x19.trans ((hcpu_mc.readReg64 (.gpr 19#5)).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 19#5)).trans hx19_c'))
    have hx20_sfmc : sf_mc.readReg64 (.gpr 20#5) = BitVec.ofNat 64 chunk.length :=
      hcs_sfmc.readReg64_x20.trans ((hcpu_mc.readReg64 (.gpr 20#5)).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 20#5)).trans hx20_c'))
    have hx21_sfmc : sf_mc.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length :=
      hcs_sfmc.readReg64_x21.trans ((hcpu_mc.readReg64 (.gpr 21#5)).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 21#5)).trans hx21_c'))
    have hvregs_sfmc : calleeSavedVRegs sf_mc = calleeSavedVRegs s0 :=
      hcs_sfmc.vregs.trans (hcpu_mc.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs sc').trans
          (hcpu_c.calleeSavedVRegs.trans hvregs)))
    have hpbuf_len : (chunk ++ (List.replicate 32 0#8).drop chunk.length).length = 32 := by
      simp [List.length_append, List.length_drop]; omega
    refine SepWP.weaken_pre ?_
      (rustSmallProbeRead_epilogue A hext (ptr' := ptr') (st4 := st4) (st5 := st5)
        hstk_top hcl_sfmc hpc_sfmc hrun_sfmc hsp0 hsp_sfmc_eq
        hx19_sfmc hx20_sfmc hx21_sfmc hvregs_sfmc hpbuf_len
        fun sf hpc_f hrun_f hsp_f hcs_f hpres_ef hfs_ef htr_ef hx0_f hx1_f =>
          hcont sf hpc_f hrun_f hsp_f hcs_f
            (hpres_mc.trans (hpres_sfmc.trans hpres_ef))
            (hfs_ef.trans (hstd_mc.1.trans hnsp_mc.2.2.2.2.2.2))
            (htr_ef.trans (hstd_mc.2.1.trans hnsp_mc.1)) hx0_f hx1_f)
    dsimp only [rustStdVecBuf, rustSprSavedSlots]
    simp only [hcap'_ne, ↓reduceIte]
    rw [pure_sepConj_of_true ⟨by simp [List.length_append]; omega, hcap'_lt, hptr'_ne⟩,
        pointsToBytes_append (a := s0.sp - 144#64),
        pointsToBytes_append (a := ptr'),
        show ptr' + BitVec.ofNat 64 (bs ++ chunk).length =
          ptr' + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 chunk.length by
          rw [List.length_append, BitVec.ofNat_add, BitVec.add_assoc],
        show cap' - (bs ++ chunk).length = cap' - bs.length - chunk.length by
          simp [List.length_append]; omega,
        ← hpool_sfmc]
    sep_entail

private theorem rustSmallProbeRead_reserve [SmallProbeReadPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} {fd : BitVec 64} {cap lb lk reserveStack : Nat}
    (hext : ∀ pc, P.externAt? pc = none)
    (hmemcpy : subroutine_ok P (rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl "memcpy")
      (rustStdIoMultiLib.withCodeLoaded SmallProbeReadPlacement.mpl stdMemcpySpec))
    (hreserve : subroutine_ok P
      (rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl doReserveAndHandleIoSym)
      (rustStdIoMultiLib.withCodeLoaded SmallProbeReadPlacement.mpl
        (rustDoReserveAndHandleSpec A reserveStack)))
    {s0 s_r : State} {vecPtr ptr st4 st5 : BitVec 64}
    {bs chunk : List (BitVec 8)} {desc : FdEntry}
    {post : State → SepProp → Prop}
    (hstk_top : 144 + reserveStack ≤ 2 ^ 64)
    (hcl : rustStdIoMultiLib.CodeLoaded SmallProbeReadPlacement.mpl s_r.mem)
    (hpc : s_r.pc = sprPl13.base + 320#64)
    (hrun : s_r.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp_eq : s_r.sp = s0.sp - 144#64)
    (hx19 : s_r.readReg64 (.gpr 19#5) = vecPtr)
    (hx20 : s_r.readReg64 (.gpr 20#5) = BitVec.ofNat 64 chunk.length)
    (hx21 : s_r.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length)
    (hvregs : calleeSavedVRegs s_r = calleeSavedVRegs s0)
    (hclen_le32 : chunk.length ≤ 32)
    (hgt : cap - bs.length < chunk.length)
    (hno_null : ¬ NullAllowed (rustVecGrowCap cap bs.length chunk.length) 1)
    (hcan : A.CanAlloc lb lk (rustVecGrowCap cap bs.length chunk.length) 1)
    (hio_r : IoFrame s0 s_r)
    (hfs_r : s_r.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }))
    (htp_r : s_r.tpidrEl0 = s0.tpidrEl0)
    (hbrks_r : s_r.brkStart = s0.brkStart)
    (hcont : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      sf.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }) →
      IoFrame s0 sf → sf.tpidrEl0 = s0.tpidrEl0 → sf.brkStart = s0.brkStart →
      sf.readReg64 .x0 = 0#64 → sf.readReg64 .x1 = BitVec.ofNat 64 chunk.length →
      let growCap := rustVecGrowCap cap bs.length chunk.length
      post sf (stackAt s0.sp (144 + reserveStack) ∗
        rustStdVecU8At A vecPtr (bs ++ chunk) growCap ∗
        A.pool (rustVecGrowLb A lb cap growCap) (rustVecGrowLk lk cap) sf ∗
        errnoCell s0.tpidrEl0)) :
    SepWP P (s0.readReg64 .lr) s_r
      (stackAt (s0.sp - 144#64) reserveStack ∗
        ((s0.sp - 144#64) ↦ₛ (chunk ++ (List.replicate 32 0#8).drop chunk.length)) ∗
        rustSprSavedSlots s0 st4 st5 ∗
        (vecPtr ↦₆₄ BitVec.ofNat 64 cap) ∗ ((vecPtr + 8#64) ↦₆₄ ptr) ∗
        ((vecPtr + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        rustStdVecBuf A cap ptr bs ∗ A.pool lb lk s_r ∗
        errnoCell s0.tpidrEl0)
      post
      (fun sf =>
        ⌜cap - bs.length < chunk.length ∧
          ∃ sm, IoFrame s0 sm ∧
            sm.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }) ∧
            oom sm sf⌝) := by
  apply sepWP_seg_rebase_pure (lib := rustStdIoMultiLib) (mpl := SmallProbeReadPlacement.mpl)
    hext 13 (by decide) rustIoBlockNoSvc0_13 hcl
    (mid := rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl doReserveAndHandleIoSym)
  intro sr' hcpu_r; change SepWP (sprPC13.rebase sprPl13.base (fun _ => none)) _ _ _ _
  have hpc_r' : sr'.pc = sprPl13.base + 320#64 := hcpu_r.pc_eq.trans hpc
  have hrun_r' : sr'.status = .Running := hcpu_r.status_eq.trans hrun
  have hsp_r_in : sr'.sp = s0.sp - 144#64 := hcpu_r.sp_eq.trans hsp_eq
  have hsp_r' : sr'.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_r_in]; exact s0.spAligned_sub 144#64 hsp0
  have hx19_r' : sr'.readReg64 (.gpr 19#5) = vecPtr := (hcpu_r.readReg64 (.gpr 19#5)).trans hx19
  have hx20_r' : sr'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 chunk.length :=
    (hcpu_r.readReg64 (.gpr 20#5)).trans hx20
  have hx21_r' : sr'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length :=
    (hcpu_r.readReg64 (.gpr 21#5)).trans hx21
  wp_sym_steps
  refine SepWP.done sprReserve_pc (by simpa [arm64_norm] using hrun_r')
    fun sm_res hcpu_mres hcl_mres hnsp_mres => ?_
  have hpres_mres : SyscallPreserved s_r sm_res :=
    syscallPreserved_of_seg hcpu_r hcpu_mres hnsp_mres (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_mres : A.pool lb lk s_r = A.pool lb lk sm_res :=
    (A.pool_transport lb lk s_r sm_res (poolPreserved_of_syscall hpres_mres)).symm
  have htp_mres : sm_res.tpidrEl0 = s0.tpidrEl0 := hpres_mres.1.trans htp_r
  have hio_mres : IoFrame s0 sm_res :=
    ⟨hnsp_mres.1.trans hio_r.1, hpres_mres.2.1.trans hio_r.2⟩
  have hfs_mres : sm_res.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }) :=
    hnsp_mres.2.2.2.2.2.2.trans hfs_r
  have hpc_mres : sm_res.pc =
      rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl doReserveAndHandleIoSym :=
    hcpu_mres.pc_eq.trans sprReserve_pc
  have hrun_mres : sm_res.status = .Running := hcpu_mres.status_eq.trans hrun_r'
  have hsp_mres_eq : sm_res.sp = s0.sp - 144#64 :=
    (hcpu_mres.sp_eq.trans (by simp [arm64_norm])).trans hsp_r_in
  have hsp_mres : sm_res.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_mres_eq]; exact s0.spAligned_sub 144#64 hsp0
  have hlr_mres : sm_res.readReg64 .lr =
      sprPl13.base + (reloc_call_off% sprLib13.text.relocs
        "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [rust_std_io]" + 4#64) := by
    rw [hcpu_mres.readReg64 .lr]; simp [arm64_norm]
  have hx0_mres : sm_res.readReg64 .x0 = vecPtr := by
    rw [hcpu_mres.readReg64 .x0]; simp [arm64_norm]
  have hx1_mres : sm_res.readReg64 .x1 = BitVec.ofNat 64 bs.length := by
    rw [hcpu_mres.readReg64 .x1]; simp [arm64_norm]
  have hx2_mres : sm_res.readReg64 .x2 = BitVec.ofNat 64 chunk.length := by
    rw [hcpu_mres.readReg64 .x2]; simp [arm64_norm]
  have hx3_mres : sm_res.readReg64 .x3 = 1#64 := by
    rw [hcpu_mres.readReg64 .x3]; simp [arm64_norm]
  have hx4_mres : sm_res.readReg64 .x4 = 1#64 := by
    rw [hcpu_mres.readReg64 .x4]; simp [arm64_norm]
  wp_conv_pre => rw [hpool_mres, ← hsp_mres_eq, ← errnoCell_eq, ← htp_mres]
  apply seqCodeLoaded hcl_mres
    (mid := sprPl13.base + (reloc_call_off% sprLib13.text.relocs
      "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [rust_std_io]" + 4#64))
  apply (SepWP.call_subroutine_frame hreserve
    (x := (vecPtr, ptr, cap, bs, chunk.length, lb, lk))
    hpc_mres hrun_mres hsp_mres hlr_mres
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun R' sf _ ho => by
      dsimp only [MultiPlacedLib.withCodeLoaded, rustDoReserveAndHandleSpec] at ho
      rw [satisfies_pure_sepConj] at ho
      rcases ho with ⟨⟨sm, hio_sm, hfs_sm, hoom_sm⟩, hFR⟩
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hgt, sm, ⟨hio_sm.1.trans hio_mres.1, hio_sm.2.trans hio_mres.2⟩,
        hfs_sm.trans hfs_mres, hoom_sm⟩, Satisfies.drop_left hFR⟩))
  · intro R' hm'
    dsimp only [MultiPlacedLib.withCodeLoaded, rustDoReserveAndHandleSpec]
    rw [sepConj_comm _ ⌜rustStdIoMultiLib.CodeLoaded SmallProbeReadPlacement.mpl sm_res.mem⌝,
        sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl_mres, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_mres, hx1_mres, hx2_mres, hx3_mres, hx4_mres, hgt, hno_null, hcan⟩,
      Satisfies.mono (by sep_frame) hm'⟩
  · intro sf_res hpc_sfres hrun_sfres hsp_sfres hcs_sfres
    refine SepWP.done hpc_sfres hrun_sfres fun hcl_sfres => ?_
    dsimp only [MultiPlacedLib.withCodeLoaded, rustDoReserveAndHandleSpec]
    wp_conv_pre => simp only [sepExists_sepConj_left]
    refine SepWP.exists_elim fun newPtr => ?_
    wp_conv_pre => simp only [sepConj_assoc, hsp_mres_eq, htp_mres, errnoCell_eq]
    apply SepWP.pure_elim; rintro ⟨hfs_al, htr_al, hsig_al, htp_al, hbrks_al, _, _⟩
    have hsp_sfres_eq : sf_res.sp = s0.sp - 144#64 := hsp_sfres.trans hsp_mres_eq
    have hx19_sfres : sf_res.readReg64 (.gpr 19#5) = vecPtr :=
      hcs_sfres.readReg64_x19.trans ((hcpu_mres.readReg64 (.gpr 19#5)).trans
        ((by simp [arm64_norm] : _ = sr'.readReg64 (.gpr 19#5)).trans hx19_r'))
    have hx20_sfres : sf_res.readReg64 (.gpr 20#5) = BitVec.ofNat 64 chunk.length :=
      hcs_sfres.readReg64_x20.trans ((hcpu_mres.readReg64 (.gpr 20#5)).trans
        ((by simp [arm64_norm] : _ = sr'.readReg64 (.gpr 20#5)).trans hx20_r'))
    have hvregs_sfres : calleeSavedVRegs sf_res = calleeSavedVRegs s0 :=
      hcs_sfres.vregs.trans (hcpu_mres.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs sr').trans
          (hcpu_r.calleeSavedVRegs.trans hvregs)))
    apply sepWP_seg_rebase_pure (lib := rustStdIoMultiLib) (mpl := SmallProbeReadPlacement.mpl)
      hext 13 (by decide) rustIoBlockNoSvc0_13 hcl_sfres (mid := sprPl13.base + 104#64)
    intro sb' hcpu_b; change SepWP (sprPC13.rebase sprPl13.base (fun _ => none)) _ _ _ _
    have hpc_b' : sb'.pc = sprPl13.base + 344#64 := hcpu_b.pc_eq.trans hpc_sfres
    have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_sfres
    have hsp_b_in : sb'.sp = s0.sp - 144#64 := hcpu_b.sp_eq.trans hsp_sfres_eq
    have hsp_b' : sb'.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_b_in]; exact s0.spAligned_sub 144#64 hsp0
    have hx19_b' : sb'.readReg64 (.gpr 19#5) = vecPtr :=
      (hcpu_b.readReg64 (.gpr 19#5)).trans hx19_sfres
    wp_sym_steps
    refine SepWP.done (by rfl) (by simpa [arm64_norm] using hrun_b')
      fun s_cp hcpu_cp hcl_cp hnsp_cp => ?_
    have hpres_cp : SyscallPreserved sf_res s_cp :=
      syscallPreserved_of_seg hcpu_b hcpu_cp hnsp_cp (by simp [arm64_norm]) (by simp [arm64_norm])
    let growCap := rustVecGrowCap cap bs.length chunk.length
    have hpool_cp :
        A.pool (rustVecGrowLb A lb cap growCap) (rustVecGrowLk lk cap) sf_res =
          A.pool (rustVecGrowLb A lb cap growCap) (rustVecGrowLk lk cap) s_cp :=
      (A.pool_transport _ _ sf_res s_cp (poolPreserved_of_syscall hpres_cp)).symm
    have hpc_cp : s_cp.pc = sprPl13.base + 104#64 := by rw [hcpu_cp.pc_eq]; rfl
    have hrun_cp : s_cp.status = .Running := hcpu_cp.status_eq.trans hrun_b'
    have hsp_cp : s_cp.sp = s0.sp - 144#64 :=
      (hcpu_cp.sp_eq.trans (by simp [arm64_norm])).trans hsp_b_in
    have hx19_cp : s_cp.readReg64 (.gpr 19#5) = vecPtr :=
      (hcpu_cp.readReg64 (.gpr 19#5)).trans ((by simp [arm64_norm] : _ = sb'.readReg64 (.gpr 19#5)).trans hx19_b')
    have hx20_cp : s_cp.readReg64 (.gpr 20#5) = BitVec.ofNat 64 chunk.length :=
      (hcpu_cp.readReg64 (.gpr 20#5)).trans ((by simp [arm64_norm] : _ = sb'.readReg64 (.gpr 20#5)).trans
        ((hcpu_b.readReg64 (.gpr 20#5)).trans hx20_sfres))
    have hx21_cp : s_cp.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length := by
      rw [hcpu_cp.readReg64 (.gpr 21#5)]; simp [arm64_norm]
    have hvregs_cp : calleeSavedVRegs s_cp = calleeSavedVRegs s0 :=
      hcpu_cp.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
        (hcpu_b.calleeSavedVRegs.trans hvregs_sfres))
    have hfit_grow : chunk.length ≤ growCap - bs.length := by
      have := rustVecGrowCap_ge cap bs.length chunk.length; omega
    refine SepWP.weaken_pre (by rw [hpool_cp]; dsimp only [rustSprSavedSlots]; sep_entail) <|
      rustSmallProbeRead_copy_and_epilogue A hext hmemcpy
        (ptr' := newPtr) (st4 := st4) (st5 := st5)
        hstk_top hcl_cp hpc_cp hrun_cp hsp0
        hsp_cp hx19_cp hx20_cp hx21_cp hvregs_cp (by omega) hclen_le32 hfit_grow
        fun sf hpc_f hrun_f hsp_f hcs_f hpres_cpf hfs_cpf htr_cpf hx0_f hx1_f =>
          hcont sf hpc_f hrun_f hsp_f hcs_f
            (hfs_cpf.trans (hnsp_cp.2.2.2.2.2.2.trans (hfs_al.trans hfs_mres)))
            ⟨htr_cpf.trans (hnsp_cp.1.trans (htr_al.trans hio_mres.1)),
             hpres_cpf.2.1.trans (hpres_cp.2.1.trans (hsig_al.trans hio_mres.2))⟩
            (hpres_cpf.1.trans (hpres_cp.1.trans (htp_al.trans (hpres_mres.1.trans htp_r))))
            (hpres_cpf.2.2.brkStart_eq.trans (hpres_cp.2.2.brkStart_eq.trans
              (hbrks_al.trans (hpres_mres.2.2.brkStart_eq.trans hbrks_r))))
            hx0_f hx1_f

/-- Total-correctness and OOM-explicit contract for
    `std::io::default_read_to_end::small_probe_read::<std::fs::File>`
    (block `13` of `rustStdIoMultiLib`, `smallProbeReadFileSym`). -/
theorem rustSmallProbeRead_ok {oom : State → State → Prop} (A : RustStdAlloc oom)
    {mpl : MultiPlacement} (hpl : rustStdIoMultiLib.Placeable mpl)
    {P : Program} {fd : BitVec 64} {reserveStack : Nat}
    (hext : ∀ pc, P.externAt? pc = none)
    (hstk : 32 ≤ reserveStack ∧ 144 + reserveStack ≤ 2 ^ 64 := by decide)
    (hread : subroutine_ok P (rustStdIoMultiLib.resolve mpl "read")
      (rustStdIoMultiLib.withCodeLoaded mpl muslRead32ClampedSpec))
    (hmemcpy : subroutine_ok P (rustStdIoMultiLib.resolve mpl "memcpy")
      (rustStdIoMultiLib.withCodeLoaded mpl stdMemcpySpec))
    (hreserve : subroutine_ok P (rustStdIoMultiLib.resolve mpl doReserveAndHandleIoSym)
      (rustStdIoMultiLib.withCodeLoaded mpl (rustDoReserveAndHandleSpec A reserveStack))) :
    subroutine_ok P (rustStdIoMultiLib.fnAddr mpl smallProbeReadFileSym)
      (rustStdIoMultiLib.withCodeLoaded mpl (rustSmallProbeReadSpec A fd reserveStack)) := by
  letI : SmallProbeReadPlacement := ⟨mpl, hpl⟩
  apply subroutine_ok_of_sepWP_init
  rintro ⟨vecPtr, cap, bs, desc, lb, lk⟩ R s0 hpc hrun hpre hsp
  rw [fnAddr_eq_base hpl 13 smallProbeReadFileSym (by decide) (by decide)] at hpc
  dsimp only [MultiPlacedLib.withCodeLoaded, rustSmallProbeReadSpec] at hpre ⊢
  rw [errnoCell_eq] at hpre ⊢
  rw [sepConj_comm _ ⌜rustStdIoMultiLib.CodeLoaded mpl s0.mem⌝,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hw0, hx1, hfds, hfd_ge, hfd_lt, hkind, hcanr, hsp_lo, hsp_va, hlfs, hgrow_ok⟩, hpre⟩
  let chunk := ((s0.fs.fdBytes desc).drop desc.offset).take 32
  have hclen_le32 : chunk.length ≤ 32 := by simp [chunk]; omega
  dsimp only [rustStdVecU8At, vecHeader] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨ptr, hpre⟩
  have ⟨hbs_le, hcap_lt, _⟩ :=
    satisfies_rustStdVecBuf_bounds (A := A) (cap := cap) (ptr := ptr) (bs := bs)
      (Satisfies.mono (by sep_frame) hpre)
  rw [show 144 + reserveStack = reserveStack + 8 * 18 by omega,
      stackAt_split_cells s0.sp reserveStack 18 (by omega)] at hpre
  dsimp only [cells] at hpre
  simp only [Nat.reduceMul, bv_lin_norm, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨st0, st1, st2, st3, st4, st5, st6, st7, st8, st9, st10, st11,
    st12, st13, st14, st15, st16, st17, hpre⟩
  refine ⟨_, hpre, ?_⟩
  apply sepWP_seg_rebase_pure (lib := rustStdIoMultiLib) (mpl := SmallProbeReadPlacement.mpl)
    hext 13 (by decide) rustIoBlockNoSvc0_13 hcl
    (mid := rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl "read")
  intro s0' hcpu0; change SepWP (sprPC13.rebase sprPl13.base (fun _ => none)) _ _ _ _
  have hpc0' : s0'.pc = sprPl13.base := hcpu0.pc_eq.trans hpc
  have hrun0' : s0'.status = .Running := hcpu0.status_eq.trans hrun
  have hsp0' : s0'.spAligned = true := hcpu0.spAligned.trans hsp
  have hw0' : BitVec.setWidth 32 (s0'.readReg64 (.gpr 0#5)) = BitVec.setWidth 32 fd :=
    (hcpu0.readReg32 .x0).trans hw0
  have hx1' : s0'.readReg64 (.gpr 1#5) = vecPtr := (hcpu0.readReg64 .x1).trans hx1
  wp_conv_pre => simp only [← hcpu0.sp_eq]
  clear hpc; wp_sym_steps
  refine SepWP.done sprRead_pc (by simpa [arm64_norm] using hrun0') fun sm1 hcpu_m1 hcl1 hnsp1 => ?_
  have hpres_m1 : SyscallPreserved s0 sm1 :=
    syscallPreserved_of_seg hcpu0 hcpu_m1 hnsp1
      (by simp [State.writeVReg128, arm64_norm]) (by simp [State.writeVReg128, arm64_norm])
  have hpool_m1 : A.pool lb lk s0 = A.pool lb lk sm1 :=
    (A.pool_transport lb lk s0 sm1 (poolPreserved_of_syscall hpres_m1)).symm
  have hfs_m1 : sm1.fs = s0.fs := hnsp1.2.2.2.2.2.2
  have htr_m1 : sm1.trace = s0.trace := hnsp1.1
  have hpc1 : sm1.pc = rustStdIoMultiLib.resolve SmallProbeReadPlacement.mpl "read" :=
    hcpu_m1.pc_eq.trans sprRead_pc
  have hrun1 : sm1.status = .Running := hcpu_m1.status_eq.trans hrun0'
  have hsp1_eq : sm1.sp = s0.sp - 144#64 := by
    rw [hcpu_m1.sp_eq]; simp [arm64_norm, hcpu0.sp_eq]
  have hsp1 : sm1.spAligned = true := by
    simp only [State.spAligned]; rw [hsp1_eq]; exact s0.spAligned_sub 144#64 hsp
  have hlr1 : sm1.readReg64 .lr =
      sprPl13.base + (reloc_call_off% sprLib13.text.relocs "read" + 4#64) := by
    rw [hcpu_m1.readReg64 .lr]; simp [arm64_norm]
  have hx0_m1 : (sm1.readReg32 .x0).zeroExtend 64 = fd := by
    rw [hcpu_m1.readReg32 .x0]; dsimp only [State.readReg32, Reg.x0]
    simp only [arm64_norm, hw0']; bv_omega
  have hx1_m1 : sm1.readReg64 .x1 = s0.sp - 144#64 := by
    rw [hcpu_m1.readReg64 .x1]; simp [arm64_norm, hcpu0.sp_eq]
  have hx2_m1 : sm1.readReg64 .x2 = 32#64 := by rw [hcpu_m1.readReg64 .x2]; simp [arm64_norm]
  have hfds_m1 : sm1.fs.fds fd = some desc := by rw [hfs_m1]; exact hfds
  refine SepWP.weaken_pre (P' :=
      stackAt sm1.sp 32 ∗ ((s0.sp - 144#64) ↦ₛ List.replicate 32 0#8) ∗
      memRegion (sm1.sp - BitVec.ofNat 64 reserveStack) (reserveStack - 32) ∗
      rustSprSavedSlots s0 st4 st5 ∗
      (vecPtr ↦₆₄ BitVec.ofNat 64 cap) ∗ ((vecPtr + 8#64) ↦₆₄ ptr) ∗
      ((vecPtr + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      rustStdVecBuf A cap ptr bs ∗ A.pool lb lk sm1 ∗
      errnoCell s0.tpidrEl0)
    (by
      rw [stackAt_shrink (s0'.sp - 144) reserveStack 32 hstk.1 (by omega),
          ← rustPointsTo64_sp144_zero]
      simp only [hcpu0.sp_eq, hcpu0.readReg64, hpool_m1, hsp1_eq, rustSprSavedSlots, bv_lin_norm]
      sep_entail) ?_
  apply seqCodeLoaded hcl1 (mid := sprPl13.base + (reloc_call_off% sprLib13.text.relocs "read" + 4#64))
  apply (SepWP.call_subroutine_frame hread
    (x := (fd, s0.sp - 144#64, 32#64, desc, List.replicate 32 0#8))
    hpc1 hrun1 hsp1 hlr1
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [MultiPlacedLib.withCodeLoaded, muslRead32ClampedSpec]
    rw [sepConj_comm _ ⌜rustStdIoMultiLib.CodeLoaded mpl sm1.mem⌝,
        sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_m1, hfd_ge, hfd_lt, hx1_m1, hx2_m1,
      by unfold Arm64.USER_VA_LIMIT at hsp_va ⊢; bv_omega, hlfs, rfl, hfds_m1, hkind, hcanr⟩,
      Satisfies.mono (by sep_frame) hm'⟩
  · intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1
    refine SepWP.done hpc_sf1 hrun_sf1 fun hcl_sf1 => ?_
    dsimp only [MultiPlacedLib.withCodeLoaded, muslRead32ClampedSpec]
    have hchunk_eq : ((sm1.fs.fdBytes desc).drop desc.offset).take 32 = chunk := by rw [hfs_m1]
    wp_conv_pre => simp only [hsp1_eq, show min (32#64).toNat Arm64.MAX_RW_COUNT = 32 from rfl, hchunk_eq, sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_sf1, hfs_sf1, htr_sf1, hpres_sf1⟩
    have hpres_01 : SyscallPreserved s0 sf1 := hpres_m1.trans hpres_sf1
    have hpool_sf1 : A.pool lb lk sm1 = A.pool lb lk sf1 :=
      (A.pool_transport lb lk sm1 sf1 (poolPreserved_of_syscall hpres_sf1)).symm
    have hfs_01 : sf1.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }) :=
      hfs_sf1.trans (by rw [hfs_m1])
    have htr_01 : sf1.trace = s0.trace := htr_sf1.trans htr_m1
    have hsp_sf1_eq : sf1.sp = s0.sp - 144#64 := hsp_sf1.trans hsp1_eq
    have hx19_sf1 : sf1.readReg64 (.gpr 19#5) = vecPtr := by
      rw [hcs_sf1.readReg64_x19, hcpu_m1.readReg64 (.gpr 19#5)]
      simp [arm64_norm]
    have hvregs_sf1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0 :=
      hcs_sf1.vregs.trans (hcpu_m1.calleeSavedVRegs.trans
        ((by simp [arm64_norm] : _ = calleeSavedVRegs s0').trans hcpu0.calleeSavedVRegs))
    refine SepWP.weaken_pre (P' :=
        stackAt (s0.sp - 144#64) reserveStack ∗
        ((s0.sp - 144#64) ↦ₛ (chunk ++ (List.replicate 32 0#8).drop chunk.length)) ∗
        rustSprSavedSlots s0 st4 st5 ∗
        (vecPtr ↦₆₄ BitVec.ofNat 64 cap) ∗ ((vecPtr + 8#64) ↦₆₄ ptr) ∗
        ((vecPtr + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        rustStdVecBuf A cap ptr bs ∗ A.pool lb lk sf1 ∗
        errnoCell s0.tpidrEl0)
      (by
        rw [hpool_sf1, stackAt_shrink (s0.sp - 144#64) reserveStack 32 hstk.1 (by omega)]
        dsimp only [rustSprSavedSlots]
        sep_entail) ?_
    have hcmn_ne : BitVec.ofNat 64 chunk.length + 1#64 ≠ 0#64 := by bv_omega
    have hcmn_bne : (BitVec.ofNat 64 chunk.length + 1#64 != 0#64) = true := bne_iff_ne.mpr hcmn_ne
    have hcmn_beq : (BitVec.ofNat 64 chunk.length + 1#64 == 0#64) = false := beq_false_of_ne hcmn_ne
    have hcmp33_ule : BitVec.ule 33#64 (BitVec.ofNat 64 chunk.length) = false := by
      simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : chunk.length < 2 ^ 64)]; omega
    have hcmp33_ult : BitVec.ult (BitVec.ofNat 64 chunk.length) 33#64 = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : chunk.length < 2 ^ 64)]; omega
    have hsub_cap : BitVec.ofNat 64 cap - BitVec.ofNat 64 bs.length =
        BitVec.ofNat 64 (cap - bs.length) := by
      have hcap_split : cap = bs.length + (cap - bs.length) := by omega
      conv => lhs; arg 1; rw [hcap_split]
      exact rustBv64_ofNat_sub_len (by omega)
    by_cases hgt : cap - bs.length < chunk.length
    · obtain ⟨hno_null, hcan⟩ := hgrow_ok hgt
      have hcmp_cap : (BitVec.ofNat 64 (cap - bs.length)).ult (BitVec.ofNat 64 chunk.length) = true := by
        simp [BitVec.ult, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : chunk.length < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : cap - bs.length < 2 ^ 64)]; omega
      have hcmp_cap_ule : (BitVec.ofNat 64 chunk.length).ule (BitVec.ofNat 64 (cap - bs.length)) = false := by
        simp [BitVec.ule, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : chunk.length < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : cap - bs.length < 2 ^ 64)]; omega
      apply sepWP_seg_rebase_pure (lib := rustStdIoMultiLib) (mpl := SmallProbeReadPlacement.mpl)
        hext 13 (by decide) rustIoBlockNoSvc0_13 hcl_sf1 (mid := sprPl13.base + 320#64)
      intro s2' hcpu2; change SepWP (sprPC13.rebase sprPl13.base (fun _ => none)) _ _ _ _
      have hpc2' : s2'.pc = sprPl13.base + 60#64 := hcpu2.pc_eq.trans hpc_sf1
      have hrun2' : s2'.status = .Running := hcpu2.status_eq.trans hrun_sf1
      have hsp2_in : s2'.sp = s0.sp - 144#64 := hcpu2.sp_eq.trans hsp_sf1_eq
      have hsp2' : s2'.spAligned = true := by
        simp only [State.spAligned]; rw [hsp2_in]; exact s0.spAligned_sub 144#64 hsp
      have hx0_2' : s2'.readReg64 (.gpr 0#5) = BitVec.ofNat 64 chunk.length :=
        (hcpu2.readReg64 .x0).trans hx0_sf1
      have hx19_2' : s2'.readReg64 (.gpr 19#5) = vecPtr :=
        (hcpu2.readReg64 (.gpr 19#5)).trans hx19_sf1
      wp_sym_steps
      refine SepWP.done (by rfl) (by simpa [arm64_norm] using hrun2')
        fun s_r hcpu_r hcl_r hnsp_r => ?_
      have hpres_1r : SyscallPreserved sf1 s_r :=
        syscallPreserved_of_seg hcpu2 hcpu_r hnsp_r (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpres_0r : SyscallPreserved s0 s_r := hpres_01.trans hpres_1r
      have hpool_r : A.pool lb lk sf1 = A.pool lb lk s_r :=
        (A.pool_transport lb lk sf1 s_r (poolPreserved_of_syscall hpres_1r)).symm
      have hpc_r : s_r.pc = sprPl13.base + 320#64 := by rw [hcpu_r.pc_eq]; rfl
      have hrun_r : s_r.status = .Running := hcpu_r.status_eq.trans hrun2'
      have hsp_r : s_r.sp = s0.sp - 144#64 :=
        (hcpu_r.sp_eq.trans (by simp [arm64_norm])).trans hsp2_in
      have hx19_r : s_r.readReg64 (.gpr 19#5) = vecPtr :=
        (hcpu_r.readReg64 (.gpr 19#5)).trans
          ((by simp [arm64_norm] : _ = s2'.readReg64 (.gpr 19#5)).trans hx19_2')
      have hx20_r : s_r.readReg64 (.gpr 20#5) = BitVec.ofNat 64 chunk.length := by
        rw [hcpu_r.readReg64 (.gpr 20#5)]; simp [arm64_norm]
      have hx21_r : s_r.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length := by
        rw [hcpu_r.readReg64 (.gpr 21#5)]; simp [arm64_norm]
      have hvregs_r : calleeSavedVRegs s_r = calleeSavedVRegs s0 :=
        hcpu_r.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs s2').trans
            (hcpu2.calleeSavedVRegs.trans hvregs_sf1))
      refine SepWP.weaken_pre (by rw [hpool_r]; sep_entail) <|
        rustSmallProbeRead_reserve A hext hmemcpy hreserve hstk.2 hcl_r hpc_r hrun_r hsp
          hsp_r hx19_r hx20_r hx21_r hvregs_r hclen_le32 hgt hno_null hcan
          ⟨hnsp_r.1.trans htr_01, hpres_0r.2.1⟩
          (hnsp_r.2.2.2.2.2.2.trans hfs_01) hpres_0r.1 hpres_0r.2.2.brkStart_eq
          fun sf _ _ hsp_f hcs_f hfs_f hio_f htp_f hbrks_f hx0_f hx1_f =>
            ⟨fun hm_f => Satisfies.mono (by
              have hgrew : decide (cap - bs.length < chunk.length) = true := decide_eq_true hgt
              simp only [show ((s0.fs.fdBytes desc).drop desc.offset).take 32 = chunk from rfl,
                hgrew, ↓reduceIte]
              rw [pure_sepConj_of_true ⟨hx0_f, hx1_f, hfs_f, hio_f, htp_f, hbrks_f,
                fun hf => Bool.noConfusion hf⟩]
              sep_entail) hm_f, hsp_f, hcs_f⟩
    · have hle : chunk.length ≤ cap - bs.length := Nat.le_of_not_lt hgt
      have hcmp_cap : (BitVec.ofNat 64 (cap - bs.length)).ult (BitVec.ofNat 64 chunk.length) = false := by
        simp [BitVec.ult, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : chunk.length < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : cap - bs.length < 2 ^ 64)]; omega
      have hcmp_cap_ule : (BitVec.ofNat 64 chunk.length).ule (BitVec.ofNat 64 (cap - bs.length)) = true := by
        simp [BitVec.ule, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : chunk.length < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : cap - bs.length < 2 ^ 64)]; omega
      have hgrew : decide (cap - bs.length < chunk.length) = false := decide_eq_false hgt
      by_cases hc0 : chunk.length = 0
      · have hchunk_nil : chunk = [] := List.eq_nil_of_length_eq_zero hc0
        have hult0 : (BitVec.ofNat 64 (cap - bs.length)).ult 0#64 = false := by simp [BitVec.ult]
        apply sepWP_seg_rebase_pure (lib := rustStdIoMultiLib) (mpl := SmallProbeReadPlacement.mpl)
          hext 13 (by decide) rustIoBlockNoSvc0_13 hcl_sf1 (mid := sprPl13.base + 124#64)
        intro s2' hcpu2; change SepWP (sprPC13.rebase sprPl13.base (fun _ => none)) _ _ _ _
        have hpc2' : s2'.pc = sprPl13.base + 60#64 := hcpu2.pc_eq.trans hpc_sf1
        have hrun2' : s2'.status = .Running := hcpu2.status_eq.trans hrun_sf1
        have hsp2_in : s2'.sp = s0.sp - 144#64 := hcpu2.sp_eq.trans hsp_sf1_eq
        have hsp2' : s2'.spAligned = true := by
          simp only [State.spAligned]; rw [hsp2_in]; exact s0.spAligned_sub 144#64 hsp
        have hx0_2' : s2'.readReg64 (.gpr 0#5) = 0#64 :=
          (hcpu2.readReg64 .x0).trans (hx0_sf1.trans (by simp [hc0]))
        have hx19_2' : s2'.readReg64 (.gpr 19#5) = vecPtr :=
          (hcpu2.readReg64 (.gpr 19#5)).trans hx19_sf1
        wp_sym_steps
        refine SepWP.done (by rfl) (by simpa [arm64_norm] using hrun2')
          fun s_ep hcpu_ep hcl_ep hnsp_ep => ?_
        have hpres_1ep : SyscallPreserved sf1 s_ep :=
          syscallPreserved_of_seg hcpu2 hcpu_ep hnsp_ep (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpool_ep : A.pool lb lk sf1 = A.pool lb lk s_ep :=
          (A.pool_transport lb lk sf1 s_ep (poolPreserved_of_syscall hpres_1ep)).symm
        have hpc_ep : s_ep.pc = sprPl13.base + 124#64 := by rw [hcpu_ep.pc_eq]; rfl
        have hrun_ep : s_ep.status = .Running := hcpu_ep.status_eq.trans hrun2'
        have hsp_ep : s_ep.sp = s0.sp - 144#64 :=
          (hcpu_ep.sp_eq.trans (by simp [arm64_norm])).trans hsp2_in
        have hx19_ep : s_ep.readReg64 (.gpr 19#5) = vecPtr :=
          (hcpu_ep.readReg64 (.gpr 19#5)).trans
            ((by simp [arm64_norm] : _ = s2'.readReg64 (.gpr 19#5)).trans hx19_2')
        have hx20_ep : s_ep.readReg64 (.gpr 20#5) = BitVec.ofNat 64 chunk.length := by
          rw [hcpu_ep.readReg64 (.gpr 20#5), hc0]; simp [arm64_norm]
        have hx21_ep : s_ep.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length := by
          rw [hcpu_ep.readReg64 (.gpr 21#5)]; simp [arm64_norm]
        have hvregs_ep : calleeSavedVRegs s_ep = calleeSavedVRegs s0 :=
          hcpu_ep.calleeSavedVRegs.trans
            ((by simp [arm64_norm] : _ = calleeSavedVRegs s2').trans
              (hcpu2.calleeSavedVRegs.trans hvregs_sf1))
        have hpbuf_len : (chunk ++ (List.replicate 32 0#8).drop chunk.length).length = 32 := by
          simp [List.length_append, List.length_drop]; omega
        refine SepWP.weaken_pre
          (by rw [hpool_ep]; (conv => rhs; rw [hchunk_nil, List.append_nil]); sep_entail) <|
          rustSmallProbeRead_epilogue A hext (ptr' := ptr) (st4 := st4) (st5 := st5)
            hstk.2 hcl_ep hpc_ep hrun_ep hsp hsp_ep
            hx19_ep hx20_ep hx21_ep hvregs_ep hpbuf_len
            fun sf _ _ hsp_f hcs_f hpres_epf hfs_epf htr_epf hx0_f hx1_f =>
              have hpres_f : SyscallPreserved s0 sf :=
                hpres_01.trans (hpres_1ep.trans hpres_epf)
              ⟨fun hm_f => Satisfies.mono (by
                simp only [show ((s0.fs.fdBytes desc).drop desc.offset).take 32 = chunk from rfl,
                  hgrew, Bool.false_eq_true, ↓reduceIte]
                rw [pure_sepConj_of_true ⟨hx0_f, hx1_f,
                  hfs_epf.trans (hnsp_ep.2.2.2.2.2.2.trans hfs_01),
                  ⟨htr_epf.trans (hnsp_ep.1.trans htr_01), hpres_f.2.1⟩,
                  hpres_f.1, hpres_f.2.2.brkStart_eq, fun _ => hpres_f⟩]
                sep_entail) hm_f, hsp_f, hcs_f⟩
      · have hc_ne0 : BitVec.ofNat 64 chunk.length ≠ 0#64 := by bv_omega
        have hc_beq0 : (BitVec.ofNat 64 chunk.length == 0#64) = false := beq_false_of_ne hc_ne0
        apply sepWP_seg_rebase_pure (lib := rustStdIoMultiLib) (mpl := SmallProbeReadPlacement.mpl)
          hext 13 (by decide) rustIoBlockNoSvc0_13 hcl_sf1 (mid := sprPl13.base + 104#64)
        intro s2' hcpu2; change SepWP (sprPC13.rebase sprPl13.base (fun _ => none)) _ _ _ _
        have hpc2' : s2'.pc = sprPl13.base + 60#64 := hcpu2.pc_eq.trans hpc_sf1
        have hrun2' : s2'.status = .Running := hcpu2.status_eq.trans hrun_sf1
        have hsp2_in : s2'.sp = s0.sp - 144#64 := hcpu2.sp_eq.trans hsp_sf1_eq
        have hsp2' : s2'.spAligned = true := by
          simp only [State.spAligned]; rw [hsp2_in]; exact s0.spAligned_sub 144#64 hsp
        have hx0_2' : s2'.readReg64 (.gpr 0#5) = BitVec.ofNat 64 chunk.length :=
          (hcpu2.readReg64 .x0).trans hx0_sf1
        have hx19_2' : s2'.readReg64 (.gpr 19#5) = vecPtr :=
          (hcpu2.readReg64 (.gpr 19#5)).trans hx19_sf1
        wp_sym_steps
        refine SepWP.done (by rfl) (by simpa [arm64_norm] using hrun2')
          fun s_cp hcpu_cp hcl_cp hnsp_cp => ?_
        have hpres_1cp : SyscallPreserved sf1 s_cp :=
          syscallPreserved_of_seg hcpu2 hcpu_cp hnsp_cp (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpool_cp : A.pool lb lk sf1 = A.pool lb lk s_cp :=
          (A.pool_transport lb lk sf1 s_cp (poolPreserved_of_syscall hpres_1cp)).symm
        have hpc_cp : s_cp.pc = sprPl13.base + 104#64 := by rw [hcpu_cp.pc_eq]; rfl
        have hrun_cp : s_cp.status = .Running := hcpu_cp.status_eq.trans hrun2'
        have hsp_cp : s_cp.sp = s0.sp - 144#64 :=
          (hcpu_cp.sp_eq.trans (by simp [arm64_norm])).trans hsp2_in
        have hx19_cp : s_cp.readReg64 (.gpr 19#5) = vecPtr :=
          (hcpu_cp.readReg64 (.gpr 19#5)).trans
            ((by simp [arm64_norm] : _ = s2'.readReg64 (.gpr 19#5)).trans hx19_2')
        have hx20_cp : s_cp.readReg64 (.gpr 20#5) = BitVec.ofNat 64 chunk.length := by
          rw [hcpu_cp.readReg64 (.gpr 20#5)]; simp [arm64_norm]
        have hx21_cp : s_cp.readReg64 (.gpr 21#5) = BitVec.ofNat 64 bs.length := by
          rw [hcpu_cp.readReg64 (.gpr 21#5)]; simp [arm64_norm]
        have hvregs_cp : calleeSavedVRegs s_cp = calleeSavedVRegs s0 :=
          hcpu_cp.calleeSavedVRegs.trans
            ((by simp [arm64_norm] : _ = calleeSavedVRegs s2').trans
              (hcpu2.calleeSavedVRegs.trans hvregs_sf1))
        refine SepWP.weaken_pre (by rw [hpool_cp]; sep_entail) <|
          rustSmallProbeRead_copy_and_epilogue A hext hmemcpy
            (ptr' := ptr) (st4 := st4) (st5 := st5)
            hstk.2 hcl_cp hpc_cp hrun_cp hsp
            hsp_cp hx19_cp hx20_cp hx21_cp hvregs_cp (Nat.pos_of_ne_zero hc0) hclen_le32 hle
            fun sf _ _ hsp_f hcs_f hpres_cpf hfs_cpf htr_cpf hx0_f hx1_f =>
              have hpres_f : SyscallPreserved s0 sf :=
                hpres_01.trans (hpres_1cp.trans hpres_cpf)
              ⟨fun hm_f => Satisfies.mono (by
                simp only [show ((s0.fs.fdBytes desc).drop desc.offset).take 32 = chunk from rfl,
                  hgrew, Bool.false_eq_true, ↓reduceIte]
                rw [pure_sepConj_of_true ⟨hx0_f, hx1_f,
                  hfs_cpf.trans (hnsp_cp.2.2.2.2.2.2.trans hfs_01),
                  ⟨htr_cpf.trans (hnsp_cp.1.trans htr_01), hpres_f.2.1⟩,
                  hpres_f.1, hpres_f.2.2.brkStart_eq, fun _ => hpres_f⟩]
                sep_entail) hm_f, hsp_f, hcs_f⟩

end

end VerifiedLibraries.RustStd.Io
