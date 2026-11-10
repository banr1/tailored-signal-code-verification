/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.CType

/-!
# Specification Audit Regression Tests

Regression suite for `#spec_nonvacuous`, `#spec_lint`, and `#spec_smoke`: positive and negative
checks for spatial overlap, contradictory pure preconditions, bounded witness synthesis,
quantified and recursive ghost predicates, fail-closed forced-overlap queries, `c_spec` /
`rust_spec` / `c_type_spec` lowering, `oom_when` contracts, and nested `stackFrameAt` frames.
-/

@[expose] public section

namespace Testing.SpecAudit

open Arm64 ProofLib

/-! ## Full-Coverage Spec -/

@[simp, arm64_norm] def good_audit_addr : BitVec 64 := 0x70000#64

/-- `good_audit_fn` (5 instructions):
    `ldr x8, [x0]; ldr x9, [x0, #8]; add x8, x8, x9; str x8, [x0]; ret`. -/
def goodAuditCode : FnCode :=
  .atAddr "good_audit_fn" good_audit_addr
    ("f9400008 " ++ -- 0x70000: ldr x8, [x0]
     "f9400409 " ++ -- 0x70004: ldr x9, [x0, #8]
     "8b090108 " ++ -- 0x70008: add x8, x8, x9
     "f9000008 " ++ -- 0x7000c: str x8, [x0]
     "d65f03c0")    -- 0x70010: ret

structure GoodAuditArgs where
  ptr : BitVec 64
  v0  : BitVec 64
  v1  : BitVec 64

def goodAuditSpec : Spec GoodAuditArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.ptr⌝ ∗
    (a.ptr ↦₆₄ a.v0) ∗
    ((a.ptr + 8#64) ↦₆₄ a.v1)
  post := fun a _ _ =>
    (a.ptr ↦₆₄ (a.v0 + a.v1)) ∗
    ((a.ptr + 8#64) ↦₆₄ a.v1)

-- Diagnostic commands (never error the build) and strict assertions:
#spec_nonvacuous goodAuditSpec
#spec_nonvacuous! goodAuditSpec
#spec_lint goodAuditSpec
#spec_lint! goodAuditSpec
#spec_smoke goodAuditCode goodAuditSpec
#spec_smoke! goodAuditCode goodAuditSpec

theorem goodAudit_ok (prog : Program) (h_code : goodAuditCode.holds prog) :
    subroutine_ok prog good_audit_addr goodAuditSpec := by
  wp_init a s0
  wp_steps
  wp_done

/-! ## Overlapping Frame and Contradictory Pure Specs -/

structure OverlapArgs where
  v0 : BitVec 64
  v1 : BitVec 64

/-- Spec with a 64-byte `stackFrame s0 64` (`[s0.sp - 64, s0.sp)`) overlapping an explicit stack
    slot `(s0.sp - 32#64) ↦₆₄ a.v0` (a frame that silently aliases a caller-visible cell). -/
def overlappingFrameSpec : Spec OverlapArgs where
  pre := fun a s0 =>
    stackFrame s0 64 ∗
    ((s0.sp - 32#64) ↦₆₄ a.v0) ∗
    ((s0.sp - 24#64) ↦₆₄ a.v1)
  post := fun _ _ _ => emp

-- Non-failing diagnostic command logs FLAGGED via logInfo:
#spec_nonvacuous overlappingFrameSpec

-- Strict check confirms that `#spec_nonvacuous!` flags the overlapping spatial regions:
/--
error: [spec_nonvacuous] FLAGGED (overlappingFrameSpec):
  - overlapping spatial regions on `s0.sp`: `memRegion (s0.sp - 64#64)
  64` ([s0.sp - 64, +64)) and `(s0.sp - 32#64) ↦₆₄ a.v0` ([s0.sp - 32, +8))
  - overlapping spatial regions on `s0.sp`: `memRegion (s0.sp - 64#64)
  64` ([s0.sp - 64, +64)) and `(s0.sp - 24#64) ↦₆₄ a.v1` ([s0.sp - 24, +8))
-/
#guard_msgs (error, drop info) in
#spec_nonvacuous! overlappingFrameSpec

/-- Spec with contradictory pure constraints (`x < 10` and `20 ≤ x`). -/
def contradictoryPureSpec : Spec (BitVec 64) where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x ∧ BitVec.ult x 10#64 ∧ BitVec.ule 20#64 x⌝
  post := fun _ _ _ => emp

#spec_nonvacuous contradictoryPureSpec

/--
error: [spec_nonvacuous] FLAGGED (contradictoryPureSpec):
  - contradictory pure precondition (pure hypotheses prove `False`)
-/
#guard_msgs (error, drop info) in
#spec_nonvacuous! contradictoryPureSpec

/-! ## Auto-Bound Identifier Typo -/

-- With `autoImplicit := false`, a misspelled identifier such as `stackFrame64` (instead of
-- `stackFrame s0 64`) is rejected immediately instead of silently becoming an implicit parameter.
/--
error: Unknown identifier `stackFrame64`
-/
#guard_msgs (error) in
def typoAutoImplicitSpec : Spec Unit where
  pre := fun _ s0 => stackFrame64 s0
  post := fun _ _ _ => emp

/-! ## Guard-Only Spec -/

@[simp, arm64_norm] def guard_only_addr : BitVec 64 := 0x70100#64

/-- `guard_only_fn` (10 instructions):
    Checks `cbz x0, .Lerr` (returning `-2` / `0xfffffffffffffffe` in 3 instructions);
    on the non-NULL path (7 instructions), loads `[x0]` and `[x0, #8]`, stores their sum,
    and returns `0`. -/
def guardOnlyAuditCode : FnCode :=
  .atAddr "guard_only_fn" guard_only_addr
    ("b40000e0 " ++ -- 0x70100: cbz x0, 0x7011c (+28)
     "f9400008 " ++ -- 0x70104: ldr x8, [x0]
     "f9400409 " ++ -- 0x70108: ldr x9, [x0, #8]
     "8b090108 " ++ -- 0x7010c: add x8, x8, x9
     "f9000008 " ++ -- 0x70110: str x8, [x0]
     "d2800000 " ++ -- 0x70114: mov x0, #0
     "d65f03c0 " ++ -- 0x70118: ret
     "92800020 " ++ -- 0x7011c: mov x0, #-2
     "d65f03c0 " ++ -- 0x70120: ret
     "d503201f")    -- 0x70124: nop

structure GuardOnlyArgs where
  strm : BitVec 64

/-- Guard-only spec that pins `strm = 0#64` in the precondition and only verifies the error return. -/
def guardOnlyAuditSpec : Spec GuardOnlyArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.strm ∧ a.strm = 0#64⌝
  post := fun _ _ sf =>
    ⌜sf.readReg64 .x0 = 0xfffffffffffffffe#64⌝

#spec_lint guardOnlyAuditSpec

/--
error: [spec_lint] FLAGGED (guardOnlyAuditSpec):
  - [input-pinned-null] precondition pins input to NULL/0 (`a.strm = 0#64`)
-/
#guard_msgs (error, drop info) in
#spec_lint! guardOnlyAuditSpec

theorem guardOnlyAudit_ok (prog : Program) (h_code : guardOnlyAuditCode.holds prog) :
    subroutine_ok prog guard_only_addr guardOnlyAuditSpec := by
  wp_init a s0
  rcases a with ⟨strm⟩
  subst ‹strm = 0#64›
  wp_steps
  wp_done

/-! ## Missing Points-To Cell and Missing Step Rule in `#spec_smoke` -/

@[simp, arm64_norm] def missing_cell_addr : BitVec 64 := 0x70200#64

/-- `missing_cell_fn` (4 instructions):
    Loads `[x0]` (`a.strm`) and `[x0, #64]` (`a.strm + 64#64`), adds them, and returns. -/
def missingCellAuditCode : FnCode :=
  .atAddr "missing_cell_fn" missing_cell_addr
    ("f9400008 " ++ -- 0x70200: ldr x8, [x0]
     "f9402009 " ++ -- 0x70204: ldr x9, [x0, #64]
     "8b090100 " ++ -- 0x70208: add x0, x8, x9
     "d65f03c0")    -- 0x7020c: ret

structure MissingCellArgs where
  strm : BitVec 64
  v0   : BitVec 64

/-- Buggy spec that owns `a.strm ↦₆₄ a.v0` but forgets `(a.strm + 64#64) ↦₆₄ ...`. -/
def missingCellAuditSpec : Spec MissingCellArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.strm⌝ ∗
    (a.strm ↦₆₄ a.v0)
  post := fun a _ _ =>
    (a.strm ↦₆₄ a.v0)

-- Non-failing diagnostic command logs the missing cell via logInfo without breaking the build:
#spec_smoke missingCellAuditCode missingCellAuditSpec

-- Strict check verifies the exact stuck PC, instruction, and missing cell `a.strm + 64#64`:
/--
error: [spec_smoke] STUCK (missingCellAuditCode missingCellAuditSpec): 0/1 path(s) reached return (0 closed postcondition)
  - path 1 (unconditional): STUCK at PC 0x70204#64 (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 9#5)
  (AddrMode.Offset (Reg.gpr 0#5) 64#64)): no cell at a.strm + 64#64 in a.strm ↦₆₄ a.v0
-/
#guard_msgs (error, drop info) in
#spec_smoke! missingCellAuditCode missingCellAuditSpec

/-- `ldr h0, [x1, #2]; ret`: a 2-byte SIMD load (no step rule exists, so the smoke run gets stuck). -/
def simdH16AuditCode : FnCode :=
  .atAddr "simd_h16_fn" missing_cell_addr
    ("7d400420 " ++ -- 0x70200: ldr h0, [x1, #2]
     "d65f03c0")    -- 0x70204: ret

/-- Owns the 4 bytes `[a.1, a.1 + 4)`, which contain the 2 bytes `[a.1 + 2, a.1 + 4)` read. -/
def simdH16AuditSpec : Spec (BitVec 64 × BitVec 32) where
  pre := fun a s0 => ⌜s0.readReg64 .x1 = a.1⌝ ∗ (a.1 ↦₃₂ a.2)
  post := fun a _ _ => (a.1 ↦₃₂ a.2)

-- `[a.1 + 2, a.1 + 4)` lies inside the `↦₃₂` block, so the diagnosis must report the missing step
-- rule, not `no cell at a.1 + 2#64`.
/--
error: [spec_smoke] STUCK (simdH16AuditCode simdH16AuditSpec): 0/1 path(s) reached return (0 closed postcondition)
  - path 1 (unconditional): STUCK at PC 0x70200#64 (Instr.ldrSimd SimdMemSize.H16 (0#5)
  (AddrMode.Offset (Reg.gpr 1#5)
    2#64)): wp_step: no step rule succeeded for instruction `Instr.ldrSimd SimdMemSize.H16 (0#5)
  (AddrMode.Offset (Reg.gpr 1#5)
    2#64)` (full: `Instr.ldrSimd SimdMemSize.H16 (0#5) (AddrMode.Offset (Reg.gpr 1#5) 2#64)`) at PC `459264#64`
spatial context points-to atoms: a.fst ↦₃₂ a.snd
(detail: `simp` made no progress)
-/
#guard_msgs (error, drop info) in
#spec_smoke! simdH16AuditCode simdH16AuditSpec

/-! ## Bounded `#spec_nonvacuous!` Mode and Read-Only (`↦ᵣ`) Spatial Atoms -/

structure BoundedNonvacArgs where
  dst    : BitVec 64
  roBase : BitVec 64
  nmemb  : BitVec 64
  sz     : BitVec 64
  old    : BitVec 64

/-- Spec combining a writable cell `a.dst ↦₆₄ a.old`, a read-only `.rodata` slice
    `a.roBase ↦ᵣ [1#8, 2#8, 3#8, 4#8]`, and a nonlinear 64-bit product constraint
    `a.nmemb * a.sz ≠ 0#64` (exercising `#spec_nonvacuous! (config := { smallBounds := true })`). -/
def boundedRoAuditSpec : Spec BoundedNonvacArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.dst ∧
     s0.readReg64 .x1 = a.roBase ∧
     a.nmemb * a.sz ≠ 0#64⌝ ∗
    (a.dst ↦₆₄ a.old) ∗
    (a.roBase ↦ᵣ [1#8, 2#8, 3#8, 4#8])
  post := fun a _ _ =>
    (a.dst ↦₆₄ a.old) ∗
    (a.roBase ↦ᵣ [1#8, 2#8, 3#8, 4#8])

#spec_nonvacuous! (config := { smallBounds := true }) boundedRoAuditSpec
#spec_lint! boundedRoAuditSpec

/-- Contradictory nonlinear pure precondition (`x * x = 2#8` has no solution in `BitVec 8`):
    both default `#spec_nonvacuous!` and `smallBounds := true` refute it via `bv_decide` when no
    concrete witness exists. -/
def nonlinVacuousSpec : Spec (BitVec 8) where
  pre := fun x _ => ⌜x * x = 2#8⌝
  post := fun _ _ _ => emp

/--
error: [spec_nonvacuous] FLAGGED (nonlinVacuousSpec):
  - contradictory pure precondition (pure hypotheses prove `False`)
-/
#guard_msgs (error, drop info) in
#spec_nonvacuous! nonlinVacuousSpec

/--
error: [spec_nonvacuous] FLAGGED (nonlinVacuousSpec):
  - contradictory pure precondition (pure hypotheses prove `False`)
-/
#guard_msgs (error, drop info) in
#spec_nonvacuous! (config := { smallBounds := true }) nonlinVacuousSpec

/-! ## `#spec_lint` Checks for Aliased Allocations and Retained Freed Pointers -/

structure AliasedAllocArgs where
  tif      : BitVec 64
  old0     : BitVec 64
  old1     : BitVec 64
  newPtrFn : BitVec 64 → BitVec 64

/-- Buggy multi-allocation spec where two consecutive 8-byte allocations both pass `nmemb = 1#64`
    to an unindexed `newPtrFn : BitVec 64 → BitVec 64`, aliasing the two pointer fields in `post`
    to `a.newPtrFn 1#64`. -/
def aliasedAllocPtrsAuditSpec : Spec AliasedAllocArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.tif⌝ ∗
    (a.tif ↦₆₄ a.old0) ∗
    ((a.tif + 8#64) ↦₆₄ a.old1)
  post := fun a _ _ =>
    (a.tif ↦₆₄ a.newPtrFn 1#64) ∗
    ((a.tif + 8#64) ↦₆₄ a.newPtrFn 1#64)

/--
error: [spec_lint] FLAGGED (aliasedAllocPtrsAuditSpec):
  - [post-aliased-alloc] postcondition aliases multiple pointer cells (`a.tif ↦₆₄
  a.newPtrFn 1#64` and `(a.tif + 8#64) ↦₆₄ a.newPtrFn 1#64`) to the same symbolic allocation `a.newPtrFn 1#64`
-/
#guard_msgs (error, drop info) in
#spec_lint! aliasedAllocPtrsAuditSpec

/-- Empty 0-byte `pointsToBytes` prefix alongside a symbolic-length `memRegion` at the same base
    must not trigger a false-positive `post-aliased-alloc`. -/
def emptyPrefixRegionAuditSpec : Spec GoodAuditArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.ptr⌝ ∗
    memRegion a.ptr a.v0.toNat
  post := fun a _ _ =>
    (a.ptr ↦ₛ []) ∗
    memRegion a.ptr a.v0.toNat

#spec_lint! emptyPrefixRegionAuditSpec

/-- Non-empty `pointsToBytes` overlapping a symbolic-length `memRegion` at the same base offset 0
    must be flagged by `post-aliased-alloc`. -/
def nonEmptyOverlapRegionAuditSpec : Spec GoodAuditArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.ptr⌝ ∗
    memRegion a.ptr a.v0.toNat
  post := fun a _ _ =>
    (a.ptr ↦ₛ [0#8]) ∗
    memRegion a.ptr a.v0.toNat

/--
error: [spec_lint] FLAGGED (nonEmptyOverlapRegionAuditSpec):
  - [post-aliased-alloc] postcondition contains aliased/overlapping spatial blocks at `a.ptr` (`a.ptr ↦ₛ
  [0#8]` and `memRegion a.ptr a.v0.toNat`)
-/
#guard_msgs (error, drop info) in
#spec_lint! nonEmptyOverlapRegionAuditSpec

/-- Buggy deallocation spec whose name indicates `free` while its postcondition retains ownership
    of the freed block `a.ptr ↦₆₄ a.v0`. -/
def freeRetainsOwnershipAuditSpec : Spec GoodAuditArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.ptr⌝ ∗
    (a.ptr ↦₆₄ a.v0)
  post := fun a _ _ =>
    (a.ptr ↦₆₄ a.v0)

/--
error: [spec_lint] FLAGGED (freeRetainsOwnershipAuditSpec):
  - [post-retains-freed-ptr] deallocation spec `freeRetainsOwnershipAuditSpec` leaves freed pointer ownership (`a.ptr ↦₆₄
  a.v0`) in `post`
-/
#guard_msgs (error, drop info) in
#spec_lint! freeRetainsOwnershipAuditSpec

/-- Non-deallocation specs whose names contain `freeze` or `closest` must not trigger
    `post-retains-freed-ptr` false positives. -/
def freeze_spec : Spec GoodAuditArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.ptr⌝ ∗
    (a.ptr ↦₆₄ a.v0)
  post := fun a _ _ =>
    (a.ptr ↦₆₄ a.v0)

def closest_point_spec : Spec GoodAuditArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.ptr⌝ ∗
    (a.ptr ↦₆₄ a.v0)
  post := fun a _ _ =>
    (a.ptr ↦₆₄ a.v0)

#spec_lint! freeze_spec
#spec_lint! closest_point_spec

/-- Well-formed call-site-indexed multi-allocation spec using `ProofLib.Allocator` (`allocSeq`)
    and ownership-consuming `libcFreeSpec` both pass `#spec_lint!` with zero warnings. -/
structure IndexedAllocArgs where
  tif   : BitVec 64
  old0  : BitVec 64
  old1  : BitVec 64
  alloc : ProofLib.Allocator

def indexedAllocAuditSpec : Spec IndexedAllocArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.tif⌝ ∗
    (a.tif ↦₆₄ a.old0) ∗
    ((a.tif + 8#64) ↦₆₄ a.old1)
  post := fun a _ _ =>
    (a.tif ↦₆₄ a.alloc.ptr 0 8#64) ∗
    ((a.tif + 8#64) ↦₆₄ a.alloc.ptr 1 8#64) ∗
    a.alloc.allocSeq 0 [(8#64, 8), (8#64, 8)]

#spec_lint! indexedAllocAuditSpec
#spec_lint! libcFreeSpec
#spec_lint! freeRegionSpec

/-! ## Synthetic `c_type_spec` Non-Vacuity and Lint Checks -/

section SyntheticCTypeSpecAudit
open Arm64.CType

structure SyntheticParserState where
  pos     : BitVec 32
  toknext : BitVec 32
  toksuper : BitVec 32

def syntheticParserAt (p : BitVec 64) (st : SyntheticParserState) : SepProp :=
  (p ↦₃₂ st.pos) ∗ ((p + 4#64) ↦₃₂ st.toknext) ∗ ((p + 8#64) ↦₃₂ st.toksuper)

def SyntheticParserT : SemType SyntheticParserState where
  tyName := "struct synthetic_parser"
  interp := syntheticParserAt
  pureWf := fun p _ => p ≠ 0#64 ∧ p.toNat + 12 < 2 ^ 64

c_type_spec syntheticParserInitSpec (p : ptr) (ghost st : SyntheticParserState) : (ret : void) where
  c_arg p : MutRef SyntheticParserT st ⇝ { pos := 0#32, toknext := 0#32, toksuper := 0xffffffff#32 }
  stack16

#spec_nonvacuous! syntheticParserInitSpec
#spec_lint! syntheticParserInitSpec

end SyntheticCTypeSpecAudit

/-! ## Split-Frame Wrapper and Multi-Parameter `pureHyps` Checks -/

/-- Nested separation-logic header wrapper exercising multi-round unfolding and `flattenSepConj`. -/
def splitFrameHeader (buf content : BitVec 64) (use32 size32 : BitVec 32)
    (allocWord contentIO : BitVec 64) : SepProp :=
  (buf ↦₆₄ content) ∗
  ((buf + 8#64) ↦₃₂ use32) ∗
  ((buf + 12#64) ↦₃₂ size32) ∗
  ((buf + 16#64) ↦₆₄ allocWord) ∗
  ((buf + 24#64) ↦₆₄ contentIO)

/-- Split-frame wrapper containing `pointsToBytes` (`↦ₛ`) with `List.take` / `List.drop` payloads
    that must not be unfolded by unconstrained `whnf` during `flattenSepConj`. -/
def wrapperFrame_split_8 (buf content contentIO : BitVec 64) (use32 size32 : BitVec 32)
    (allocWord start use size : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  splitFrameHeader buf content use32 size32 allocWord contentIO ∗
  (contentIO ↦ₛ bs.take start.toNat) ∗
  (content ↦ₛ (bs.drop start.toNat).take use.toNat) ∗
  memRegion (content + use) (size.toNat - start.toNat - use.toNat)

structure SplitFrameBv64Args where
  buf       : BitVec 64
  contentIO : BitVec 64
  content   : BitVec 64
  str       : BitVec 64
  newData   : BitVec 64
  start     : BitVec 64
  len       : BitVec 64
  use       : BitVec 64
  size      : BitVec 64
  use32     : BitVec 32
  size32    : BitVec 32
  allocWord : BitVec 64
  reqSize   : BitVec 64
  allocSize : BitVec 64
  bs        : List (BitVec 8)
  addBs     : List (BitVec 8)

/-- Multi-parameter split-frame spec with free `BitVec 64` variables (`start`, `len`, `use`, `size`)
    in `pureHyps` and `wrapperFrame_split_8` (`pointsToBytes` + `List.take`). -/
def splitFrameBv64PureAuditSpec : Spec SplitFrameBv64Args where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.buf ∧
      s0.readReg64 .x1 = a.str ∧
      s0.readReg32 .x2 = a.len.truncate 32 ∧
      a.buf ≠ 0#64 ∧ a.str ≠ 0#64 ∧ a.contentIO ≠ 0#64 ∧ a.content ≠ 0#64 ∧ a.newData ≠ 0#64 ∧
      a.allocWord.truncate 32 = 3#32 ∧
      a.start ≠ 0#64 ∧ a.len ≠ 0#64 ∧
      a.content = a.contentIO + a.start ∧
      a.bs.length = (a.start + a.use).toNat ∧
      a.addBs.length = a.len.toNat ∧
      a.start + a.use ≤ a.size ∧
      (a.size - a.start).ult (a.use + a.len) = true ∧
      a.use ≤ a.use + a.len ∧
      (a.use + a.len).ult 0x7fffffff#64 = true ∧
      a.size.ult 0x7fffffff#64 = true ∧
      (((a.size <<< 1#64) ≤ (a.use + a.len + 0x64#64) ∧
          a.reqSize = a.use + a.len + 0x64#64) ∨
        ((a.use + a.len + 0x64#64) < (a.size <<< 1#64) ∧
          a.reqSize = a.size <<< 1#64)) ∧
      a.reqSize ≤ a.allocSize ∧
      a.allocSize.toNat ≤ 65536⌝ ∗
    stackFrame s0 80 ∗
    wrapperFrame_split_8 a.buf a.content a.contentIO a.use32 a.size32
      a.allocWord a.start a.use a.size a.bs ∗
    (a.str ↦ₛ a.addBs) ∗
    memRegion a.newData a.allocSize.toNat
  post := fun _ _ _ => emp

#spec_nonvacuous! (config := { smallBounds := true }) splitFrameBv64PureAuditSpec

/-- Buffer-resize-style multi-parameter spec with chained 32-bit
    inequalities (`use32 ≤ size32`, `size32.ult req32 = true`) and `newCap` disjunction. -/
structure ResizeGrowAuditArgs where
  buf       : BitVec 64
  content   : BitVec 64
  req32     : BitVec 32
  use32     : BitVec 32
  size32    : BitVec 32
  allocWord : BitVec 64
  newData   : BitVec 64
  newCap    : BitVec 64
  allocSize : BitVec 64
  bs        : List (BitVec 8)

def resizeGrowValidAuditSpec : Spec ResizeGrowAuditArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.buf ∧
      s0.readReg32 .x1 = a.req32 ∧
      a.buf ≠ 0#64 ∧ a.content ≠ 0#64 ∧ a.newData ≠ 0#64 ∧
      a.bs.length = a.use32.toNat ∧
      a.use32 ≤ a.size32 ∧
      a.size32.ult a.req32 = true ∧
      a.allocWord.truncate 32 ≠ 2#32 ∧
      a.allocWord.truncate 32 ≠ 3#32 ∧
      a.size32.ult 0x7fffffff#32 = true ∧
      a.req32.ult 0xfffffff5#32 = true ∧
      (((a.size32 <<< 1#64) ≤ (a.req32 + 10#32) ∧
          a.newCap = (a.req32 + 10#32).zeroExtend 64) ∨
        ((a.req32 + 10#32) < (a.size32 <<< 1#64) ∧
          a.newCap = (a.size32 <<< 1#64).zeroExtend 64)) ∧
      a.use32.toNat ≤ a.newCap.toNat ∧
      a.newCap ≤ a.allocSize ∧
      a.allocSize.toNat ≤ 65536⌝ ∗
    stackFrame s0 48 ∗
    splitFrameHeader a.buf a.content a.use32 a.size32 a.allocWord 0#64 ∗
    (a.content ↦ₛ a.bs) ∗
    memRegion (a.content + a.use32.zeroExtend 64) (a.size32.toNat - a.use32.toNat) ∗
    memRegion a.newData a.allocSize.toNat
  post := fun _ _ _ => emp

#spec_nonvacuous! (config := { smallBounds := true }) resizeGrowValidAuditSpec

/-- Buffer-shrink-style spec with `len32 ≤ use32 ≤ size32` and two
    dependent byte-slice lengths (`bsDrop.length = len32.toNat`, `bsKeep.length = use32.toNat - len32.toNat`). -/
structure ShrinkValidAuditArgs where
  buf       : BitVec 64
  content   : BitVec 64
  len32     : BitVec 32
  use32     : BitVec 32
  size32    : BitVec 32
  allocWord : BitVec 64
  bsDrop    : List (BitVec 8)
  bsKeep    : List (BitVec 8)

def shrinkValidAuditSpec : Spec ShrinkValidAuditArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.buf ∧
      s0.readReg32 .x1 = a.len32 ∧
      a.buf ≠ 0#64 ∧ a.content ≠ 0#64 ∧
      a.len32 ≠ 0#32 ∧
      a.len32 ≤ a.use32 ∧
      a.use32 ≤ a.size32 ∧
      a.allocWord.truncate 32 ≠ 3#32 ∧
      a.bsDrop.length = a.len32.toNat ∧
      a.bsKeep.length = a.use32.toNat - a.len32.toNat ∧
      a.size32.toNat ≤ 65536⌝ ∗
    stackFrame s0 32 ∗
    splitFrameHeader a.buf a.content a.use32 a.size32 a.allocWord 0#64 ∗
    (a.content ↦ₛ a.bsDrop) ∗
    ((a.content + a.len32.zeroExtend 64) ↦ₛ a.bsKeep) ∗
    memRegion (a.content + a.use32.zeroExtend 64) (a.size32.toNat - a.use32.toNat)
  post := fun _ _ _ => emp

#spec_nonvacuous! (config := { smallBounds := true }) shrinkValidAuditSpec

/-- Contradictory `s0.sp` bitwise mask (`s0.sp = 0x80000 ∧ s0.sp &&& 0x80000 = 0`)
    must be flagged as vacuous even when `smallBounds := true`. -/
def spSkipVacuousSpec : Spec (BitVec 64) where
  pre := fun p s0 =>
    ⌜s0.readReg64 .x0 = p ∧
      s0.sp = 0x80000#64 ∧
      s0.sp &&& 0x80000#64 = 0#64⌝ ∗
    (p ↦₆₄ 1#64)
  post := fun _ _ _ => emp

/-- info: [spec_nonvacuous] FLAGGED (spSkipVacuousSpec):
  - contradictory pure precondition (pure hypotheses prove `False`) -/
#guard_msgs in
#spec_nonvacuous (config := { smallBounds := true }) spSkipVacuousSpec

/-- Regression test: contradictory 32-bit (`readReg32`) and 64-bit (`readReg64`) bindings on the
    same register must be flagged under `smallBounds := true`. -/
def reg32WideningVacuousSpec : Spec (BitVec 32) where
  pre := fun len32 s0 =>
    ⌜s0.readReg32 .x0 = len32 ∧
      (s0.readReg64 .x0).truncate 32 = 99#32 ∧
      len32 = 1#32⌝
  post := fun _ _ _ => emp

/-- info: [spec_nonvacuous] FLAGGED (reg32WideningVacuousSpec):
  - contradictory pure precondition (pure hypotheses prove `False`) -/
#guard_msgs in
#spec_nonvacuous (config := { smallBounds := true }) reg32WideningVacuousSpec

/-! ## Elaboration-Time Hex Word Literal (`elabHexWordsStrLit` / `hex_words%`) Regression Tests -/

/-- Positive test: single string literal and `++`-concatenated string literals elaborate directly
    to `List (BitVec 32)` at elaboration time and agree with `hex_words%`. -/
def hexElabSingleTest : FnCode :=
  .ofFn "hex_elab_test" "d2800540 d65f03c0"

def hexElabConcatTest : FnCode :=
  .ofFn "hex_elab_test" ("d2800540 " ++ "d65f03c0")

#guard hexElabSingleTest.hex == [0xd2800540#32, 0xd65f03c0#32]
#guard hexElabConcatTest.hex == (hex_words% ("d2800540 " ++ "d65f03c0"))

/-- error: Type mismatch
  "d2800540 ".append "d65f03c0"
has type
  String
but is expected to have type
  List (BitVec 32) -/
#guard_msgs in
def hexElabNonLiteralNegTest : List (BitVec 32) :=
  String.append "d2800540 " "d65f03c0"

/-! Kernel-checked faithfulness: the words produced by the elaborator (which runs the compiled
`parseHexWords`) are equal, by kernel `decide` / `rfl`, to the kernel's own evaluation of
`Program.parseHexWords` on the same literal (covering comments, `0x`, uppercase, `++`, and the
empty string); literals with a trailing partial word are rejected at elaboration time. -/

example : ("d2800540 d65f03c0" : List (BitVec 32)) =
    Program.parseHexWords "d2800540 d65f03c0" := by decide
example : (("d2800540 " ++ "D65F03C0") : List (BitVec 32)) =
    Program.parseHexWords ("d2800540 " ++ "D65F03C0") := by decide
example : ("0xd2800540 -- mov x0, #42\n// ret\nd65f03c0, 1f2003d5" : List (BitVec 32)) =
    Program.parseHexWords "0xd2800540 -- mov x0, #42\n// ret\nd65f03c0, 1f2003d5" := by decide
/-- error: Hex word string literal has 12 hex digits, which is not a multiple of 8 (each 32-bit ARM64 instruction word requires 8 hex digits) -/
#guard_msgs in
example : List (BitVec 32) := "d2800540 d65f"

/-- error: Hex word string literal has 7 hex digits, which is not a multiple of 8 (each 32-bit ARM64 instruction word requires 8 hex digits) -/
#guard_msgs in
example : List (BitVec 32) := hex_words% ("d28005 " ++ "4")
example : ("" : List (BitVec 32)) = Program.parseHexWords "" := by decide

/-- The elaborator does not affect ordinary `List (BitVec 32)` appends or `String` literals. -/
example : ([1#32] ++ [2#32] : List (BitVec 32)) = [1#32, 2#32] := rfl
example : ("ab" ++ "cd" : String) = "abcd" := by decide

/-- Regression test: alignment masks on spatial base pointers (`ptr &&& 15#64 = 0#64`) and
    LHS-spatial dependent equalities (`ptr = aliasPtr`) must find a non-null witness in
    `tryBoundedPureWitness?` without pinning `ptr` to `0#64` or dropping `aliasPtr`. -/
structure AlignedSpatialDepEqArgs where
  ptr      : BitVec 64
  aliasPtr : BitVec 64
  bs       : List (BitVec 8)
  len32    : BitVec 32

def alignedSpatialDepEqAuditSpec : Spec AlignedSpatialDepEqArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.ptr ∧
      a.ptr ≠ 0#64 ∧
      a.ptr &&& 15#64 = 0#64 ∧
      a.ptr = a.aliasPtr ∧
      a.aliasPtr ≠ 0#64 ∧
      a.len32 ≠ 0#32 ∧
      a.bs.length = a.len32.toNat ∧
      a.len32.toNat ≤ 64⌝ ∗
    (a.ptr ↦ₛ a.bs)
  post := fun _ _ _ => emp

/-- info: [spec_nonvacuous] OK (alignedSpatialDepEqAuditSpec): 1 spatial block(s) pairwise disjoint, 9 pure hypothesis(es) non-contradictory. -/
#guard_msgs in
#spec_nonvacuous! (config := { smallBounds := true }) alignedSpatialDepEqAuditSpec

/-- Regression test: bitmask constraints (`(flags &&& mask) != 0` and `(flags &&& mask2) = 0`)
    combined with multiple spatial base pointers bound only via `s0.readReg64` must synthesize a
    concrete witness in `tryBoundedPureWitness?` and substitute distinct page-aligned base
    addresses so pairwise `forcedOverlap` checks close by `bv_decide` without falling back to
    `bv_arith`. -/
structure BitmaskMultiSpatialArgs where
  tif   : BitVec 64
  buf   : BitVec 64
  flags : BitVec 32
  cc    : Nat

def bitmaskMultiSpatialAuditSpec : Spec BitmaskMultiSpatialArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.tif ∧
      s0.readReg64 .x1 = a.buf ∧
      (a.flags &&& 0x400#32) != 0#32 ∧
      (a.flags &&& 0x8000#32) = 0#32 ∧
      a.cc > 0 ∧
      a.cc ≤ 16 ∧
      BitVec.ofNat 64 a.cc = 1#64⌝ ∗
    ((a.tif + 16#64) ↦₃₂ a.flags) ∗
    (a.buf ↦ₛ List.replicate a.cc 0#8)
  post := fun _ _ _ => emp

/-- info: [spec_nonvacuous] OK (bitmaskMultiSpatialAuditSpec): 2 spatial block(s) pairwise disjoint, 8 pure hypothesis(es) non-contradictory. -/
#guard_msgs in
#spec_nonvacuous! (config := { smallBounds := true }) bitmaskMultiSpatialAuditSpec

/-- Negative regression test: contradictory bitmask constraints (`(flags &&& mask) != 0` and
    `(flags &&& mask) = 0` on the same mask) must be rejected by `#spec_nonvacuous`. -/
def contradictoryBitmaskAuditSpec : Spec (BitVec 32) where
  pre := fun flags s0 =>
    ⌜s0.readReg32 .x0 = flags ∧
      (flags &&& 0x400#32) != 0#32 ∧
      (flags &&& 0x400#32) = 0#32⌝
  post := fun _ _ _ => emp

/-- info: [spec_nonvacuous] FLAGGED (contradictoryBitmaskAuditSpec):
  - contradictory pure precondition (pure hypotheses prove `False`) -/
#guard_msgs in
#spec_nonvacuous (config := { smallBounds := true }) contradictoryBitmaskAuditSpec

/-- Regression test: user-defined `Prop` conjunction predicates (`UserStateLengthsOk`), user-defined
    `Bool` helper predicates (`userModeValid (st.mode.truncate 32) = true`), and zero-literal
    non-spatial struct fields (`st.winPtr = 0#64`) must unfold and synthesize a witness in
    `tryBoundedPureWitness?` without falling back to `bv_arith` across large byte-slice blocks. -/
structure UserAuditState where
  ptr    : BitVec 64
  winPtr : BitVec 64
  mode   : BitVec 64
  b1     : List (BitVec 8)
  b2     : List (BitVec 8)

def UserAuditState.LengthsOk (st : UserAuditState) : Prop :=
  st.b1.length = 40 ∧ st.b2.length = 24

def userModeValid (m : BitVec 32) : Bool :=
  BitVec.ule 16180#32 m && BitVec.ule m 16209#32

def userPropAndZeroFieldAuditSpec : Spec UserAuditState where
  pre := fun st s0 =>
    ⌜s0.readReg64 .x0 = st.ptr ∧
      st.ptr ≠ 0#64 ∧
      st.winPtr = 0#64 ∧
      st.LengthsOk ∧
      userModeValid (st.mode.truncate 32) = true⌝ ∗
    ((st.ptr + 0#64) ↦₆₄ st.winPtr) ∗
    ((st.ptr + 8#64) ↦₆₄ st.mode) ∗
    ((st.ptr + 16#64) ↦ₛ st.b1) ∗
    ((st.ptr + 64#64) ↦ₛ st.b2)
  post := fun _ _ _ => emp

/-- info: [spec_nonvacuous] OK (userPropAndZeroFieldAuditSpec): 4 spatial block(s) pairwise disjoint, 7 pure hypothesis(es) non-contradictory. -/
#guard_msgs in
#spec_nonvacuous! (config := { smallBounds := true }) userPropAndZeroFieldAuditSpec

/-- Negative regression test: a contradictory length constraint inside a user-defined `Prop`
    conjunction predicate (`st.LengthsOk` combined with `st.b1.length = 8`) must be unfolded by
    `splitProgress` and flagged as a contradictory pure precondition by `#spec_nonvacuous`. -/
def contradictoryUserPropAuditSpec : Spec UserAuditState where
  pre := fun st s0 =>
    ⌜s0.readReg64 .x0 = st.ptr ∧
      st.LengthsOk ∧
      st.b1.length = 8⌝
  post := fun _ _ _ => emp

/-- info: [spec_nonvacuous] FLAGGED (contradictoryUserPropAuditSpec):
  - contradictory pure precondition (pure hypotheses prove `False`) -/
#guard_msgs in
#spec_nonvacuous (config := { smallBounds := true }) contradictoryUserPropAuditSpec

/-! ## Built-In `base` Quantification (`BaseSpec`) -/

/-- Positive regression test: `c_spec` mentioning `base` automatically produces a `BaseSpec`
    (`BitVec 64 → Spec α`) that passes `#spec_lint!` and `#spec_nonvacuous!`. -/
c_spec baseRelocAuditSpec (p : ptr) (ghost oldVal : u64) : (ret : u64) where
  requires (p ↦₆₄ oldVal)
  ensures  ⌜ret = base + 0x100#64⌝ ∗ (p ↦₆₄ (base + 0x100#64))

example : BaseSpec (BitVec 64 × BitVec 64) := baseRelocAuditSpec

/-- info: [spec_lint] OK (baseRelocAuditSpec): no precondition-pinning warnings. -/
#guard_msgs in
#spec_lint! baseRelocAuditSpec

/-- info: [spec_nonvacuous] OK (baseRelocAuditSpec): 1 spatial block(s) pairwise disjoint, 2 pure hypothesis(es) non-contradictory. -/
#guard_msgs in
#spec_nonvacuous! baseRelocAuditSpec

/-- Negative regression test: a `BaseSpec` with overlapping spatial cells in `requires` is
    caught by `#spec_nonvacuous`. -/
c_spec baseRelocOverlapBadSpec (p : ptr) (ghost v1 v2 : u64) : unit where
  requires (p ↦₆₄ v1) ∗ ((p + 4#64) ↦₆₄ v2)
  ensures  (p ↦₆₄ (base + v1)) ∗ ((p + 4#64) ↦₆₄ v2)

/-- info: [spec_nonvacuous] FLAGGED (baseRelocOverlapBadSpec):
  - overlapping spatial regions on `a_1`: `a_1 ↦₆₄ a` ([a_1, +8)) and `(a_1 + 4#64) ↦₆₄ a_rest_1` ([a_1 + 4, +8)) -/
#guard_msgs in
#spec_nonvacuous baseRelocOverlapBadSpec

/-- Regression test: single-field structure shorthand `{ base }` inside `c_spec` must be
    recognized as a free `base` occurrence by `stxMentionsFreeIdent`. -/
structure BaseHolder where
  base : BitVec 64

c_spec baseStructShorthandSpec (p : ptr) (ghost oldVal : u64) : unit where
  requires (p ↦₆₄ oldVal)
  ensures  (p ↦₆₄ ({ base : BaseHolder }.base))

example : BaseSpec (BitVec 64 × BitVec 64) := baseStructShorthandSpec

/-! ## Tuple `List` Witnesses and Complement-Add (`~~~idx + len`) Bounds -/

/-- Positive regression test: `List (BitVec 64 × BitVec 64 × BitVec 16)` ghost variable with
    non-zero length (`children.length = rightKeys.length + 1`) and `~~~idx + len.zeroExtend 64`
    bound must synthesize a concrete witness in `tryBoundedPureWitness?`. -/
rust_spec tupleListAndComplementAddValidSpec
    (nodePtr : ptr) (idx : u64) (ghost len : u16)
    (ghost rightKeys : List (BitVec 64))
    (ghost children : List (BitVec 64 × BitVec 64 × BitVec 16)) : u64
  requires_cond ¬(BitVec.ule 0xc#64 (~~~idx + len.zeroExtend 64)) ∧
                ((~~~idx + len.zeroExtend 64) <<< 3#64) = BitVec.ofNat 64 (8 * rightKeys.length) ∧
                children.length = rightKeys.length + 1
  requires      ((nodePtr + 0xba#64) ↦₁₆ len) ∗
                ((nodePtr + 8#64) ↦₆₄* rightKeys) ∗
                ((nodePtr + 0xc0#64) ↦₆₄* (children.map Prod.fst))
  ensures       ((nodePtr + 0xba#64) ↦₁₆ len) ∗
                ((nodePtr + 8#64) ↦₆₄* rightKeys) ∗
                ((nodePtr + 0xc0#64) ↦₆₄* (children.map Prod.fst))
  returns       nodePtr

/-- info: [spec_nonvacuous] OK (tupleListAndComplementAddValidSpec): 3 spatial block(s) pairwise disjoint, 6 pure hypothesis(es) non-contradictory. -/
#guard_msgs in
#spec_nonvacuous! (config := { smallBounds := true }) tupleListAndComplementAddValidSpec

/-- Negative regression test: contradictory `List` tuple length (`children.length = 1 ∧ children.length = 2`)
    must still be flagged as vacuous under `smallBounds := true`. -/
rust_spec tupleListContradictorySpec
    (nodePtr : ptr)
    (ghost children : List (BitVec 64 × BitVec 64 × BitVec 16)) : u64
  requires_cond children.length = 1 ∧ children.length = 2
  requires      (nodePtr ↦₆₄* (children.map Prod.fst))
  ensures       (nodePtr ↦₆₄* (children.map Prod.fst))
  returns       nodePtr

/-- info: [spec_nonvacuous] FLAGGED (tupleListContradictorySpec):
  - contradictory pure precondition (pure hypotheses prove `False`) -/
#guard_msgs in
#spec_nonvacuous (config := { smallBounds := true }) tupleListContradictorySpec

/-! ## `Nat`-Literal Lower Bounds, `ite`-Defined Ghosts, and Wrapping-Subtraction Lengths -/

/-- Positive regression test (B-tree right-split shape): `6 ≤ idx.toNat` must lower-bound `idx`
    (a `Nat` literal, not a `BitVec` literal), and `mid = if idx = 6 then 5 else 6` must be used as
    a dependent equation even though `rcases` leaves the original ghost tuple inside the `ite`'s
    `Decidable` instance. Otherwise `ins = idx - mid - 1` wraps and `ksL.length = ins.toNat` has no
    small witness, `requireWitness` flags the spec, and large specs fall back to one tactic call
    per block pair. -/
rust_spec wrappingSubLenSplitSpec
    (nodePtr : ptr) (ghost idx mid ins : u64)
    (ghost ksL ksR : List (BitVec 64)) : u64
  requires_cond 6 ≤ idx.toNat ∧ idx.toNat ≤ 11 ∧
                mid = (if idx = 6#64 then 5#64 else 6#64) ∧ ins = idx - mid - 1#64 ∧
                ksL.length = ins.toNat ∧ ksR.length = 10 - mid.toNat - ins.toNat
  requires      (nodePtr ↦₆₄* (ksL ++ ksR)) ∗
                (((nodePtr + 0x100#64) + (mid <<< 3#64)) ↦₆₄ ins)
  ensures       (nodePtr ↦₆₄* (ksL ++ ksR)) ∗
                (((nodePtr + 0x100#64) + (mid <<< 3#64)) ↦₆₄ ins)
  returns       nodePtr

/-- info: [spec_nonvacuous] OK (wrappingSubLenSplitSpec): 2 spatial block(s) pairwise disjoint, 8 pure hypothesis(es) non-contradictory. -/
#guard_msgs in
#spec_nonvacuous! (config := { smallBounds := true, requireWitness := true }) wrappingSubLenSplitSpec

/-- Negative regression test: the same shape with an unsatisfiable range (`12 ≤ idx.toNat ≤ 11`)
    must still be flagged as contradictory. -/
rust_spec wrappingSubLenContradictorySpec
    (nodePtr : ptr) (ghost idx mid ins : u64)
    (ghost ksL : List (BitVec 64)) : u64
  requires_cond 12 ≤ idx.toNat ∧ idx.toNat ≤ 11 ∧
                mid = (if idx = 6#64 then 5#64 else 6#64) ∧ ins = idx - mid - 1#64 ∧
                ksL.length = ins.toNat
  requires      (nodePtr ↦₆₄* ksL)
  ensures       (nodePtr ↦₆₄* ksL)
  returns       nodePtr

/-- info: [spec_nonvacuous] FLAGGED (wrappingSubLenContradictorySpec):
  - contradictory pure precondition (pure hypotheses prove `False`) -/
#guard_msgs in
#spec_nonvacuous (config := { smallBounds := true, requireWitness := true }) wrappingSubLenContradictorySpec

/-! ## Quantified Pure Facts over `BitVec 64` -/

/-- Iterated `↦₆₄` over a symbolic cell list (kept as one atomic spatial block). -/
def qmCells : List (BitVec 64 × BitVec 64) → SepProp
  | [] => emp
  | (a, v) :: cs => (a ↦₆₄ v) ∗ qmCells cs

/-- Every mapped key has a cell. Once witness search grounds `cells := []`, Core's
    `BitVec.instDecidableForallBitVec` makes this `Decidable` by enumerating `2 ^ 64` keys, so the
    witness check must not run `decide` on it. -/
def qmCellsOk (M : BitVec 64 → Option Nat) (cells : List (BitVec 64 × BitVec 64)) : Prop :=
  (cells.map Prod.fst).Nodup ∧
  ∀ p ind, M p = some ind → ∃ v : BitVec 64, (p, v) ∈ cells ∧ (v >>> 48#64).toNat = ind

def qmMap (M : BitVec 64 → Option Nat) : SepProp :=
  ∃∗ cells : List (BitVec 64 × BitVec 64), ⌜qmCellsOk M cells⌝ ∗ qmCells cells

abbrev qmM : BitVec 64 → Option Nat := fun p => if p = 0x400000#64 then some 2 else none

/-- Positive regression test: finishes quickly and reports the quantified fact as opaque
    (neither refuted nor witnessed) instead of claiming a verified witness. -/
def quantMapAuditSpec : Spec (BitVec 64) where
  pre := fun a s0 => ⌜s0.readReg64 .x0 = a⌝ ∗ (a ↦₆₄ 0#64) ∗ qmMap qmM
  post := fun _ _ _ => emp

/-- info: [spec_nonvacuous] OK (quantMapAuditSpec): 1 spatial block(s) pairwise disjoint, 4 pure hypothesis(es) non-contradictory. Note: 1 quantified pure hypothesis(es) were not refuted but also not witnessed (treated as opaque); prove satisfiability separately for a full non-vacuity guarantee. -/
#guard_msgs in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
#spec_nonvacuous! (config := { smallBounds := true }) quantMapAuditSpec

/-- Negative regression test: the quantified fact must not mask a scalar contradiction. -/
def quantMapContraSpec : Spec (BitVec 64) where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a ∧ a.toNat < 4 ∧ 8 ≤ a.toNat⌝ ∗ (a ↦₆₄ 0#64) ∗ qmMap qmM
  post := fun _ _ _ => emp

/-- info: [spec_nonvacuous] FLAGGED (quantMapContraSpec):
  - contradictory pure precondition (pure hypotheses prove `False`) -/
#guard_msgs in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
#spec_nonvacuous (config := { smallBounds := true }) quantMapContraSpec

/-! ## Fail-Closed Forced-Overlap Queries -/

structure TwoPtrArgs where
  a : BitVec 64
  b : BitVec 64

/-- Two distinct cells whose bases are both constrained by pure hypotheses, so the pair needs a
    forced-overlap query (no `smallBounds` witness). -/
def twoPtrAuditSpec : Spec TwoPtrArgs where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.a ∧ s0.readReg64 .x1 = x.b⌝ ∗ (x.a ↦₆₄ 0#64) ∗ (x.b ↦₆₄ 0#64)
  post := fun _ _ _ => emp

/-- info: [spec_nonvacuous] OK (twoPtrAuditSpec): 2 spatial block(s) pairwise disjoint, 3 pure hypothesis(es) non-contradictory. -/
#guard_msgs in
#spec_nonvacuous! twoPtrAuditSpec

-- Negative regression test: an overlap query that exhausts its heartbeat budget is
-- *inconclusive* and must never be reported `OK` (the bang form fails, the plain form FLAGs).
/--
error: [spec_nonvacuous] FLAGGED (twoPtrAuditSpec):
  - inconclusive forced-overlap query between `a.a ↦₆₄
  0#64` and `a.b ↦₆₄
  0#64` (exhausted its `overlapHeartbeats := 1` budget); 0 further block pair(s) not checked. Raise `set_option maxHeartbeats N in` (or `overlapHeartbeats`) so that every pair is checked
-/
#guard_msgs in
#spec_nonvacuous! (config := { overlapHeartbeats := 1 }) twoPtrAuditSpec

/--
info: [spec_nonvacuous] FLAGGED (twoPtrAuditSpec):
  - inconclusive forced-overlap query between `a.a ↦₆₄
  0#64` and `a.b ↦₆₄
  0#64` (exhausted its `overlapHeartbeats := 1` budget); 0 further block pair(s) not checked. Raise `set_option maxHeartbeats N in` (or `overlapHeartbeats`) so that every pair is checked
-/
#guard_msgs in
#spec_nonvacuous (config := { overlapHeartbeats := 1 }) twoPtrAuditSpec

/-- Overlap forced only through a quantified pure hypothesis (`∀ i < 1, a = b` pins the two
    base pointers equal). Quantified hypotheses must stay in the overlap-query context, and a
    witness that ignores them (e.g. `a := 0x1000`, `b := 0x2000`) must not discharge the pair. -/
def quantForcedOverlapSpec : Spec TwoPtrArgs where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.a ∧ s0.readReg64 .x1 = x.b ∧ ∀ i : Nat, i < 1 → x.a = x.b⌝ ∗
      (x.a ↦₆₄ 0#64) ∗ (x.b ↦₆₄ 0#64)
  post := fun _ _ _ => emp

/-- info: [spec_nonvacuous] FLAGGED (quantForcedOverlapSpec):
  - pure hypotheses force spatial overlap between `a.a ↦₆₄ 0#64` and `a.b ↦₆₄ 0#64` -/
#guard_msgs in
#spec_nonvacuous quantForcedOverlapSpec

/-- info: [spec_nonvacuous] FLAGGED (quantForcedOverlapSpec):
  - pure hypotheses force spatial overlap between `a.a ↦₆₄ 0#64` and `a.b ↦₆₄ 0#64` -/
#guard_msgs in
#spec_nonvacuous (config := { smallBounds := true }) quantForcedOverlapSpec

/-- Positive regression test: a wide-`BitVec` quantified fact in the context of a two-block
    overlap query still finishes quickly and is `OK`. -/
def quantMapTwoBlockSpec : Spec TwoPtrArgs where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.a ∧ s0.readReg64 .x1 = x.b⌝ ∗ (x.a ↦₆₄ 0#64) ∗ (x.b ↦₆₄ 0#64) ∗
      qmMap qmM
  post := fun _ _ _ => emp

/-- info: [spec_nonvacuous] OK (quantMapTwoBlockSpec): 2 spatial block(s) pairwise disjoint, 5 pure hypothesis(es) non-contradictory. Note: 1 quantified pure hypothesis(es) were not refuted but also not witnessed (treated as opaque); prove satisfiability separately for a full non-vacuity guarantee. -/
#guard_msgs in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
#spec_nonvacuous! (config := { smallBounds := true }) quantMapTwoBlockSpec

/-! ## Recursive Predicates over Ghost `List`s of Non-Scalar Elements

When pure or spatial predicates are structurally recursive over a ghost list of non-scalar elements,
`#spec_nonvacuous` specializes unconstrained ghost lists to `[]`, unfolds the predicates once, and
records the specialization in its diagnostic message. -/

/-- One level of a synthetic chain: a node pointer and a non-scalar payload. -/
structure RecLvl where
  node : BitVec 64
  keys : List (BitVec 64)

/-- Synthetic level kinds (a non-structure inductive). -/
inductive RecLevel where
  | a (l : RecLvl)
  | b (l : RecLvl)

/-- Synthetic chain terminator. -/
structure RecTop where
  node : BitVec 64
  len : BitVec 16
  keys : List (BitVec 64)

/-- Structurally recursive pure side condition over the ghost list. -/
def RecOk : RecTop → List RecLevel → Prop
  | t, [] => t.node ≠ 0#64 ∧ t.len.toNat < 11 ∧ t.keys.length = t.len.toNat
  | t, .a l :: rest => l.node ≠ 0#64 ∧ l.keys.length = 2 ∧ RecOk t rest
  | t, .b l :: rest => l.node ≠ 0#64 ∧ RecOk t rest

/-- Structurally recursive footprint over the ghost list. -/
def RecPre : BitVec 64 → RecTop → List RecLevel → SepProp
  | c, t, [] => (c ↦₆₄ t.node) ∗ ((t.node + 8#64) ↦₁₆ t.len) ∗ ((t.node + 16#64) ↦₆₄* t.keys)
  | c, t, .a l :: rest => (c ↦₆₄ l.node) ∗ ((l.node + 16#64) ↦₆₄* l.keys) ∗ RecPre l.node t rest
  | c, t, .b l :: rest => (c ↦₆₄ l.node) ∗ RecPre l.node t rest

/-- Positive regression test: the ghost list is specialized to `[]`, both recursive predicates
    reduce to their base case, and a concrete witness is found (`requireWitness`). -/
rust_spec recListGhostValidSpec (cursor : ptr) (p : ptr) (x : u64)
    (ghost levels : List RecLevel) (ghost top : RecTop) (ghost v : u64) : u64
  requires_cond x ≠ 0#64 ∧ RecOk top levels
  requires      (p ↦₆₄ v) ∗ RecPre cursor top levels
  ensures       (p ↦₆₄ x) ∗ RecPre cursor top levels
  returns       x

/-- info: [spec_nonvacuous] OK (recListGhostValidSpec): 4 spatial block(s) pairwise disjoint, 8 pure hypothesis(es) non-contradictory.
  (note: ghost `a_3 : List RecLevel` passed to recursive [RecOk, RecPre] specialized to `[]`) -/
#guard_msgs in
#spec_nonvacuous! (config := { smallBounds := true, requireWitness := true }) recListGhostValidSpec

/-- Negative regression test: a contradiction elsewhere in the spec (`x = 0 ∧ x ≠ 0`) is still
    flagged when the spec also mentions recursive predicates over a ghost list. -/
rust_spec recListGhostContradictorySpec (cursor : ptr) (p : ptr) (x : u64)
    (ghost levels : List RecLevel) (ghost top : RecTop) (ghost v : u64) : u64
  requires_cond x = 0#64 ∧ x ≠ 0#64 ∧ RecOk top levels
  requires      (p ↦₆₄ v) ∗ RecPre cursor top levels
  ensures       (p ↦₆₄ x) ∗ RecPre cursor top levels
  returns       x

/-- info: [spec_nonvacuous] FLAGGED (recListGhostContradictorySpec):
  - contradictory pure precondition (pure hypotheses prove `False`)
  - pure hypotheses force spatial overlap between `a ↦₆₄ a_rest` and `a_1 ↦₆₄ a_4.node`
  - pure hypotheses force spatial overlap between `a ↦₆₄ a_rest` and `(a_4.node + 8#64) ↦₁₆ a_4.len`
  - pure hypotheses force spatial overlap between `a ↦₆₄ a_rest` and `(a_4.node + 16#64) ↦₆₄* a_4.keys`
  - pure hypotheses force spatial overlap between `a_1 ↦₆₄ a_4.node` and `(a_4.node + 8#64) ↦₁₆ a_4.len`
  - pure hypotheses force spatial overlap between `a_1 ↦₆₄ a_4.node` and `(a_4.node + 16#64) ↦₆₄* a_4.keys`
  (note: ghost `a_3 : List RecLevel` passed to recursive [RecOk, RecPre] specialized to `[]`) -/
#guard_msgs in
#spec_nonvacuous (config := { smallBounds := true }) recListGhostContradictorySpec

/-- Negative regression test: a spatial overlap outside the recursive predicate (`p` owned
    twice) is still flagged. -/
rust_spec recListGhostOverlapSpec (cursor : ptr) (p : ptr) (x : u64)
    (ghost levels : List RecLevel) (ghost top : RecTop) (ghost v : u64) : u64
  requires_cond RecOk top levels
  requires      (p ↦₆₄ v) ∗ (p ↦₆₄ v) ∗ RecPre cursor top levels
  ensures       (p ↦₆₄ x) ∗ (p ↦₆₄ v) ∗ RecPre cursor top levels
  returns       x

/-- info: [spec_nonvacuous] FLAGGED (recListGhostOverlapSpec):
  - overlapping spatial regions on `a`: `a ↦₆₄ a_rest` ([a, +8)) and `a ↦₆₄ a_rest` ([a, +8))
  (note: ghost `a_3 : List RecLevel` passed to recursive [RecOk, RecPre] specialized to `[]`) -/
#guard_msgs in
#spec_nonvacuous (config := { smallBounds := true }) recListGhostOverlapSpec

/-- Guard regression test: `levels` is also constrained outside the recursive predicates
    (`levels.length = 2`), so specializing it to `[]` would contradict that fact and produce a
    spurious `FLAGGED`. No specialization note may appear, and the spec must not be flagged. -/
rust_spec recListGhostConstrainedSpec (cursor : ptr) (p : ptr) (x : u64)
    (ghost levels : List RecLevel) (ghost top : RecTop) (ghost v : u64) : u64
  requires_cond levels.length = 2 ∧ RecOk top levels
  requires      (p ↦₆₄ v) ∗ RecPre cursor top levels
  ensures       (p ↦₆₄ x) ∗ RecPre cursor top levels
  returns       x

/-- info: [spec_nonvacuous] OK (recListGhostConstrainedSpec): 1 spatial block(s) pairwise disjoint, 6 pure hypothesis(es) non-contradictory. -/
#guard_msgs in
#spec_nonvacuous (config := { smallBounds := true }) recListGhostConstrainedSpec

/-! ## `c_type_spec` `SemType` Descriptor Unfolding in `#spec_lint` -/

section SemTypeUnfoldLint
open Arm64.CType

def testHandleRep (p : BitVec 64) (v : BitVec 64) : SepProp :=
  if p = 0#64 then emp else (p ↦₆₄ v)

def TestHandleT : SemType (BitVec 64) :=
  { tyName := "TestHandle *",
    interp := testHandleRep,
    pureWf := fun _ _ => True }

/-- Positive regression test: `c_type_spec` cleanup spec consuming `Own TestHandleT` (defined via
    `def`, not `abbrev`) plus a preserved `stackBelow sp` region is NOT falsely flagged by
    `[post-retains-freed-ptr]`. -/
c_type_spec semTypeCleanupValidSpec (h : ptr) (ghost v : u64) (sp : sp) : (ret : u32) where
  c_arg h : Own TestHandleT v
  c_env memRegion (sp - 64#64) 64
  returns 0#32

/-- info: [spec_lint] OK (semTypeCleanupValidSpec): no precondition-pinning warnings. -/
#guard_msgs in
#spec_lint! semTypeCleanupValidSpec

/-- Negative regression test: `c_type_spec` cleanup spec that uses `ShrRef TestHandleT` (retaining
    the freed handle in `post`) IS flagged by `[post-retains-freed-ptr]`. -/
c_type_spec semTypeCleanupRetainedSpec (h : ptr) (ghost v : u64) (sp : sp) : (ret : u32) where
  c_arg h : ShrRef TestHandleT v
  c_env memRegion (sp - 64#64) 64
  returns 0#32

/--
error: [spec_lint] FLAGGED (semTypeCleanupRetainedSpec):
  - [post-retains-freed-ptr] deallocation spec `semTypeCleanupRetainedSpec` leaves freed pointer ownership (`a.fst ↦₆₄
  a.2.fst`) in `post`
-/
#guard_msgs (error, drop info) in
#spec_lint! semTypeCleanupRetainedSpec

end SemTypeUnfoldLint

/-! ## Large `List.replicate` Witness Reduction and Pure-Anchor Overlap Filtering -/

/-- Positive regression test: a spec with a 4096-byte list (`bytes.length = 4096`, triggering
    `List.replicate 4096 1#8` in `tryBoundedPureWitness?`), multiple struct fields on an
    ABI entry-register pointer `p`, and a stack frame passes `#spec_nonvacuous!` with
    `requireWitness := true` under a tight `maxHeartbeats 25000` budget because
    `List.length_replicate` rewrites before `decide` and unconstrained entry-register bindings
    do not trigger quadratic forced-overlap tactic calls. -/
rust_spec largeListWitnessValidSpec (p : ptr) (q : ptr)
    (ghost v0 : u64) (ghost v1 : u64) (ghost bytes : List (BitVec 8)) : u32
  requires_cond bytes.length = 4096
  requires      (p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ v1) ∗ (q ↦ₛ bytes) ∗ stackFrame s0 64
  ensures       (p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ v1) ∗ (q ↦ₛ bytes) ∗ stackFrame sf 64
  returns       0#32

/-- info: [spec_nonvacuous] OK (largeListWitnessValidSpec): 4 spatial block(s) pairwise disjoint, 4 pure hypothesis(es) non-contradictory. -/
#guard_msgs in
set_option maxHeartbeats 25000 in
#spec_nonvacuous! (config := { smallBounds := true, requireWitness := true }) largeListWitnessValidSpec

/-- Negative regression test: when `s0.sp` and an entry-register pointer `p` ARE constrained in
    pure hypotheses to alias (`p = s0.sp - 16#64`), `#spec_nonvacuous!` still detects the forced
    spatial overlap between `p ↦₆₄ v0` and `stackFrame s0 64`. -/
def spAliasForcedOverlapSpec : Spec (BitVec 64 × BitVec 64) where
  pre := fun (p, v0) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ p = s0.sp - 16#64⌝ ∗
    (p ↦₆₄ v0) ∗ stackFrame s0 64
  post := fun (p, v0) _ sf =>
    (p ↦₆₄ v0) ∗ stackFrame sf 64

/--
error: [spec_nonvacuous] FLAGGED (spAliasForcedOverlapSpec):
  - pure hypotheses force spatial overlap between `a_1 ↦₆₄ a_rest` and `memRegion (s0.sp - 64#64) 64`
-/
#guard_msgs (error, drop info) in
#spec_nonvacuous! (config := { smallBounds := false }) spAliasForcedOverlapSpec

/-! ## Update Modality (`|==>`) and Ghost Map (`ghostMapAuth`, `ghostMapElem`) -/

/-- Positive regression test: a spec with `ghostMapAuth` / `ghostMapElem` in its precondition and
    a `|==>` postcondition passes `#spec_lint!` and `#spec_nonvacuous!`. -/
c_spec ghostMapUpdateValidSpec (ctx γ : GhostName) (p : ptr) (ghost n : Nat) : u64
  requires_cond 0 < n ∧ n ≤ 64
  requires      memRegion p n ∗ ghostMapElem γ p n ∗ stackFrame s0 32
  ensures       |==> (stackFrame sf 32)
  returns       0#64

#spec_lint! (ghostMapUpdateValidSpec 0)
#spec_nonvacuous! (config := { smallBounds := true }) (ghostMapUpdateValidSpec 0)

/-- Negative regression test: a spec with `|==>` in its postcondition and a contradictory pure
    precondition is still flagged by `#spec_nonvacuous`. -/
c_spec ghostMapUpdateVacuousSpec (ctx γ : GhostName) (p : ptr) : u64
  requires_cond p = 0#64 ∧ p ≠ 0#64
  requires      ghostMapElem γ p 8 ∗ stackFrame s0 32
  ensures       |==> (stackFrame sf 32)
  returns       0#64

/-- info: [spec_nonvacuous] FLAGGED ((ghostMapUpdateVacuousSpec 0)):
  - contradictory pure precondition (pure hypotheses prove `False`) -/
#guard_msgs in
#spec_nonvacuous (config := { smallBounds := true }) (ghostMapUpdateVacuousSpec 0)

/-! ## `SepWP` and `oom_when` Contracts -/

/-- User-defined `SepProp` wrapper (`def`, not `abbrev`): `#spec_smoke` must match the 6-argument
    `SepWP` goal after `wp_init` / `wp_start` and unfold `oomCell64` in its `P` argument before
    stepping `ldr x8, [x0]`. -/
def oomCell64 (p v : BitVec 64) : SepProp := p ↦₆₄ v

/-- Valid spec with `oom_when True` and a user-defined `SepProp` in `requires`: must be audited and
    pass `#spec_nonvacuous!`, `#spec_lint!`, and `#spec_smoke!`. -/
c_spec oomWhenGoodAuditSpec (ptr : ptr) (ghost v0 : u64) (ghost v1 : u64)
  requires oomCell64 ptr v0 ∗ ((ptr + 8#64) ↦₆₄ v1)
  ensures  (ptr ↦₆₄ (v0 + v1)) ∗ ((ptr + 8#64) ↦₆₄ v1)
  oom_when True

#spec_nonvacuous! oomWhenGoodAuditSpec
#spec_lint! oomWhenGoodAuditSpec
#spec_smoke! goodAuditCode oomWhenGoodAuditSpec

/-- Buggy spec with `oom_when True` (missing `(ptr + 8) ↦₆₄ v1` for `ldr x9, [x0, #8]`): must FAIL
    `#spec_smoke!`. -/
c_spec oomWhenMissingCellSpec (ptr : ptr) (ghost v0 : u64) (ghost v1 : u64)
  requires oomCell64 ptr v0
  ensures  (ptr ↦₆₄ (v0 + v1))
  oom_when True

/--
error: [spec_smoke] STUCK (goodAuditCode oomWhenMissingCellSpec): 0/1 path(s) reached return (0 closed postcondition)
  - path 1 (unconditional): STUCK at PC 0x70004#64 (Instr.ldr RegWidth.W64 MemWidth.X64 false (Reg.gpr 9#5)
  (AddrMode.Offset (Reg.gpr 0#5) 8#64)): no cell at a.fst + 8#64 in a.fst ↦₆₄ a.2.fst
-/
#guard_msgs (error, drop info) in
#spec_smoke! goodAuditCode oomWhenMissingCellSpec

/-- Buggy spec with `oom_when True` (overlapping spatial blocks at `ptr`): must FAIL
    `#spec_nonvacuous!`. -/
c_spec oomWhenOverlapSpec (ptr : ptr) (ghost v0 : u64) (ghost v1 : u64)
  requires oomCell64 ptr v0 ∗ (ptr ↦₆₄ v1)
  ensures  (ptr ↦₆₄ v0)
  oom_when True

/--
error: [spec_nonvacuous] FLAGGED (oomWhenOverlapSpec):
  - overlapping spatial regions on `a_1`: `a_1 ↦₆₄ a` ([a_1, +8)) and `a_1 ↦₆₄ a_rest_1` ([a_1, +8))
-/
#guard_msgs (error, drop info) in
#spec_nonvacuous! oomWhenOverlapSpec

/-! ## `stackFrameAt` Nested-Frame Overlap

`stackFrameAt sp n` owns `[sp - n, sp)`. Two frames declared at the same base (instead of placing
the callee frame strictly below the caller frame), or a scratch area at the caller's own `sp`, make
the precondition unsatisfiable and must be flagged, including when `n` is symbolic. -/

/-- Callee frame `[sp - 40, sp - 16)` declared at the same base as the caller's
    `[sp - 32, sp - 16)` instead of below it: the two frames share `[sp - 32, sp - 16)`. -/
def widgetNestedFrameOverlapSpec : Spec (BitVec 64) where
  pre := fun sp s0 => ⌜s0.sp = sp⌝ ∗ stackFrameAt (sp - 16#64) 16 ∗ stackFrameAt (sp - 16#64) 24
  post := fun _ _ _ => emp

/--
error: [spec_nonvacuous] FLAGGED (widgetNestedFrameOverlapSpec):
  - overlapping spatial regions on `a`: `stackFrameAt (a - 16#64)
  16` ([a - 32, +16)) and `stackFrameAt (a - 16#64) 24` ([a - 40, +24))
-/
#guard_msgs (error, drop info) in
#spec_nonvacuous! widgetNestedFrameOverlapSpec

/-- Callee scratch area `stackFrameAt sp 64` placed at the caller's own `sp` instead of below its
    8-byte frame `stackFrameAt sp 8`. -/
def widgetScratchOverlapSpec : Spec (BitVec 64) where
  pre := fun sp s0 => ⌜s0.sp = sp⌝ ∗ stackFrameAt sp 8 ∗ stackFrameAt sp 64
  post := fun _ _ _ => emp

/--
error: [spec_nonvacuous] FLAGGED (widgetScratchOverlapSpec):
  - overlapping spatial regions on `a`: `stackFrameAt a 8` ([a - 8, +8)) and `stackFrameAt a 64` ([a - 64, +64))
-/
#guard_msgs (error, drop info) in
#spec_nonvacuous! widgetScratchOverlapSpec

/-- Correctly nested layout: caller frame, callee frame below it, scratch below both. -/
def widgetNestedFrameGoodSpec : Spec (BitVec 64) where
  pre := fun sp s0 =>
    ⌜s0.sp = sp⌝ ∗ stackFrameAt sp 16 ∗ stackFrameAt (sp - 16#64) 24 ∗ stackFrameAt (sp - 40#64) 64
  post := fun _ _ _ => emp

#spec_nonvacuous! widgetNestedFrameGoodSpec

/-- Symbolic frame size: two frames of the same symbolic size at the same base. -/
def alphaSymFrameOverlapSpec : Spec (BitVec 64 × Nat) where
  pre := fun a s0 =>
    ⌜s0.sp = a.1⌝ ∗ ⌜0 < a.2 ∧ a.2 < 4096⌝ ∗
      stackFrameAt (a.1 - 64#64) a.2 ∗ stackFrameAt (a.1 - 64#64) a.2
  post := fun _ _ _ => emp

/--
error: [spec_nonvacuous] FLAGGED (alphaSymFrameOverlapSpec):
  - overlapping spatial regions at `a_1 - 64#64 -
  BitVec.ofNat 64 a_rest`: `stackFrameAt (a_1 - 64#64) a_rest` and `stackFrameAt (a_1 - 64#64) a_rest`
-/
#guard_msgs (error, drop info) in
#spec_nonvacuous! alphaSymFrameOverlapSpec

/-- Symbolic frame size with a disjoint cell above `sp`. -/
def alphaSymFrameGoodSpec : Spec (BitVec 64 × Nat × BitVec 64) where
  pre := fun a s0 =>
    ⌜s0.sp = a.1⌝ ∗ ⌜0 < a.2.1 ∧ a.2.1 < 4096⌝ ∗
      stackFrameAt a.1 a.2.1 ∗ (a.1 ↦₆₄ a.2.2)
  post := fun _ _ _ => emp

#spec_nonvacuous! alphaSymFrameGoodSpec

end Testing.SpecAudit
