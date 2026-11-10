/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.InternalPlaced
public import VerifiedLibraries.Mallocng.Proofs.GhostToken

/-!
# Block-Token-Generic Placed Allocation Specifications

Placed `malloc`, `calloc`, `aligned_alloc`, and `posix_memalign` contracts parameterized by an
alignment-indexed block token `B : GhostName → BitVec 64 → Nat → Nat → SepProp` (`B γ p n effAlign`).
Instantiated at `mallocngOldTok` (`mallocngIface.Block`, ignoring `effAlign`) and at
`MallocngTightBlock` (ghost overhead bounded by `effAlign - 16`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj Arm64.CType ProofLib VerifiedLibraries.Mallocng

/-! ## Block Types and Token Instances -/

/-- `MallocngBlock` over an alignment-indexed token `B γ p n effAlign`. -/
@[reducible] def MallocngTokBlock (B : BitVec 64 → Nat → Nat → SepProp) : SemType (Nat × Nat) where
  tyName := "void * (mallocng allocated block)"
  interp := fun p (n, effAlign) => B p n effAlign ∗ memRegion p n
  pureWf := fun p (n, align) => p ≠ 0#64 ∧ align ∣ p.toNat ∧ p.toNat + n < 2 ^ 64

/-- `MallocngZeroedBlock` over an alignment-indexed token `B γ p n effAlign`. -/
@[reducible] def MallocngTokZeroedBlock (B : BitVec 64 → Nat → Nat → SepProp) :
    SemType (Nat × Nat) where
  tyName := "void * (zero-initialized mallocng block)"
  interp := fun p (n, effAlign) => B p n effAlign ∗ (p ↦ₛ List.replicate n 0#8)
  pureWf := fun p (n, align) => p ≠ 0#64 ∧ align ∣ p.toNat ∧ p.toNat + n < 2 ^ 64

/-- The concrete `mallocngIface.Block` token, ignoring the effective alignment. -/
@[reducible] def mallocngOldTok (γ : GhostName) (p : BitVec 64) (n _a : Nat) : SepProp :=
  mallocngIface.Block γ p n

/-! ## Placed `__libc_malloc_impl` and `default_malloc` Spec over `B` -/

/-- `libcMallocImplPlacedTightSpec` returning `B γ p req 16`. -/
def libcMallocImplPlacedTokSpec [MallocngMultiPlacement]
    (B : GhostName → BitVec 64 → Nat → Nat → SepProp)
    (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat) : Spec Unit :=
  let ok := decide (req ≤ MallocngMaxAllocSize)
  let bf := mallocngAllocBudget ok req b
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜(s0.readReg64 .x0).toNat = req⌝ ∗
      stackFrame s0 704 ∗
      MallocngEnv mallocngIface γ maddrs tp brkStart b ivs0 s0
    post := fun _ s0 sf =>
      ⌜MallocngProcPreserved s0 sf ∧
       MallocngMappedDelta 16 (MallocngTightStepBound (if ok then req else 0) b.peakCount) s0.mem sf.mem⌝ ∗
      stackFrame s0 704 ∗
      if req ≤ MallocngMaxAllocSize then
        ∃∗ p : BitVec 64,
        ∃∗ bs : List (BitVec 8),
        ∃∗ st' : MallocngSt,
          ⌜sf.readReg64 .x0 = p ∧
           sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
           MallocngBlockWf p req ∧
           bs.length = req ∧
           MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngCountIvsWF bf (dynamicRootRegions st') st' ∧
           ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
             g'.slots[idx]'hIdx = .liveUser p req (max req MallocngMinBlockCost) ∧
             p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
             (g'.isMmapped = true → bs = List.replicate req 0#8)⌝ ∗
          MallocngRoTablesA maddrs ∗
          MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
          MallocngRuntime maddrs tp ∗
          (p ↦ₛ bs) ∗
          B γ p req 16
      else
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf
    onOom := fun _ s0 sf => ⌜MallocngTightOomCond msvc (if ok then req else 0) b.peakCount s0 sf⌝
  }

/-- Placed `__libc_malloc_impl(req)` (`blk09`, `704` B stack) returning `B γ p req 16`. -/
def LibcMallocImplPlacedTokStmt (B : GhostName → BitVec 64 → Nat → Nat → SepProp) : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
    subroutine_ok (mallocngBlockProg mmpl 9 msvc) (mbase 9)
      (libcMallocImplPlacedTokSpec B γ tp brkStart b ivs0 req)

/-- Placed `default_malloc(req)` / `malloc(req)` (`blk04`, `704` B stack) returning `B γ p req 16`. -/
def DefaultMallocPlacedTokStmt (B : GhostName → BitVec 64 → Nat → Nat → SepProp) : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
    subroutine_ok (mallocngBlockProg mmpl 4 msvc) (mbase 4)
      (libcMallocImplPlacedTokSpec B γ tp brkStart b ivs0 req)

theorem call_placed_defaultMalloc_tok [MallocngMultiPlacement]
    {B : GhostName → BitVec 64 → Nat → Nat → SepProp} (h : DefaultMallocPlacedTokStmt B)
    {P : Program} (γ : GhostName) (tp brkStart : BitVec 64) (b : MallocngBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 4) (libcMallocImplPlacedTokSpec B γ tp brkStart b ivs0 req) :=
  subroutine_ok_block_to_block (j := 4) (by decide) (h γ tp brkStart b ivs0 req) hext hsvc

theorem DefaultMallocPlacedTightStmt.toTok (h : DefaultMallocPlacedTightStmt) :
    DefaultMallocPlacedTokStmt mallocngOldTok := h

/-! ## Public C Specs over `B` -/

/-- `mallocngMallocTightSpec` with block token `B`. -/
c_type_spec mallocngMallocTokSpec (ctx B : GhostName → BitVec 64 → Nat → Nat → SepProp)
    (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (req : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost b : MallocngBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := decide (req.toNat ≤ MallocngMaxAllocSize)
  let b' := mallocngAllocBudget ok req.toNat b
  c_arg req : Val SizeT
  c_ret : Own (OptOwn (MallocngTokBlock (B γ)))
    (if ok then some (req.toNat, 16) else none)
  c_env (MallocngEnv mallocngIface γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngPostEnv mallocngIface γ A tp brkStart b' ivs0 s0 sf ∗
          stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting
    16 (MallocngTightStepBound (if ok then req.toNat else 0) b.peakCount) s0 sf
  oom_when MallocngTightOomCond svc (if ok then req.toNat else 0) b.peakCount s0 sf

/-- `mallocngCallocTightSpec` with block token `B`. -/
c_type_spec mallocngCallocTokSpec (ctx B : GhostName → BitVec 64 → Nat → Nat → SepProp)
    (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (nmemb : u64) (size : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost b : MallocngBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let total := nmemb.toNat * size.toNat
  let ok := decide (total ≤ MallocngMaxAllocSize)
  let b' := mallocngAllocBudget ok total b
  c_arg nmemb : Val SizeT
  c_arg size : Val SizeT
  c_ret : Own (OptOwn (MallocngTokZeroedBlock (B γ)))
    (if ok then some (total, 16) else none)
  c_env (MallocngEnv mallocngIface γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngPostEnv mallocngIface γ A tp brkStart b' ivs0 s0 sf ∗
          stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting
    16 (MallocngTightStepBound (if ok then total else 0) b.peakCount) s0 sf
  oom_when MallocngTightOomCond svc (if ok then total else 0) b.peakCount s0 sf

/-- `mallocngAlignedAllocTightSpec` with block token `B`. -/
c_type_spec mallocngAlignedAllocTokSpec (ctx B : GhostName → BitVec 64 → Nat → Nat → SepProp)
    (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (align : u64) (len : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost b : MallocngBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := mallocngAlignedAllocOk align len
  let eff := mallocngAlignedEffSize align.toNat len.toNat
  let b' := mallocngAlignedBudget ok align.toNat len.toNat b
  caveat [API_RESTRICTION] "align ≤ 2^31 avoids musl 1.2.5 set_size int32 reserved overflow" :
    align.toNat ≤ MaxAlignedAllocAlign
  c_arg align : Val SizeT
  c_arg len : Val SizeT
  c_ret : Own (OptOwn (MallocngTokBlock (B γ)))
    (if ok then some (len.toNat, max align.toNat 16) else none)
  c_env (MallocngEnv mallocngIface γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngPostEnv mallocngIface γ A tp brkStart b' ivs0 s0 sf ∗
          stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting
    16 (MallocngTightStepBound (if ok then eff else 0) b.peakCount) s0 sf
  oom_when MallocngTightOomCond svc (if ok then eff else 0) b.peakCount s0 sf

/-- `mallocngPosixMemalignTightSpec` with block token `B`. -/
c_type_spec mallocngPosixMemalignTokSpec (ctx B : GhostName → BitVec 64 → Nat → Nat → SepProp)
    (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (res : ptr) (align : u64) (len : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost b : MallocngBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : u32) where
  let ok := mallocngPosixMemalignOk align len
  let eff := mallocngAlignedEffSize align.toNat len.toNat
  let b' := mallocngAlignedBudget ok align.toNat len.toNat b
  caveat [API_RESTRICTION] "align ≤ 2^31 avoids musl 1.2.5 set_size int32 reserved overflow" :
    align.toNat ≤ MaxAlignedAllocAlign
  c_arg res : MutRef (OptOutPtr (MallocngTokBlock (B γ))) none ⇝
    (if ok then some (len.toNat, max align.toNat 16) else none)
  c_arg align : Val SizeT
  c_arg len : Val SizeT
  c_env (MallocngEnv mallocngIface γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngPostEnv mallocngIface γ A tp brkStart b' ivs0 s0 sf ∗
          stackFrameAt sp mallocngStackBytes)
  returns mallocngPosixMemalignRet align len
  ensures_pure MallocngCallAccounting
    16 (MallocngTightStepBound (if ok then eff else 0) b.peakCount) s0 sf
  oom_when MallocngTightOomCond svc (if ok then eff else 0) b.peakCount s0 sf

example (svc : State → State) (γ : GhostName) (A : MallocngAddrs) :
    mallocngMallocTokSpec mallocngOldTok svc γ A = mallocngMallocTightSpec mallocngIface svc γ A :=
  rfl

example (svc : State → State) (γ : GhostName) (A : MallocngAddrs) :
    mallocngCallocTokSpec mallocngOldTok svc γ A = mallocngCallocTightSpec mallocngIface svc γ A :=
  rfl

example (svc : State → State) (γ : GhostName) (A : MallocngAddrs) :
    mallocngAlignedAllocTokSpec mallocngOldTok svc γ A =
      mallocngAlignedAllocTightSpec mallocngIface svc γ A :=
  rfl

example (svc : State → State) (γ : GhostName) (A : MallocngAddrs) :
    mallocngPosixMemalignTokSpec mallocngOldTok svc γ A =
      mallocngPosixMemalignTightSpec mallocngIface svc γ A :=
  rfl

end VerifiedLibraries.Mallocng.Proofs
