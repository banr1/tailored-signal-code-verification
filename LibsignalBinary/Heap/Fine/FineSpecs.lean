/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.AllocSlotFine
public import LibsignalBinary.Heap.Fine.FreeReallocInvFine

/-!
# Fine-Grained `mallocng` Subroutine and Entrypoint Specifications

`FineBudget`-indexed environment predicates (`FineEnv`, `FinePostEnv`), `SemType` block wrappers,
internal `__libc_malloc_impl` / `default_malloc` callback contracts, and placed C entrypoint
specifications (`malloc`, `free`, `calloc`, `realloc`, `aligned_alloc`, `posix_memalign`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.CType ProofLib VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Environment Predicates and `SemType` Wrappers -/

/-- Step-reserve-parameterized `mallocng` OOM condition (definitionally equal to
    `MallocngStepOomCond` in `LibsignalBinary.Heap.IfaceBudget` and
    `MallocngPlacedOomCond svc 16 stepBytes`). -/
def FineStepOomCond (svc : State → State) (stepBytes : Nat) (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧
  sf.trace = s0.trace ∧
  sf.sigActions = s0.sigActions ∧
  MallocngMappedDelta 16 stepBytes s0.mem sf.mem ∧
  (MallocngSanitizedSvc svc →
    ∃ sz : Nat,
      PAGE_SIZE ≤ sz ∧
      sz % PAGE_SIZE = 0 ∧
      sz ≤ stepBytes ∧
      MallocngNoGapOrPhys sf sz)

theorem FineStepOomCond.mono {svc : State → State} {b1 b2 : Nat} {s0 sf : State}
    (hb : b1 ≤ b2) (h : FineStepOomCond svc b1 s0 sf) :
    FineStepOomCond svc b2 s0 sf := by
  obtain ⟨hfs, htr, hsig, hd, hgap⟩ := h
  refine ⟨hfs, htr, hsig, MallocngMappedDelta.mono (Nat.le_refl 16) hb hd, fun hsan => ?_⟩
  obtain ⟨sz, hlo, hmod, hhi, hng⟩ := hgap hsan
  exact ⟨sz, hlo, hmod, Nat.le_trans hhi hb, hng⟩

theorem fineStepOomCond_of_placed {svc : State → State}
    {maxIvs maxBytes stepBytes : Nat} {s0 sf : State}
    (hi : maxIvs ≤ 16) (hb : maxBytes ≤ stepBytes)
    (h : MallocngPlacedOomCond svc maxIvs maxBytes s0 sf) :
    FineStepOomCond svc stepBytes s0 sf := by
  obtain ⟨hfs, htr, hsig, ivs, hl, hs, hc, hgap⟩ := h
  refine ⟨hfs, htr, hsig, ⟨ivs, Nat.le_trans hl hi, Nat.le_trans hs hb, hc⟩, fun hsan => ?_⟩
  obtain ⟨sz, hlo, hmod, hhi, hng⟩ := hgap hsan
  exact ⟨sz, hlo, hmod, by omega, hng⟩

theorem fineStepOomCond_of_oomCond {svc : State → State} {req peakCount stepBytes : Nat}
    {s0 sf : State}
    (hb : MallocngStepBound req peakCount ≤ stepBytes)
    (h : MallocngOomCond svc req peakCount s0 sf) :
    FineStepOomCond svc stepBytes s0 sf :=
  FineStepOomCond.mono hb h

/-- State-indexed `mallocng` environment over `FineHeapImpl`. -/
noncomputable def FineEnv
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (b : FineBudget) (ivs : List (BitVec 64 × Nat)) (s : State) : SepProp :=
  ⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
    FineHeapImpl γ A tp brkStart s.brk b ivs

/-- Post-call state-indexed `mallocng` environment over `FineHeapImpl`. -/
noncomputable def FinePostEnv
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (bf : FineBudget) (ivs0 : List (BitVec 64 × Nat)) (s0 sf : State) : SepProp :=
  ∃∗ ivsf : List (BitVec 64 × Nat),
    ⌜MallocngNoOrphanMappings ivs0 ivsf s0.mem sf.mem⌝ ∗
    FineEnv γ A tp brkStart bf ivsf sf

/-- Live uninitialized `mallocng` block `SemType` over `FineBlock`. -/
@[reducible] def FineBlockSem (γ : GhostName) : SemType (Nat × Nat) where
  tyName := "void * (mallocng allocated block)"
  interp := fun p (n, effAlign) => FineBlock γ p n effAlign ∗ memRegion p n
  pureWf := fun p (n, effAlign) => p ≠ 0#64 ∧ effAlign ∣ p.toNat ∧ p.toNat + n < 2 ^ 64

/-- Live zero-initialized `mallocng` block `SemType` over `FineBlock`. -/
@[reducible] def FineZeroedBlockSem (γ : GhostName) : SemType (Nat × Nat) where
  tyName := "void * (zero-initialized mallocng block)"
  interp := fun p (n, effAlign) => FineBlock γ p n effAlign ∗ (p ↦ₛ List.replicate n 0#8)
  pureWf := fun p (n, effAlign) => p ≠ 0#64 ∧ effAlign ∣ p.toNat ∧ p.toNat + n < 2 ^ 64

/-- Live `mallocng` block with initialized prefix `bs` and alignment `align` over `FineBlock`. -/
@[reducible] def FineInitBlockSem (γ : GhostName) : SemType (Nat × Nat × List (BitVec 8)) where
  tyName := "void * (mallocng block with initialized prefix)"
  interp := fun p (sz, align, bs) =>
    FineBlock γ p sz (max align 16) ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (sz - bs.length)
  pureWf := fun p (sz, _, bs) =>
    p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + sz < 2 ^ 64 ∧ bs.length ≤ sz

/-- Nullable freeable `mallocng` block `SemType` over `FineBlock`. -/
@[reducible] def FineFreeableBlockSem (γ : GhostName) : SemType (Nat × Nat) where
  tyName := "void * (nullable mallocng allocated block)"
  interp := fun p (n, align) => if p = 0#64 then emp else FineBlock γ p n (max align 16) ∗ memRegion p n
  pureWf := fun p (n, _) => if p = 0#64 then n = 0 else 16 ∣ p.toNat ∧ p.toNat + n < 2 ^ 64

/-! ## Raw and Committed `__libc_malloc_impl` Contracts -/

/-- Pure transition relation from `st0` (at quiescent `MallocngFineInv 0 b ivs0 alignMap0 st0`)
    to `st'` after `__libc_malloc_impl(req)` (`req ≤ MallocngMaxAllocSize`) returns `p`, BEFORE
    committing `FineBudget` (`stepAlloc` vs `stepReallocAdd` vs `aligned_alloc` reframe + `stepAligned`). -/
def MallocImplFineRawRel (base brkStart : BitVec 64)
    (b : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (alignMap0 : BitVec 64 → Option Nat) (st0 st' : MallocngSt)
    (g' : GroupDesc) (idx req : Nat) (p : BitVec 64) : Prop :=
  MallocngFineInv 0 b ivs0 alignMap0 st0 ∧
  st0.liveMap p = none ∧
  st'.liveMap = st0.liveMap.insert p req 0 ∧
  st'.metaAreas.length ≤ fineMaxMetaAreas b ∧
  g' ∈ st'.groups ∧
  (∃ hIdx' : idx < g'.slots.length,
     g'.slots[idx]'hIdx' = .liveUser p req (max req MallocngMinBlockCost)) ∧
  p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
  (24 ≤ g'.sc ∧ g'.sc ≤ 26 → nominalSlotCap 23 < req) ∧
  (g'.sc = 63 → g'.maplen * 4096 ≤ req + 4115) ∧
  (if hSmall : req ≤ MmapThresholdReq then
     ∃ (sc : Nat) (pk : List Nat) (pkSC pkSB : Nat)
       (st1 : MallocngSt) (g1 : GroupDesc)
       (brk1 : BitVec 64) (live1 peak1 : Nat),
       let _ := hSmall
       sc < 48 ∧
       (sc = sizeToClassUnits ((req + 3) / 16) ∨
        sc = coarseAlt (sizeToClassUnits ((req + 3) / 16))) ∧
       (pk.length = 48 ∧
        (∀ k < 48, liveSlotsInClass st0 k ≤ pk.getD k 0) ∧
        (∀ k < 48, (allGroups st0 k).length ≤ gBound pk k) ∧
        (∀ ch < 48, ∀ pSc < 48, (nestedEdge st0 ch pSc).length ≤ edgeBound pk ch pSc) ∧
        (∀ k < 48, rootBytes st0 k ≤ rBound pk k) ∧
        (straddle63Groups st0).length ≤ pkSC ∧
        straddle63Bytes st0 ≤ pkSB ∧
        linForm grpWtS pk + FineScale * pkSC ≤ b.cumSmallGroupsS ∧
        linForm slotWt pk + pkSB ≤ b.cumSmallBytes) ∧
       AllocSlotInvPres sc pk alignMap0 st0 st1 ∧
       MallocngWFInflight 1 base brkStart brk1 live1 peak1 st1 ∧
       g1 ∈ st1.groups ∧ g1.sc = sc ∧
       (∃ hIdx1 : idx < g1.slots.length, g1.slots[idx]'hIdx1 = .claimed) ∧
       FineGroupSameGeom g' g1 ∧
       g'.slots = g1.slots.set idx (.liveUser p req (max req MallocngMinBlockCost)) ∧
       st'.groups = st1.groups.map (fun g => if g.metaPtr == g1.metaPtr then g' else g)
   else
     ∃ st1 : MallocngSt,
       idx = 0 ∧
       FineSameGroupsSlotKind st1.groups st0.groups ∧
       st'.groups = g' :: st1.groups ∧
       g'.sc = 63 ∧
       g'.slots = [.liveUser p req (max req MallocngMinBlockCost)] ∧
       g'.maplen * 4096 ≤ req + 4115)

/-- Raw budget-uncommitted `__libc_malloc_impl(req)` (`blk09`, `704` B stack) contract over `FineEnv`:
    returns `st0, alignMap0, st', g', idx, bCoarse` satisfying `MallocImplFineRawRel` together with
    `ghostMapAuth (fineAlignGam γ) alignMap0`, `MallocngCoreStA (fineBaseGam γ) ... st'`,
    `(p ↦ₛ bs)`, and `MallocngBlockToken (fineBaseGam γ) p req`. -/
noncomputable def libcMallocImplFineRawSpec [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat) : Spec Unit :=
  let ok := decide (req ≤ MallocngMaxAllocSize)
  let stepB := fineStepReserve (if ok then .alloc req else .alloc 0) b
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜(s0.readReg64 .x0).toNat = req⌝ ∗
      stackFrame s0 704 ∗
      FineEnv γ maddrs tp brkStart b ivs0 s0
    post := fun _ s0 sf =>
      ⌜MallocngProcPreserved s0 sf ∧
       MallocngMappedDelta 16 stepB s0.mem sf.mem⌝ ∗
      stackFrame s0 704 ∗
      if req ≤ MallocngMaxAllocSize then
        ∃∗ p : BitVec 64,
        ∃∗ bs : List (BitVec 8),
        ∃∗ st0 : MallocngSt,
        ∃∗ alignMap0 : BitVec 64 → Option Nat,
        ∃∗ st' : MallocngSt,
        ∃∗ g' : GroupDesc,
        ∃∗ idx : Nat,
        ∃∗ bCoarse : MallocngBudget,
          ⌜sf.readReg64 .x0 = p ∧
           sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
           MallocngBlockWf p req ∧
           bs.length = req ∧
           MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngWF maddrs.base brkStart sf.brk bCoarse.liveCost bCoarse.peakCost st' ∧
           MallocngCountIvsWF bCoarse (dynamicRootRegions st') st' ∧
           MallocImplFineRawRel maddrs.base brkStart b ivs0 alignMap0 st0 st' g' idx req p ∧
           (g'.isMmapped = true → bs = List.replicate req 0#8)⌝ ∗
          MallocngRoTablesA maddrs ∗
          ghostMapAuth (fineAlignGam γ) alignMap0 ∗
          MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk
            bCoarse.liveCost bCoarse.peakCost st' ∗
          MallocngRuntime maddrs tp ∗
          (p ↦ₛ bs) ∗
          MallocngBlockToken (fineBaseGam γ) p req
      else
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        FinePostEnv γ maddrs tp brkStart b ivs0 s0 sf
    onOom := fun _ s0 sf => ⌜FineStepOomCond msvc stepB s0 sf⌝
  }

def LibcMallocImplFineRawStmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
    subroutine_ok (mallocngBlockProg mmpl 9 msvc) (mbase 9)
      (libcMallocImplFineRawSpec γ tp brkStart b ivs0 req)

/-- Committed `align = 16` (`FineBudget.stepAlloc req b`) contract for `__libc_malloc_impl` (`blk09`)
    and `default_malloc` (`blk04`), retaining the `st'` witness for `calloc`'s `isMmapped` fast path. -/
noncomputable def libcMallocImplFineSpec [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat) : Spec Unit :=
  let ok := decide (req ≤ MallocngMaxAllocSize)
  let bf := if ok then FineBudget.stepAlloc req b else b
  let stepB := fineStepReserve (if ok then .alloc req else .alloc 0) b
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜(s0.readReg64 .x0).toNat = req⌝ ∗
      stackFrame s0 704 ∗
      FineEnv γ maddrs tp brkStart b ivs0 s0
    post := fun _ s0 sf =>
      ⌜MallocngProcPreserved s0 sf ∧
       MallocngMappedDelta 16 stepB s0.mem sf.mem⌝ ∗
      stackFrame s0 704 ∗
      if req ≤ MallocngMaxAllocSize then
        ∃∗ p : BitVec 64,
        ∃∗ bs : List (BitVec 8),
        ∃∗ st' : MallocngSt,
        ∃∗ alignMap' : BitVec 64 → Option Nat,
        ∃∗ live' : Nat,
        ∃∗ peak' : Nat,
          ⌜sf.readReg64 .x0 = p ∧
           sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
           MallocngBlockWf p req ∧
           bs.length = req ∧
           MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
           ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
             g'.slots[idx]'hIdx = .liveUser p req (max req MallocngMinBlockCost) ∧
             p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
             (g'.isMmapped = true → bs = List.replicate req 0#8)⌝ ∗
          MallocngRoTablesA maddrs ∗
          FineCoreStInflightA 0 γ maddrs brkStart sf.brk bf
            (dynamicRootRegions st') alignMap' live' peak' st' ∗
          MallocngRuntime maddrs tp ∗
          (p ↦ₛ bs) ∗
          FineBlock γ p req 16
      else
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf
    onOom := fun _ s0 sf => ⌜FineStepOomCond msvc stepB s0 sf⌝
  }

def LibcMallocImplFineStmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
    subroutine_ok (mallocngBlockProg mmpl 9 msvc) (mbase 9)
      (libcMallocImplFineSpec γ tp brkStart b ivs0 req)

def DefaultMallocFineStmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
    subroutine_ok (mallocngBlockProg mmpl 4 msvc) (mbase 4)
      (libcMallocImplFineSpec γ tp brkStart b ivs0 req)

/-! ## Placed C Entrypoint Contracts -/

/-- Fine-model `void *malloc(size_t req)` contract. -/
c_type_spec fineMallocSpec (ctx svc : State → State) (ctx γ : GhostName)
    (ctx A : MallocngAddrs) (load_addr _b)
    (req : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost b : FineBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := decide (req.toNat ≤ MallocngMaxAllocSize)
  let ev := FineEvent.alloc req.toNat
  let b' := if ok then FineBudget.step ev b else b
  let stepB := if ok then fineStepReserve ev b else fineStepReserve (.alloc 0) b
  c_arg req : Val SizeT
  c_ret : Own (OptOwn (FineBlockSem γ))
    (if ok then some (req.toNat, 16) else none)
  c_env (FineEnv γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (FinePostEnv γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting 16 stepB s0 sf
  oom_when FineStepOomCond svc stepB s0 sf

/-- Fine-model `void free(void *p)` contract. -/
c_type_spec fineFreeSpec (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (p : ptr) (sp : sp)
    (ghost n align : Nat) (ghost tp brkStart : BitVec 64) (ghost b : FineBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) where
  let b' := if p == 0#64 then b else FineBudget.step (.free align n) b
  c_arg p : Own (FineFreeableBlockSem γ) (n, align)
  c_env (FineEnv γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (FinePostEnv γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting 0 0 s0 sf

/-- Fine-model `void *calloc(size_t nmemb, size_t size)` contract. -/
c_type_spec fineCallocSpec (ctx svc : State → State) (ctx γ : GhostName)
    (ctx A : MallocngAddrs) (load_addr _b)
    (nmemb : u64) (size : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost b : FineBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let total := nmemb.toNat * size.toNat
  let ok := decide (total ≤ MallocngMaxAllocSize)
  let ev := FineEvent.alloc total
  let b' := if ok then FineBudget.step ev b else b
  let stepB := if ok then fineStepReserve ev b else fineStepReserve (.alloc 0) b
  c_arg nmemb : Val SizeT
  c_arg size : Val SizeT
  c_ret : Own (OptOwn (FineZeroedBlockSem γ))
    (if ok then some (total, 16) else none)
  c_env (FineEnv γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (FinePostEnv γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting 16 stepB s0 sf
  oom_when FineStepOomCond svc stepB s0 sf

/-- Fine-model `void *realloc(void *p, size_t newSize)` contract. -/
c_type_spec fineReallocSpec (ctx svc : State → State) (ctx γ : GhostName)
    (ctx A : MallocngAddrs) (load_addr _b)
    (p : ptr) (newSize : u64) (sp : sp)
    (ghost oldBlk : Option (Nat × Nat × List (BitVec 8)))
    (ghost tp brkStart : BitVec 64) (ghost b : FineBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
  let keptBs := ((oldBlk.map fun (_, _, bs) => bs).getD []).take newSize.toNat
  let ev : FineEvent := match oldBlk with
    | none => .alloc newSize.toNat
    | some (oldSize, align, _) => .realloc align oldSize newSize.toNat
  let evRes : FineEvent := match oldBlk with
    | none => .realloc 16 0 newSize.toNat
    | some (oldSize, align, _) => .realloc align oldSize newSize.toNat
  let outAlign : Nat := match oldBlk with
    | none => 16
    | some (_, align, _) => max align 16
  let b' := if ok then FineBudget.step ev b else b
  let stepB := if ok then fineStepReserve evRes b else fineStepReserve (.alloc 0) b
  c_arg p : MutRef (CondOwn (OptOwn (FineInitBlockSem γ))) (some oldBlk) ⇝
    (if ok then none else some oldBlk)
  c_arg newSize : Val SizeT
  c_ret : Own (OptOwn (FineInitBlockSem γ))
    (if ok then some (newSize.toNat, outAlign, keptBs) else none)
  c_env (FineEnv γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (FinePostEnv γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting 16 stepB s0 sf
  oom_when FineStepOomCond svc stepB s0 sf

/-- Fine-model `void *aligned_alloc(size_t align, size_t len)` contract. -/
c_type_spec fineAlignedAllocSpec (ctx svc : State → State) (ctx γ : GhostName)
    (ctx A : MallocngAddrs) (load_addr _b)
    (align : u64) (len : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost b : FineBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := mallocngAlignedAllocOk align len
  let ev := FineEvent.aligned align.toNat len.toNat
  let b' := if ok then FineBudget.step ev b else b
  let stepB := if ok then fineStepReserve ev b else fineStepReserve (.alloc 0) b
  caveat [API_RESTRICTION] "align ≤ 2^31 avoids musl 1.2.5 set_size int32 reserved overflow" :
    align.toNat ≤ MaxAlignedAllocAlign
  c_arg align : Val SizeT
  c_arg len : Val SizeT
  c_ret : Own (OptOwn (FineBlockSem γ))
    (if ok then some (len.toNat, max align.toNat 16) else none)
  c_env (FineEnv γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (FinePostEnv γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting 16 stepB s0 sf
  oom_when FineStepOomCond svc stepB s0 sf

/-- Fine-model `int posix_memalign(void **res, size_t align, size_t len)` contract. -/
c_type_spec finePosixMemalignSpec (ctx svc : State → State) (ctx γ : GhostName)
    (ctx A : MallocngAddrs) (load_addr _b)
    (res : ptr) (align : u64) (len : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost b : FineBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : u32) where
  let ok := mallocngPosixMemalignOk align len
  let ev := FineEvent.aligned align.toNat len.toNat
  let b' := if ok then FineBudget.step ev b else b
  let stepB := if ok then fineStepReserve ev b else fineStepReserve (.alloc 0) b
  caveat [API_RESTRICTION] "align ≤ 2^31 avoids musl 1.2.5 set_size int32 reserved overflow" :
    align.toNat ≤ MaxAlignedAllocAlign
  c_arg res : MutRef (OptOutPtr (FineBlockSem γ)) none ⇝
    (if ok then some (len.toNat, max align.toNat 16) else none)
  c_arg align : Val SizeT
  c_arg len : Val SizeT
  c_env (FineEnv γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (FinePostEnv γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  returns mallocngPosixMemalignRet align len
  ensures_pure MallocngCallAccounting 16 stepB s0 sf
  oom_when FineStepOomCond svc stepB s0 sf

end LibsignalBinary.Heap.Fine
