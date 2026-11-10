/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ReallocNullStage4Fine
public import LibsignalBinary.Heap.Fine.MallocImplFine

/-!
# Fine-Grained Placed `__libc_realloc` Non-Null Path

Verifies the non-null path (`oldBlk = some (oldSz, align, origBs)`, `p ≠ 0#64`) of placed
`__libc_realloc` (`blk14`) over `FineBudget`, dispatching between Stage 2 in-place `set_size`,
Stage 3 individual-`mmap` `mremap`, and Stage 4 out-of-place `malloc + memcpy + free`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj Arm64.CType ProofLib ProofLib.SepLogic
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Stage 2 and Stage 3 Continuation Contracts -/

/-- Fine-model Stage-2 continuation (`+0x2cc` → `ret`, in-place `set_size(p, end, newSz)` for
    `g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1`, `newSz ≤ 131051`, `p.toNat + newSz ≤ (g.slotEnd idx).toNat`). -/
def ReallocStage2FineStmt : Prop :=
  ∀ [MallocngMultiPlacement] {b : BitVec 64} (_hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt) (alignMap0 : BitVec 64 → Option Nat) (live0 peak0 : Nat)
    {g : GroupDesc} (_hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz align oldEff newSz : Nat} (origBs tailBs : List (BitVec 8))
    (_hInv0 : MallocngFineInv 0 bgt ivs0 alignMap0 st)
    (_hwf0 : MallocngWF maddrs.base brkStart s0.brk live0 peak0 st)
    (_hAlign0 : alignMap0 p = some (max align 16)) (_hpNe : p ≠ 0#64)
    (_hOrigLen : origBs.length ≤ oldSz) (_hTailLen : tailBs.length = oldSz - origBs.length)
    (_hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (_hF : LiveUserBlockFacts st g idx p oldSz oldEff)
    (_hNewMax : newSz ≤ 131051) (_hFit : p.toNat + newSz ≤ (g.slotEnd idx).toNat)
    (_hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1)
    {Frame : SepProp}
    (_hpc : s.pc = b + 0x2cc#64) (_hrun : s.status = .Running)
    (_hPerm : s.mem.perm = s0.mem.perm) (_hbrk : s.brk = s0.brk)
    (_hproc : MallocngProcPreserved s0 s) (_htp0 : s0.tpidrEl0 = tp) (_hbrks0 : s0.brkStart = brkStart)
    (_hsp : s.sp = s0.sp - 80#64) (_hal : s.spAligned = true) (_hsp0 : s0.sp &&& 15#64 = 0#64)
    (_hx3 : s.readReg64 .x3 = BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat))
    (_hx4 : s.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64) (_hx5 : s.readReg64 .x5 = g.slotEnd idx)
    (_hx19 : s.readReg64 .x19 = p) (_hx21 : s.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (_hcs : ReallocUntouchedCS s0 s) (_hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem),
    let sp1 := s0.sp - 80#64
    let bCoarse := synthCoarseBudget live0 peak0 st
    let bf := FineBudget.stepRealloc align oldSz newSz bgt
    let stepB := fineStepReserve (.realloc align oldSz newSz) bgt
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
       MallocngBlockToken (fineBaseGam γ) p oldSz ∗
       ghostMapAuth (fineAlignGam γ) alignMap0 ∗ ghostMapElem (fineAlignGam γ) p (max align 16) ∗
       (p ↦ₛ (origBs ++ tailBs)) ∗ Frame)
      (fun sf Pf =>
        ∃ q : BitVec 64,
          MallocngCallAccounting 16 stepB s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q ∧
          (Pf ⊢ stackFrame s0 800 ∗ FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(FineInitBlockSem γ).pureWf q (newSz, max align 16, keptBs)⌝ ∗
            (FineInitBlockSem γ).interp q (newSz, max align 16, keptBs) ∗ Frame))
      (fun sf => ⌜FineStepOomCond msvc stepB s0 sf⌝)

/-- Fine-model Stage-3 continuation (`+0x324` → `ret`, individual-`mmap` `mremap` / Stage-4 fallback). -/
def ReallocStage3FineStmt : Prop :=
  ∀ [MallocngMultiPlacement] {b : BitVec 64} (_hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt) (alignMap0 : BitVec 64 → Option Nat) (live0 peak0 : Nat)
    {p : BitVec 64} {oldSz align oldEff newSz : Nat}
    {g : GroupDesc} (_hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (origBs tailBs : List (BitVec 8))
    (_hInv0 : MallocngFineInv 0 bgt ivs0 alignMap0 st)
    (_hwf0 : MallocngWF maddrs.base brkStart s0.brk live0 peak0 st)
    (_hAlign0 : alignMap0 p = some (max align 16)) (_hpNe : p ≠ 0#64)
    (_hOrigLe : origBs.length ≤ oldSz) (_hTailLen : tailBs.length = oldSz - origBs.length)
    (_hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (_hF : LiveUserBlockFacts st g idx p oldSz oldEff) (_hNewMax : newSz ≤ MallocngMaxAllocSize)
    {Frame : SepProp}
    (_hpc : s.pc = b + 0x324#64) (_hrun : s.status = .Running)
    (_hPerm : s.mem.perm = s0.mem.perm) (_hbrk : s.brk = s0.brk)
    (_hproc : MallocngProcPreserved s0 s) (_htp0 : s0.tpidrEl0 = tp) (_hbrks0 : s0.brkStart = brkStart)
    (_hsp : s.sp = s0.sp - 80#64) (_hal : s.spAligned = true) (_hsp0 : s0.sp &&& 15#64 = 0#64)
    (_hx0 : s.readReg64 .x0 = g.mem) (_hx1 : s.readReg64 .x1 = g.packedWord)
    (_hx2 : s.readReg64 .x2 = 131051#64) (_hx6 : s.readReg64 .x6 = BitVec.ofNat 64 g.sc)
    (_hx7 : s.readReg64 .x7 = (g.packedWord.extractLsb' 0 16).zeroExtend 64)
    (_hx19 : s.readReg64 .x19 = p) (_hx20 : s.readReg64 .x20 = g.slotStart idx)
    (_hx21 : s.readReg64 .x21 = BitVec.ofNat 64 newSz) (_hx22 : s.readReg64 .x22 = g.metaPtr)
    (_hx23 : s.readReg64 .x23 = p + BitVec.ofNat 64 oldSz) (_hx24 : s.readReg64 .x24 = 0#64)
    (_hcs : ReallocUntouchedCS s0 s) (_hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem),
    let sp1 := s0.sp - 80#64
    let bCoarse := synthCoarseBudget live0 peak0 st
    let bf := FineBudget.stepRealloc align oldSz newSz bgt
    let stepB := fineStepReserve (.realloc align oldSz newSz) bgt
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
       MallocngBlockToken (fineBaseGam γ) p oldSz ∗
       ghostMapAuth (fineAlignGam γ) alignMap0 ∗ ghostMapElem (fineAlignGam γ) p (max align 16) ∗
       (p ↦ₛ (origBs ++ tailBs)) ∗ Frame)
      (fun sf Pf =>
        ∃ q : BitVec 64,
          MallocngCallAccounting 16 stepB s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q ∧
          (Pf ⊢ stackFrame s0 800 ∗ FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(FineInitBlockSem γ).pureWf q (newSz, max align 16, keptBs)⌝ ∗
            (FineInitBlockSem γ).interp q (newSz, max align 16, keptBs) ∗ Frame))
      (fun sf => ⌜FineStepOomCond msvc stepB s0 sf⌝)

/-! ## `FineHeapImpl` Read Unpack and Stage 4 Repack Bridges -/

theorem fineInitBlockSem_interp_max16 (γ : GhostName) (q : BitVec 64)
    (sz align : Nat) (bs : List (BitVec 8)) :
    (FineInitBlockSem γ).interp q (sz, max align 16, bs) =
      (FineInitBlockSem γ).interp q (sz, align, bs) := by
  dsimp only [FineInitBlockSem]
  rw [Nat.max_eq_left (Nat.le_max_right align 16)]

/-- Unpacks `FineHeapImpl` + `FineBlock γ p oldSz (max align 16)` for read-only Stage-1 inspection,
    producing `hInv0`, `hwf0`, `hAlign0`, `LiveUserBlockFacts`, `MallocngReadRest (fineBaseGam γ)`
    at `synthCoarseBudget live0 peak0 st`, and the `fineAlignGam γ` ghost auth/elem pair. -/
theorem fineHeap_read_liveUser_unpack (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64) (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (p : BitVec 64) (oldSz align : Nat) :
    FineHeapImpl γ A tp brkStart brk bgt ivs0 ∗ FineBlock γ p oldSz (max align 16) ⊢
      ∃∗ st : MallocngSt,
      ∃∗ alignMap0 : BitVec 64 → Option Nat,
      ∃∗ live0 : Nat,
      ∃∗ peak0 : Nat,
      ∃∗ g : GroupDesc,
      ∃∗ idx : Nat,
      ∃∗ oldEff : Nat,
        ⌜MallocngFineInv 0 bgt ivs0 alignMap0 st ∧
          MallocngWF A.base brkStart brk live0 peak0 st ∧
          alignMap0 p = some (max align 16) ∧
          g ∈ st.groups ∧
          (∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .liveUser p oldSz oldEff) ∧
          LiveUserBlockFacts st g idx p oldSz oldEff⌝ ∗
        MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MallocngReadRest (fineBaseGam γ) A tp brkStart brk
          (synthCoarseBudget live0 peak0 st) ivs0 st ∗
        MallocngBlockToken (fineBaseGam γ) p oldSz ∗
        ghostMapAuth (fineAlignGam γ) alignMap0 ∗
        ghostMapElem (fineAlignGam γ) p (max align 16) := by
  rw [FineHeapImpl_eq, FineCoreImpl_eq]
  unfold MallocngRoTablesA
  rw [sepConj_assoc, sepConj_assoc]
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_mono fun st => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_mono fun alignMap0 => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_mono fun live0 => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_mono fun peak0 => ?_
  unfold FineCoreStInflightA MallocngCoreStInflightA
  refine Entails.trans (Entails.of_eq (show _ =
      ⌜MallocngFineInv 0 bgt ivs0 alignMap0 st⌝ ∗
      ⌜MallocngWF A.base brkStart brk live0 peak0 st⌝ ∗
      ((ghostMapAuth (fineAlignGam γ) alignMap0 ∗
        MallocngLiveAuth (fineBaseGam γ) st.liveMap ∗
        FineBlock γ p oldSz (max align 16)) ∗
       (MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32) ∗
        ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
        MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MappedSet st.masterDom (OwnedMappedByte st) ∗
        MallocngRuntime A tp)) by
    dsimp only [MallocngWF]
    generalize (MallocngRoTablesAt A) = PRo
    generalize (MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap) = PAu
    generalize (FineBlock γ p oldSz (max align 16)) = PBlk
    ac_rfl)) ?_
  refine Entails.pure_left fun hInv0 => Entails.pure_left fun hwf0 => ?_
  refine Entails.trans
    (sepConj_mono_left (fineBlock_lookup γ st.liveMap alignMap0 p oldSz (max align 16))) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨_, _, hLive, hAlign0⟩ => ?_
  obtain ⟨g, hg, idx, hIdx, oldEff, hSlot⟩ := (hwf0.liveMap_wf p oldSz).mp hLive
  have hFacts := liveUserBlockFacts_of hwf0 hg hIdx hSlot
  have hIvsEq : ivs0 = dynamicRootRegions st := hInv0.ivs_eq rfl
  have hCount : MallocngCountIvsWF (synthCoarseBudget live0 peak0 st) ivs0 st :=
    hIvsEq ▸ synthCoarseBudget_countIvsWF st (groupsGrpBound_128_of_geom hInv0.groups_geom)
  have hwfCoarse :
      MallocngWF A.base brkStart brk
        (synthCoarseBudget live0 peak0 st).liveCost
        (synthCoarseBudget live0 peak0 st).peakCost st := hwf0
  refine Entails.sepExists_right g (Entails.sepExists_right idx (Entails.sepExists_right oldEff ?_))
  refine Entails.pure_right ⟨hInv0, hwf0, hAlign0, hg, ⟨hIdx, hSlot⟩, hFacts⟩ ?_
  unfold FineBlock MallocngReadRest
  rw [pure_sepConj_of_true (Nat.le_max_right align 16)]
  rw [pure_sepConj_of_true ⟨hCount, hwfCoarse⟩]
  exact Entails.of_eq (by
    generalize (MallocngRoTablesAt A) = PRo
    generalize (MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap) = PAu
    ac_rfl)

/-- Repacks `MallocngReadRest (fineBaseGam γ)` + `ghostMapAuth (fineAlignGam γ) alignMap0` + `hInv0`
    and `MallocngBlockToken ∗ ghostMapElem` back into `FineEnv` + `FineBlock` for Stage-4 fallback
    (`+0x260` → `ret`). -/
theorem repack_fine_read_to_stage4 [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt) (alignMap0 : BitVec 64 → Option Nat) (live0 peak0 : Nat)
    (hInv0 : MallocngFineInv 0 bgt ivs0 alignMap0 st)
    {p : BitVec 64} {oldSz align : Nat} (origBs tailBs : List (BitVec 8))
    (hTailLen : tailBs.length = oldSz - origBs.length)
    (hbrk : s.brk = s0.brk) (htp : s.tpidrEl0 = tp) (hbrks : s.brkStart = brkStart)
    (sp1 : BitVec 64) (Frame : SepProp) :
    (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
     MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
     ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
     MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk
       (synthCoarseBudget live0 peak0 st) ivs0 st ∗
     MallocngBlockToken (fineBaseGam γ) p oldSz ∗
     ghostMapAuth (fineAlignGam γ) alignMap0 ∗
     ghostMapElem (fineAlignGam γ) p (max align 16) ∗
     (p ↦ₛ (origBs ++ tailBs)) ∗ Frame) ⊢
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       FineEnv γ maddrs tp brkStart bgt ivs0 s ∗
       FineBlock γ p oldSz (max align 16) ∗
       (p ↦ₛ origBs) ∗ memRegion (p + BitVec.ofNat 64 origBs.length) (oldSz - origBs.length) ∗
       Frame) := by
  have hHeap :
      MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
      MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk
        (synthCoarseBudget live0 peak0 st) ivs0 st ∗
      ghostMapAuth (fineAlignGam γ) alignMap0 ⊢
        FineEnv γ maddrs tp brkStart bgt ivs0 s := by
    unfold MallocngReadRest
    refine Entails.trans (Entails.of_eq (show _ =
        ⌜MallocngCountIvsWF (synthCoarseBudget live0 peak0 st) ivs0 st ∧
          MallocngWF maddrs.base brkStart s0.brk
            (synthCoarseBudget live0 peak0 st).liveCost
            (synthCoarseBudget live0 peak0 st).peakCost st⌝ ∗
        (MallocngRoTablesAt maddrs ∗
         (ghostMapAuth (fineAlignGam γ) alignMap0 ∗
          MallocngLiveAuth (fineBaseGam γ) st.liveMap ∗
          (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
          (maddrs.lock ↦₃₂ 0#32) ∗
          (maddrs.replaced ↦₃₂ 0#32) ∗
          (maddrs.aaReplaced ↦₃₂ 0#32) ∗
          ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
          MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
          ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st)) ∗
         MallocngRuntime maddrs tp) by
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap) = PAu
      ac_rfl)) ?_
    refine Entails.pure_left fun ⟨_, hwf0⟩ => ?_
    have hwfS : MallocngWFInflight 0 maddrs.base brkStart s.brk live0 peak0 st := by
      rw [hbrk]; exact hwf0
    unfold FineEnv
    refine Entails.pure_right ⟨htp, hbrks⟩ ?_
    rw [FineHeapImpl_eq, FineCoreImpl_eq]
    unfold MallocngRoTablesA
    have hBody :
        ghostMapAuth (fineAlignGam γ) alignMap0 ∗
        MallocngLiveAuth (fineBaseGam γ) st.liveMap ∗
        (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        (maddrs.lock ↦₃₂ 0#32) ∗
        (maddrs.replaced ↦₃₂ 0#32) ∗
        (maddrs.aaReplaced ↦₃₂ 0#32) ∗
        ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
        MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MappedSet st.masterDom (OwnedMappedByte st) ⊢
        ∃∗ st' : MallocngSt,
        ∃∗ alignMap' : BitVec 64 → Option Nat,
        ∃∗ live' : Nat,
        ∃∗ peak' : Nat,
          FineCoreStInflightA 0 γ maddrs brkStart s.brk bgt ivs0 alignMap' live' peak' st' := by
      refine Entails.sepExists_right st
        (Entails.sepExists_right alignMap0
          (Entails.sepExists_right live0 (Entails.sepExists_right peak0 ?_)))
      unfold FineCoreStInflightA MallocngCoreStInflightA
      rw [pure_sepConj_of_true hInv0, pure_sepConj_of_true hwfS]
      exact Entails.of_eq (by
        generalize (MallocngAuxvState (fineBaseGam γ) st.auxvPtr st.auxvSnap) = PAu
        ac_rfl)
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left hBody)) ?_
    exact Entails.of_eq (by
      generalize (MallocngRoTablesAt maddrs) = PRo
      ac_rfl)
  have hBlk :
      MallocngBlockToken (fineBaseGam γ) p oldSz ∗
      ghostMapElem (fineAlignGam γ) p (max align 16) ⊢
        FineBlock γ p oldSz (max align 16) := by
    unfold FineBlock
    exact Entails.pure_right (Nat.le_max_right align 16) (Entails.refl _)
  have hUser := unsplit_user_bytes p origBs tailBs oldSz hTailLen
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine Entails.trans (Q :=
      (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk
         (synthCoarseBudget live0 peak0 st) ivs0 st ∗
       ghostMapAuth (fineAlignGam γ) alignMap0) ∗
      (MallocngBlockToken (fineBaseGam γ) p oldSz ∗
       ghostMapElem (fineAlignGam γ) p (max align 16)) ∗
      (p ↦ₛ (origBs ++ tailBs)) ∗ Frame)
    (Entails.of_eq (by
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk
        (synthCoarseBudget live0 peak0 st) ivs0 st) = PRest
      ac_rfl)) ?_
  refine sepConj_mono hHeap (sepConj_mono hBlk ?_)
  exact Entails.trans (sepConj_mono_left hUser) (Entails.of_eq (by ac_rfl))

/-! ## Post-`size_to_class` Dispatch and Non-Null Path -/

private theorem procPreserved_setPState_setPC_fine {s0 s : State} (ps : PState) (pc : BitVec 64)
    (h : MallocngProcPreserved s0 s) :
    MallocngProcPreserved s0 ((s.setPState ps).setPC pc) := h

private theorem untouchedCS_setPState_setPC_fine {s0 s : State} (ps : PState) (pc : BitVec 64)
    (h : ReallocUntouchedCS s0 s) :
    ReallocUntouchedCS s0 ((s.setPState ps).setPC pc) :=
  ⟨h.1, h.2.1, h.2.2⟩

private theorem realloc_post_sc_fine_ok [MallocngMultiPlacement]
    (hStage2 : ReallocStage2FineStmt)
    {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart p : BitVec 64)
    (oldSz align oldEff newSz : Nat) (origBs tailBs : List (BitVec 8))
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 sSc : State) (st : MallocngSt) (alignMap0 : BitVec 64 → Option Nat) (live0 peak0 : Nat)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hInv0 : MallocngFineInv 0 bgt ivs0 alignMap0 st)
    (hwf0 : MallocngWF maddrs.base brkStart s0.brk live0 peak0 st)
    (hAlign0 : alignMap0 p = some (max align 16))
    (hpNe : p ≠ 0#64)
    (hOrigLe : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hF : LiveUserBlockFacts st g idx p oldSz oldEff)
    (hNewMax : newSz ≤ MallocngMaxAllocSize) (hNew131 : newSz ≤ 131051)
    (hFit : p.toNat + newSz ≤ (g.slotEnd idx).toNat)
    (hpcSc : sSc.pc = b + 0x258#64) (hrunSc : sSc.status = .Running)
    (hPermSc : sSc.mem.perm = s0.mem.perm) (hclSc : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sSc.mem)
    (hbrkSc0 : sSc.brk = s0.brk) (hprocSc0 : MallocngProcPreserved s0 sSc)
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart)
    (hspSc0 : sSc.sp = s0.sp - 80#64) (hspMask0 : s0.sp &&& 15#64 = 0#64)
    (hw2_sc : sSc.readReg32 .x2 = BitVec.ofNat 32 (sizeToClassUnits ((newSz + 3) / 16) + 1))
    (hx3Sc0 : sSc.readReg64 .x3 = BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat))
    (hx4Sc0 : sSc.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx5Sc0 : sSc.readReg64 .x5 = g.slotEnd idx)
    (hx6Sc0 : sSc.readReg64 .x6 = BitVec.ofNat 64 g.sc)
    (hx19Sc0 : sSc.readReg64 .x19 = p)
    (hx21_sc : sSc.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (hx23Sc0 : sSc.readReg64 .x23 = p + BitVec.ofNat 64 oldSz)
    (hcsSc0 : ReallocUntouchedCS s0 sSc)
    {post : State → SepProp → Prop}
    (hFinishPost : ∀ sf Pf,
      (∃ q : BitVec 64,
        MallocngCallAccounting 16
          (fineStepReserve (.realloc align oldSz newSz) bgt) s0 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q ∧
        (Pf ⊢ stackFrame s0 800 ∗
          FinePostEnv γ maddrs tp brkStart
            (FineBudget.stepRealloc align oldSz newSz bgt) ivs0 s0 sf ∗
          ⌜(FineInitBlockSem γ).pureWf q (newSz, max align 16, origBs.take newSz)⌝ ∗
          (FineInitBlockSem γ).interp q (newSz, max align 16, origBs.take newSz) ∗ emp)) →
      post sf Pf) :
    let sp1 := s0.sp - 80#64
    let bCoarse := synthCoarseBudget live0 peak0 st
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) sSc
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
       MallocngBlockToken (fineBaseGam γ) p oldSz ∗
       ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       ghostMapElem (fineAlignGam γ) p (max align 16) ∗
       (p ↦ₛ (origBs ++ tailBs)) ∗ emp)
      post
      (fun sf => ⌜FineStepOomCond msvc (fineStepReserve (.realloc align oldSz newSz) bgt) s0 sf⌝) := by
  intro sp1 bCoarse; have _ := hb
  apply sepWP_abstract_all; intro PG postG oomG hPG hPostG hOomG
  generalize hw2Val : BitVec.ofNat 32 (sizeToClassUnits ((newSz + 3) / 16) + 1) = w2v at hw2_sc
  wp_step; wp_step
  wp_if hleSc
  · subst hPG hPostG hOomG
    have hScLt31 : g.sc < 2 ^ 31 := by rcases hF.sc_cases with h | h <;> omega
    have hUnitsLt48 := sizeToClassUnits_lt_48 (u := (newSz + 3) / 16) (by omega)
    have hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1 := by
      have hTrunc6 : BitVec.truncate 32 (BitVec.ofNat 64 g.sc) = BitVec.ofNat 32 g.sc := by bv_omega
      dsimp only [State.readReg32] at hw2_sc
      try rw [hx6Sc0] at hleSc
      try rw [hw2_sc] at hleSc
      rw [hTrunc6, ← hw2Val,
          VerifiedLibraries.Mallocng.Proofs.bv32_sle_iff_of_lt31 hScLt31 (by omega),
          decide_eq_true_eq] at hleSc
      exact hleSc
    apply sepWP_bind_state; intro sS2 hsS2
    have hmS2 : sS2.mem = sSc.mem := by rw [hsS2, State.mem_setPC, State.mem_setPState]
    refine SepWP.mono (hStage2 hb γ tp brkStart bgt ivs0 s0 sS2 st alignMap0 live0 peak0
      hg hIdx origBs tailBs hInv0 hwf0 hAlign0 hpNe hOrigLe hTailLen hSlot hF
      hNew131 hFit hScLe (Frame := emp)
      (by rw [hsS2, State.pc_setPC])
      (by rw [hsS2, State.status_setPC, State.status_setPState]; exact hrunSc)
      (by rw [hmS2]; exact hPermSc)
      (by rw [hsS2, State.brk_setPC, State.brk_setPState]; exact hbrkSc0)
      (by rw [hsS2]; exact procPreserved_setPState_setPC_fine _ _ hprocSc0) htp0 hbrks0
      (by rw [hsS2, State.sp_setPC, State.sp_setPState]; exact hspSc0)
      (spAligned_of_sub80 (by rw [hsS2, State.sp_setPC, State.sp_setPState]; exact hspSc0) hspMask0)
      hspMask0
      (by rw [hsS2, State.readReg64_setPC, State.readReg64_setPState]; exact hx3Sc0)
      (by rw [hsS2, State.readReg64_setPC, State.readReg64_setPState]; exact hx4Sc0)
      (by rw [hsS2, State.readReg64_setPC, State.readReg64_setPState]; exact hx5Sc0)
      (by rw [hsS2, State.readReg64_setPC, State.readReg64_setPState]; exact hx19Sc0)
      (by rw [hsS2, State.readReg64_setPC, State.readReg64_setPState]; exact hx21_sc)
      (by rw [hsS2]; exact untouchedCS_setPState_setPC_fine _ _ hcsSc0)
      (by rw [hmS2]; exact hclSc))
      (fun sf Pf _ _ hPost => hFinishPost sf Pf hPost)
  · subst hPG hPostG hOomG
    apply sepWP_bind_state; intro sS4 hsS4
    have hmS4 : sS4.mem = sSc.mem := by rw [hsS4, State.mem_setPC, State.mem_setPState]
    have hbrkS4 : sS4.brk = s0.brk := by rw [hsS4, State.brk_setPC, State.brk_setPState]; exact hbrkSc0
    have hprocS4 : MallocngProcPreserved s0 sS4 := by
      rw [hsS4]; exact procPreserved_setPState_setPC_fine _ _ hprocSc0
    refine SepWP.weaken_pre (repack_fine_read_to_stage4 γ tp brkStart bgt ivs0 s0 sS4 st
      alignMap0 live0 peak0 hInv0 (align := align) origBs tailBs hTailLen
      hbrkS4 (hprocS4.2.2.1.trans htp0) (hprocS4.2.2.2.1.trans hbrks0)
      sp1 emp) ?_
    refine SepWP.mono (realloc_stage4_oop_fine_ok placed_libcMallocImpl_raw_fine_ok hb
      γ tp brkStart bgt ivs0 s0 sS4 (oldSz := oldSz) (align := align) (newSz := newSz) origBs (Frame := emp)
      hpNe (Nat.le_trans hF.p_add_n_le_end hF.stride_bounds.2.2.2.2.2) hOrigLe hNewMax
      (by rw [hsS4, State.pc_setPC])
      (by rw [hsS4, State.status_setPC, State.status_setPState]; exact hrunSc)
      (by rw [hmS4]; exact hPermSc) hprocS4
      (by rw [hsS4, State.sp_setPC, State.sp_setPState]; exact hspSc0)
      (spAligned_of_sub80 (by rw [hsS4, State.sp_setPC, State.sp_setPState]; exact hspSc0) hspMask0)
      hspMask0
      (by rw [hsS4, State.readReg64_setPC, State.readReg64_setPState]; exact hx19Sc0)
      (by rw [hsS4, State.readReg64_setPC, State.readReg64_setPState]; exact hx21_sc)
      (by rw [hsS4, State.readReg64_setPC, State.readReg64_setPState]; exact hx23Sc0)
      (by rw [hsS4]; exact untouchedCS_setPState_setPC_fine _ _ hcsSc0)
      (by rw [hmS4]; exact hclSc))
      (fun sf Pf _ _ hPost => hFinishPost sf Pf hPost)

set_option maxHeartbeats 400000 in
/-- Placed `__libc_realloc` (`blk14`) on the non-null path (`oldBlk = some (oldSz, align, origBs)`,
    `p ≠ 0#64`), parameterized only over `ReallocStage2FineStmt` and `ReallocStage3FineStmt`. -/
theorem realloc_nonnull_path_fine_ok [MallocngMultiPlacement]
    (hStage2 : ReallocStage2FineStmt) (hStage3 : ReallocStage3FineStmt)
    {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart p newSize : BitVec 64)
    (oldSz align : Nat) (origBs : List (BitVec 8))
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 : State) (R : SepProp)
    (hpWf : (FineInitBlockSem γ).pureWf p (oldSz, align, origBs))
    (hpc : s0.pc = b) (hrun : s0.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = p) (hx1 : s0.readReg64 .x1 = newSize)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem) :
    let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
    let keptBs := origBs.take newSize.toNat
    let bf := if ok then FineBudget.step (.realloc align oldSz newSize.toNat) bgt else bgt
    let stepB :=
      if ok then fineStepReserve (.realloc align oldSz newSize.toNat) bgt
      else fineStepReserve (.alloc 0) bgt
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) s0
      (stackFrame s0 800 ∗ FineEnv γ maddrs tp brkStart bgt ivs0 s0 ∗
       (FineInitBlockSem γ).interp p (oldSz, align, origBs))
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R →
          sf.mem ⊨
            ((⌜MallocngCallAccounting 16 stepB s0 sf⌝ ∗
              stackFrame s0 800 ∗
              FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf ∗
              if ok then
                ∃∗ q : BitVec 64,
                  ⌜sf.readReg64 .x0 = q ∧
                   (FineInitBlockSem γ).pureWf q (newSize.toNat, max align 16, keptBs)⌝ ∗
                  (FineInitBlockSem γ).interp q (newSize.toNat, max align 16, keptBs)
              else
                ⌜sf.readReg64 .x0 = 0#64⌝ ∗
                (FineInitBlockSem γ).interp p (oldSz, align, origBs)) ∗
             ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜FineStepOomCond msvc stepB s0 sf⌝) := by
  intro ok keptBs bf stepB; have _ := hb
  obtain ⟨hpNe, hpAlign, hpOld64, hOrigLe⟩ := hpWf
  have hspMask0 : s0.sp &&& 15#64 = 0#64 := of_decide_eq_true hsp0
  have hspAlign80 : (s0.sp - 80#64) &&& 15#64 = 0#64 := by revert hspMask0; bv_robdd
  let sp1 := s0.sp - 80#64
  refine sepWP_mono_cl (post := fun sf Pf =>
      (sf.mem ⊨ Pf ∗ R →
        sf.mem ⊨
          (⌜MallocngCallAccounting 16 stepB s0 sf⌝ ∗
            stackFrame s0 800 ∗
            FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf ∗
            if ok then
              ∃∗ q : BitVec 64,
                ⌜sf.readReg64 .x0 = q ∧
                 (FineInitBlockSem γ).pureWf q (newSize.toNat, max align 16, keptBs)⌝ ∗
                (FineInitBlockSem γ).interp q (newSize.toNat, max align 16, keptBs)
            else
              ⌜sf.readReg64 .x0 = 0#64⌝ ∗
              (FineInitBlockSem γ).interp p (oldSz, align, origBs)) ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    hcl0 ?_ (fun sf Pf _ _ hclSf ⟨hq, hspF, hcsF⟩ =>
      ⟨fun hm => Satisfies.mono (sepConj_mono_left
        (Entails.trans (Entails.pure_right hclSf (Entails.refl _))
          (Entails.of_eq (sepConj_comm _ _)))) (hq hm), hspF, hcsF⟩)
  refine SepWP.weaken_pre (sepConj_mono_left (stackFrame800_entails_exists_cells s0)) ?_
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro v0; apply SepWP.exists_left; intro v1
  apply SepWP.exists_left; intro v2; apply SepWP.exists_left; intro v3
  apply SepWP.exists_left; intro v4; apply SepWP.exists_left; intro v5
  apply SepWP.exists_left; intro v6; apply SepWP.exists_left; intro v7
  apply SepWP.exists_left; intro v8; apply SepWP.exists_left; intro v9
  wp_stp64_cl m1 hm1 hcl0 hcl1
  wp_step
  wp_stp64_cl m2 hm2 hcl1 hcl2
  wp_step; wp_step
  wp_if hzP
  · exact absurd hzP hpNe
  ·
    wp_stp64_cl m3 hm3 hcl2 hcl3
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_if hhiMax
    ·
      have hNotLe : ¬ (newSize.toNat ≤ MallocngMaxAllocSize) :=
        (ult_maxAllocBv_iff newSize).mp hhiMax
      have hOkFalse : ok = false := decide_eq_false hNotLe
      have hBfEq : bf = bgt := by dsimp only [bf]; simp [hOkFalse]
      apply sepWP_bind_state; intro sEn hsEn
      have hPermEn : sEn.mem.perm = s0.mem.perm := by
        have hmEq : sEn.mem = m3 := by rw [hsEn]; rfl
        rw [hmEq, hm3, hm2, hm1]
      have hclEn : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sEn.mem := by
        have hmEq : sEn.mem = m3 := by rw [hsEn]; rfl
        rwa [hmEq]
      have hEnvEn : FineEnv γ maddrs tp brkStart bgt ivs0 s0 =
          FineEnv γ maddrs tp brkStart bgt ivs0 sEn := by
        unfold FineEnv
        have htpE : sEn.tpidrEl0 = s0.tpidrEl0 := by rw [hsEn]; rfl
        have hbrksE : sEn.brkStart = s0.brkStart := by rw [hsEn]; rfl
        have hbrkE : sEn.brk = s0.brk := by rw [hsEn]; rfl
        rw [htpE, hbrksE, hbrkE]
      have hLoPack :
          (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
           ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x20) ∗
           ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22) ∗
           ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
           ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ⊢
          ReallocSavedLo s0 sp1 ∗ (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
            memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) := by
        dsimp only [ReallocSavedLo, sp1]
        rw [show s0.sp - 80#64 + 8#64 = s0.sp - 72#64 by bv_lin, show s0.sp - 80#64 + 16#64 = s0.sp - 64#64 by bv_lin,
            show s0.sp - 80#64 + 24#64 = s0.sp - 56#64 by bv_lin, show s0.sp - 80#64 + 32#64 = s0.sp - 48#64 by bv_lin,
            show s0.sp - 80#64 + 40#64 = s0.sp - 40#64 by bv_lin, show s0.sp - 80#64 + 48#64 = s0.sp - 32#64 by bv_lin,
            show s0.sp - 80#64 + 56#64 = s0.sp - 24#64 by bv_lin, show s0.sp - 80#64 + 64#64 = s0.sp - 16#64 by bv_lin,
            show s0.sp - 80#64 + 72#64 = s0.sp - 8#64 by bv_lin]
        have hGrp :
            (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
             ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x20) ∗
             ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22) ∗
             ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
             ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) =
            ((((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
              ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x20) ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22)) ∗
             (((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
              ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9))) := by ac_rfl
        rw [hGrp]
        exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))
      rw [hEnvEn]
      refine SepWP.weaken_pre (P' := ReallocSavedLo s0 sp1 ∗
          (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
           memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
          stackFrameAt sp1 720 ∗ FineEnv γ maddrs tp brkStart bgt ivs0 sEn ∗
          (FineInitBlockSem γ).interp p (oldSz, align, origBs))
        (Entails.trans (sepConj_mono_left (sepConj_mono_left hLoPack))
          (Entails.of_eq (by
            dsimp only [FineInitBlockSem, sp1]
            generalize (FineEnv γ maddrs tp brkStart bgt ivs0 sEn) = PEnv
            generalize (FineBlock γ p oldSz (max align 16)) = PBlk
            ac_rfl))) ?_
      refine SepWP.mono (realloc_enomem_fine_ok hb γ tp brkStart bgt ivs0 s0 sEn
        (Rest := (FineInitBlockSem γ).interp p (oldSz, align, origBs))
        (by rw [hsEn]; simp) (by rw [hsEn]; simp [hrun]) hPermEn (by rw [hsEn]; rfl)
        (by rw [hsEn]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) (by rw [hsEn]; simp)
        (spAligned_of_sub80 (by rw [hsEn]; simp) hspMask0) hspMask0
        (by rw [hsEn]; simp) (by rw [hsEn]; simp) (by rw [hsEn]; simp) (by rw [hsEn]; simp)
        (by rw [hsEn]; exact ⟨by simp, by simp, by simp [calleeSavedVRegs]⟩) hclEn) ?_
      intro sf Pf _ _ ⟨hPermSf, _, hProcSf, hspSf, hcsSf, hx0Sf, hPf⟩
      refine ⟨fun hm => ?_, hspSf, hcsSf⟩
      have hAcc : MallocngCallAccounting 16 stepB s0 sf :=
        ⟨hProcSf, mallocngMappedDelta_of_perm_eq hPermSf⟩
      simp only [hOkFalse, Bool.false_eq_true, ↓reduceIte, hBfEq] at hAcc ⊢
      refine Satisfies.mono ?_ (Satisfies.mono (sepConj_mono_left hPf) hm)
      refine Entails.trans (sepConj_mono_left (Entails.pure_right hAcc
        (sepConj_mono_right (sepConj_mono_right (Entails.pure_right hx0Sf (Entails.refl _)))))) ?_
      exact Entails.of_eq (by
        dsimp only [FineInitBlockSem]
        try ac_rfl)
    ·
      have hNewMax : newSize.toNat ≤ MallocngMaxAllocSize :=
        Classical.not_not.mp (mt (ult_maxAllocBv_iff newSize).mpr hhiMax)
      have hOkTrue : ok = true := decide_eq_true hNewMax
      let newSz := newSize.toNat
      have hNewBv : newSize = BitVec.ofNat 64 newSz := (BitVec.ofNat_toNat 64 newSize).symm
      wp_stp64_cl m4 hm4 hcl3 hcl4; wp_step; wp_stp64_cl m5 hm5 hcl4 hcl5; wp_step
      wp_if hneAlign
      · exact absurd (align16_and15_eq_zero hpAlign) hneAlign
      · apply sepWP_bind_state; intro s1 hs1
        have hPerm1 : s1.mem.perm = s0.mem.perm := by
          have hmEq : s1.mem = m5 := by rw [hs1]; rfl
          rw [hmEq, hm5, hm4, hm3, hm2, hm1]
        have hcl1' : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem := by
          have hmEq : s1.mem = m5 := by rw [hs1]; rfl
          rwa [hmEq]
        have hSavedEq :
            (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
             ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x20) ∗
             ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x24) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x26)) =
            (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1) := by
          dsimp only [ReallocSavedLo, ReallocSavedHi, sp1]
          rw [show s0.sp - 80#64 + 8#64 = s0.sp - 72#64 by bv_lin, show s0.sp - 80#64 + 16#64 = s0.sp - 64#64 by bv_lin,
              show s0.sp - 80#64 + 24#64 = s0.sp - 56#64 by bv_lin, show s0.sp - 80#64 + 32#64 = s0.sp - 48#64 by bv_lin,
              show s0.sp - 80#64 + 40#64 = s0.sp - 40#64 by bv_lin, show s0.sp - 80#64 + 48#64 = s0.sp - 32#64 by bv_lin,
              show s0.sp - 80#64 + 56#64 = s0.sp - 24#64 by bv_lin, show s0.sp - 80#64 + 64#64 = s0.sp - 16#64 by bv_lin,
              show s0.sp - 80#64 + 72#64 = s0.sp - 8#64 by bv_lin]
          ac_rfl
        have hUnpackPre :
            ((ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1) ∗ stackFrameAt sp1 720) ∗
            FineEnv γ maddrs tp brkStart bgt ivs0 s0 ∗
            (FineInitBlockSem γ).interp p (oldSz, align, origBs) ⊢
            ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
            ∃∗ st : MallocngSt,
            ∃∗ alignMap0 : BitVec 64 → Option Nat,
            ∃∗ live0 : Nat,
            ∃∗ peak0 : Nat,
            ∃∗ g : GroupDesc,
            ∃∗ idx : Nat,
            ∃∗ oldEff : Nat,
            ∃∗ tailBs : List (BitVec 8),
              ⌜(MallocngFineInv 0 bgt ivs0 alignMap0 st ∧
                MallocngWF maddrs.base brkStart s0.brk live0 peak0 st ∧
                alignMap0 p = some (max align 16) ∧
                g ∈ st.groups ∧
                (∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .liveUser p oldSz oldEff) ∧
                LiveUserBlockFacts st g idx p oldSz oldEff) ∧
               tailBs.length = oldSz - origBs.length⌝ ∗
              reallocReadPre maddrs st
                (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
                 MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk
                   (synthCoarseBudget live0 peak0 st) ivs0 st ∗
                 MallocngBlockToken (fineBaseGam γ) p oldSz ∗
                 ghostMapAuth (fineAlignGam γ) alignMap0 ∗
                 ghostMapElem (fineAlignGam γ) p (max align 16) ∗
                 (p ↦ₛ (origBs ++ tailBs))) := by
          dsimp only [FineEnv, FineInitBlockSem]
          have hUnpackH := fineHeap_read_liveUser_unpack γ maddrs tp brkStart s0.brk bgt ivs0 p oldSz align
          have hTailE := memRegion_entails_exists_pointsToBytes (oldSz - origBs.length)
            (p + BitVec.ofNat 64 origBs.length) (by omega)
          refine Entails.trans (Q :=
              ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
              (FineHeapImpl γ maddrs tp brkStart s0.brk bgt ivs0 ∗
               FineBlock γ p oldSz (max align 16)) ∗
              (p ↦ₛ origBs) ∗ memRegion (p + BitVec.ofNat 64 origBs.length) (oldSz - origBs.length) ∗
              (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720))
            (Entails.of_eq (by
              generalize (ReallocSavedLo s0 sp1) = PLo
              generalize (ReallocSavedHi s0 sp1) = PHi
              generalize (FineHeapImpl γ maddrs tp brkStart s0.brk bgt ivs0) = PHp
              generalize (FineBlock γ p oldSz (max align 16)) = PBlk
              ac_rfl)) ?_
          refine sepConj_mono_right ?_
          refine Entails.trans (sepConj_mono hUnpackH (sepConj_mono_right (sepConj_mono_left hTailE))) ?_
          rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun st => ?_
          rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun alignMap0 => ?_
          rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun live0 => ?_
          rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun peak0 => ?_
          rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun g => ?_
          rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun idx => ?_
          rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun oldEff => ?_
          rw [sepExists_sepConj_left]; rw [sepExists_sepConj_right]; rw [sepExists_sepConj_right]
          refine Entails.sepExists_mono fun tailBs => ?_
          refine Entails.trans (Q :=
              ⌜MallocngFineInv 0 bgt ivs0 alignMap0 st ∧
                MallocngWF maddrs.base brkStart s0.brk live0 peak0 st ∧
                alignMap0 p = some (max align 16) ∧
                g ∈ st.groups ∧
                (∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .liveUser p oldSz oldEff) ∧
                LiveUserBlockFacts st g idx p oldSz oldEff⌝ ∗
              ⌜tailBs.length = oldSz - origBs.length⌝ ∗
              ((p ↦ₛ origBs) ∗ ((p + BitVec.ofNat 64 origBs.length) ↦ₛ tailBs)) ∗
              MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
              ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
              ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
              MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk
                (synthCoarseBudget live0 peak0 st) ivs0 st ∗
              MallocngBlockToken (fineBaseGam γ) p oldSz ∗
              ghostMapAuth (fineAlignGam γ) alignMap0 ∗
              ghostMapElem (fineAlignGam γ) p (max align 16))
            (Entails.of_eq (by
              generalize (MallocngRoTablesAt maddrs) = PRo
              generalize (MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk
                (synthCoarseBudget live0 peak0 st) ivs0 st) = PRest
              generalize (ReallocSavedLo s0 sp1) = PLo
              generalize (ReallocSavedHi s0 sp1) = PHi
              ac_rfl)) ?_
          refine Entails.pure_left fun hFact => Entails.pure_left fun hTLen => ?_
          refine Entails.pure_right ⟨hFact, hTLen⟩ ?_
          rw [← pointsToBytes_append p origBs tailBs]
          unfold reallocReadPre
          exact Entails.of_eq (by
            generalize (MallocngRoTablesAt maddrs) = PRo
            generalize (MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk
              (synthCoarseBudget live0 peak0 st) ivs0 st) = PRest
            generalize (ReallocSavedLo s0 sp1) = PLo
            generalize (ReallocSavedHi s0 sp1) = PHi
            ac_rfl)
        rw [hSavedEq]
        refine SepWP.weaken_pre hUnpackPre ?_
        apply SepWP.pure_elim; rintro ⟨htp0, hbrks0⟩
        apply SepWP.exists_left; intro st; apply SepWP.exists_left; intro alignMap0
        apply SepWP.exists_left; intro live0; apply SepWP.exists_left; intro peak0
        apply SepWP.exists_left; intro g; apply SepWP.exists_left; intro idx
        apply SepWP.exists_left; intro oldEff; apply SepWP.exists_left; intro tailBs
        apply SepWP.pure_elim
        rintro ⟨⟨hInv0, hwf0, hAlign0, hg, ⟨hIdx, hSlot⟩, hF⟩, hTailLen⟩
        let bCoarse := synthCoarseBudget live0 peak0 st
        apply SepWP.seq (realloc_stage1_read_ok hb hF
          (by rw [hs1]; simp) (by rw [hs1]; simp [hrun])
          (by rw [hs1]; simp) (by rw [hs1]))
        intro s7 P7 hpc7 hrun7
          ⟨⟨hP17, hx0_7, hx1_7, hx3_7, hx4_7, hx5_7, hx6_7, hx7_7, hx19_7, hx20_7, hx21_7, hx22_7, hx23_7, hx24_7⟩, hEnt7⟩
        refine SepWP.weaken_pre hEnt7 ?_
        obtain ⟨hmem17, hbrk17, hproc17, hsp17, _, _, _, hcs17⟩ := hP17
        have hPerm7 : s7.mem.perm = s0.mem.perm := by rw [hmem17, hPerm1]
        have hcl7 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s7.mem := by rwa [hmem17]
        have hbrk7 : s7.brk = s0.brk := hbrk17.trans (by rw [hs1]; rfl)
        have hproc7 : MallocngProcPreserved s0 s7 :=
          mallocngProcPreserved_trans (by rw [hs1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hproc17
        have hsp7 : s7.sp = s0.sp - 80#64 := hsp17.trans (by rw [hs1]; simp)
        have hal7 : s7.spAligned = true := spAligned_of_sub80 hsp7 hspMask0
        have hcs7 : ReallocUntouchedCS s0 s7 := by
          obtain ⟨h27, h28, hv⟩ := hcs17
          exact ⟨h27.trans (by rw [hs1]; simp), h28.trans (by rw [hs1]; simp),
            hv.trans (by rw [hs1]; simp [calleeSavedVRegs])⟩
        refine SepWP.weaken_pre (P' :=
            ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
            MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
            ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
            MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
            MallocngBlockToken (fineBaseGam γ) p oldSz ∗
            ghostMapAuth (fineAlignGam γ) alignMap0 ∗
            ghostMapElem (fineAlignGam γ) p (max align 16) ∗
            (p ↦ₛ (origBs ++ tailBs)) ∗ emp)
          (Entails.of_eq (by
            unfold reallocReadPre
            dsimp only [bCoarse]
            generalize (MallocngRoTablesAt maddrs) = PRo
            generalize (MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk
              (synthCoarseBudget live0 peak0 st) ivs0 st) = PRest
            generalize (ReallocSavedLo s0 sp1) = PLo
            generalize (ReallocSavedHi s0 sp1) = PHi
            simp only [sepConj_emp]; ac_rfl)) ?_
        have hFinishPost : ∀ sf Pf,
            (∃ q : BitVec 64,
              MallocngCallAccounting 16
                (fineStepReserve (.realloc align oldSz newSz) bgt) s0 sf ∧
              sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q ∧
              (Pf ⊢ stackFrame s0 800 ∗
                FinePostEnv γ maddrs tp brkStart
                  (FineBudget.stepRealloc align oldSz newSz bgt) ivs0 s0 sf ∗
                ⌜(FineInitBlockSem γ).pureWf q (newSz, max align 16, keptBs)⌝ ∗
                (FineInitBlockSem γ).interp q (newSz, max align 16, keptBs) ∗ emp)) →
            (sf.mem ⊨ Pf ∗ R →
              sf.mem ⊨
                (⌜MallocngCallAccounting 16 stepB s0 sf⌝ ∗
                  stackFrame s0 800 ∗
                  FinePostEnv γ maddrs tp brkStart bf ivs0 s0 sf ∗
                  if ok then
                    ∃∗ q : BitVec 64,
                      ⌜sf.readReg64 .x0 = q ∧
                       (FineInitBlockSem γ).pureWf q (newSize.toNat, max align 16, keptBs)⌝ ∗
                      (FineInitBlockSem γ).interp q (newSize.toNat, max align 16, keptBs)
                  else
                    ⌜sf.readReg64 .x0 = 0#64⌝ ∗
                    (FineInitBlockSem γ).interp p (oldSz, align, origBs)) ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
          rintro sf Pf ⟨q, hAcc, hspSf, hcsSf, hx0Q, hPf⟩
          refine ⟨fun hm => ?_, hspSf, hcsSf⟩
          have hBfTrue : FineBudget.stepRealloc align oldSz newSz bgt = bf := by
            dsimp only [bf, newSz, FineBudget.step]; rw [hOkTrue]; simp
          have hStepBTrue : fineStepReserve (.realloc align oldSz newSz) bgt = stepB := by
            dsimp only [stepB, newSz]; rw [hOkTrue]; simp
          simp only [hOkTrue, ↓reduceIte]
          change sf.mem ⊨ _ at hm
          refine Satisfies.mono ?_ (Satisfies.mono (sepConj_mono_left hPf) hm)
          rw [hBfTrue, ← hStepBTrue, sepConj_emp]
          have hRetEnt :
              ⌜(FineInitBlockSem γ).pureWf q (newSz, max align 16, keptBs)⌝ ∗
              (FineInitBlockSem γ).interp q (newSz, max align 16, keptBs) ⊢
              ∃∗ q' : BitVec 64,
                ⌜sf.readReg64 .x0 = q' ∧
                 (FineInitBlockSem γ).pureWf q' (newSz, max align 16, keptBs)⌝ ∗
                (FineInitBlockSem γ).interp q' (newSz, max align 16, keptBs) :=
            Entails.sepExists_right q
              (Entails.pure_left fun hWfQ => Entails.pure_right ⟨hx0Q, hWfQ⟩ (Entails.refl _))
          exact sepConj_mono_left
            (Entails.pure_right hAcc (sepConj_mono_right (sepConj_mono_right hRetEnt)))
        have hOomEq :
            (fun sf => ⌜FineStepOomCond msvc stepB s0 sf⌝) =
            (fun sf => ⌜FineStepOomCond msvc (fineStepReserve (.realloc align oldSz newSz) bgt) s0 sf⌝) := by
          funext sf; dsimp only [stepB, newSz]; simp only [hOkTrue, ↓reduceIte]
        rw [hOomEq]
        have hlr0 : s0.readReg64 Reg.lr = s0.readReg64 .x30 := rfl
        rw [hlr0]
        have _ := hx3_7; have _ := hx21_7
        wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
        wp_if hhiStage3
        ·
          apply sepWP_bind_state; intro sS3 hsS3
          refine SepWP.mono (hStage3 hb
            γ tp brkStart bgt ivs0 s0 sS3 st alignMap0 live0 peak0
            hg hIdx origBs tailBs hInv0 hwf0 hAlign0 hpNe hOrigLe hTailLen hSlot hF hNewMax
            (Frame := emp)
            (by rw [hsS3]; simp) (by rw [hsS3]; simp [hrun7])
            (by rw [hsS3]; simpa using hPerm7) (by rw [hsS3]; simpa using hbrk7)
            (by rw [hsS3]; exact hproc7) htp0 hbrks0
            (by rw [hsS3]; simpa using hsp7)
            (spAligned_of_sub80 (by rw [hsS3]; simpa using hsp7) hspMask0) hspMask0
            (by rw [hsS3]; simpa using hx0_7) (by rw [hsS3]; simpa using hx1_7)
            (by rw [hsS3]; simp) (by rw [hsS3]; simpa using hx6_7)
            (by rw [hsS3]; simpa using hx7_7) (by rw [hsS3]; simpa using hx19_7)
            (by rw [hsS3]; simpa using hx20_7) (by rw [hsS3]; simpa [newSz] using hx21_7)
            (by rw [hsS3]; simpa using hx22_7) (by rw [hsS3]; simpa using hx23_7)
            (by rw [hsS3]; simpa using hx24_7)
            (by rw [hsS3]; exact ⟨hcs7.1, hcs7.2.1, hcs7.2.2⟩)
            (by rw [hsS3]; exact hcl7))
            (fun sf Pf _ _ hPost => hFinishPost sf Pf hPost)
        ·
          have hP7Cond : ¬ ((if (BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat)).ule 131051#64 then
              BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat) else 131051#64).ult
              (BitVec.ofNat 64 newSz) = true) := hhiStage3
          have ⟨hNew131, hFit⟩ := not_stage3_hi_bounds
            (Nat.le_trans (Nat.le_add_right _ _) hF.p_add_n_le_end)
            hF.stride_bounds.2.2.2.2.2 hNewMax hP7Cond
          apply sepWP_bind_state; intro sSc0 hsSc0
          refine SepWP.weaken_pre (P' :=
              MallocngRoTablesAt maddrs ∗
              (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
               (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
               ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
               MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
               MallocngBlockToken (fineBaseGam γ) p oldSz ∗
               ghostMapAuth (fineAlignGam γ) alignMap0 ∗
               ghostMapElem (fineAlignGam γ) p (max align 16) ∗
               (p ↦ₛ (origBs ++ tailBs)) ∗ emp))
            (Entails.of_eq (by
              generalize (MallocngRoTablesAt maddrs) = PRo
              generalize (MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk bCoarse ivs0 st) = PRest
              generalize (ReallocSavedLo s0 sp1) = PLo
              generalize (ReallocSavedHi s0 sp1) = PHi
              ac_rfl)) ?_
          apply SepWP.seq (realloc_sizeToClass_ok hb (newSize := BitVec.ofNat 64 newSz) rfl hNew131
            (by rw [hsSc0]; simp) (by rw [hsSc0]; simp [hrun7])
            (by rw [hsSc0]; simpa using hx21_7))
          intro sSc PSc hpcSc hrunSc
            ⟨⟨hPSc, hw2_sc, hx3_sc, hx4_sc, hx5_sc, hx6_sc, hx19_sc, _, hx21_sc, _, hx23_sc, _⟩, hEntSc⟩
          refine SepWP.weaken_pre hEntSc ?_
          refine SepWP.weaken_pre (P' :=
              ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
              MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
              ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
              MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
              MallocngBlockToken (fineBaseGam γ) p oldSz ∗
              ghostMapAuth (fineAlignGam γ) alignMap0 ∗
              ghostMapElem (fineAlignGam γ) p (max align 16) ∗
              (p ↦ₛ (origBs ++ tailBs)) ∗ emp)
            (Entails.of_eq (by
              generalize (MallocngRoTablesAt maddrs) = PRo
              generalize (MallocngReadRest (fineBaseGam γ) maddrs tp brkStart s0.brk bCoarse ivs0 st) = PRest
              generalize (ReallocSavedLo s0 sp1) = PLo
              generalize (ReallocSavedHi s0 sp1) = PHi
              ac_rfl)) ?_
          obtain ⟨hmemSc, hbrkSc, hprocSc, hspSc, _, _, _, hcsSc⟩ := hPSc
          have hPermSc : sSc.mem.perm = s0.mem.perm := by rw [hmemSc, hsSc0]; exact hPerm7
          have hclSc : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sSc.mem := by rw [hmemSc, hsSc0]; exact hcl7
          have hbrkSc0 : sSc.brk = s0.brk := hbrkSc.trans (by rw [hsSc0]; exact hbrk7)
          have hprocSc0 : MallocngProcPreserved s0 sSc :=
            mallocngProcPreserved_trans (by rw [hsSc0]; exact hproc7) hprocSc
          have hspSc0 : sSc.sp = s0.sp - 80#64 := hspSc.trans (by rw [hsSc0]; exact hsp7)
          have hcsSc0 : ReallocUntouchedCS s0 sSc :=
            ⟨hcsSc.1.trans (by rw [hsSc0]; exact hcs7.1),
              hcsSc.2.1.trans (by rw [hsSc0]; exact hcs7.2.1),
              hcsSc.2.2.trans (by rw [hsSc0]; exact hcs7.2.2)⟩
          exact realloc_post_sc_fine_ok hStage2 hb γ tp brkStart p oldSz align oldEff newSz origBs tailBs
            bgt ivs0 s0 sSc st alignMap0 live0 peak0 hg hIdx hInv0 hwf0 hAlign0 hpNe hOrigLe hTailLen hSlot hF
            hNewMax hNew131 hFit hpcSc hrunSc hPermSc hclSc hbrkSc0 hprocSc0 htp0 hbrks0 hspSc0 hspMask0 hw2_sc
            (hx3_sc.trans (by rw [hsSc0]; simpa using hx3_7))
            (hx4_sc.trans (by rw [hsSc0]; simpa using hx4_7))
            (hx5_sc.trans (by rw [hsSc0]; simpa using hx5_7))
            (hx6_sc.trans (by rw [hsSc0]; simpa using hx6_7))
            (hx19_sc.trans (by rw [hsSc0]; simpa using hx19_7))
            hx21_sc
            (hx23_sc.trans (by rw [hsSc0]; simpa using hx23_7))
            hcsSc0 hFinishPost

end LibsignalBinary.Heap.Fine
