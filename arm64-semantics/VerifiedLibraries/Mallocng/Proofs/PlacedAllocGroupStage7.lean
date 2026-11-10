/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplHelpers2
public import VerifiedLibraries.Mallocng.Proofs.PlacedLeavesProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupHelpers3
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupStage4
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupStage6b
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocLargeHelpers

/-!
# Cut-Point Contracts and Helpers for Placed `alloc_group`

Recursive `alloc_slot` and `alloc_group` contracts (`AllocSlotAtDepthFullStmt`,
`AllocSlotFullPost`, `AllocGroupAtOffFullStmt`), spatial and accounting lemmas, count-dispatch and
root size-rounding helpers, and nested `enframe` parent-slot extraction invariants.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

arm64_proof_prelude

/-! ## Recursive Cut-Point Contracts -/

abbrev AllocSlotFullPostProp [MallocngMultiPlacement]
    (sc req inflight : Nat) (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat) (st0 : MallocngSt) (s0 sf : State) : SepProp :=
  ∃∗ st' : MallocngSt, ∃∗ idx : Nat,
    ⌜MallocngProcPreserved s0 sf ∧ st'.reservedMetas = st0.reservedMetas ∧ st'.liveMap = st0.liveMap ∧
     totalLiveEffCost st' = totalLiveEffCost st0 ∧ totalLiveCount st' = totalLiveCount st0 ∧
     st'.metaAreas.length ≤ max st0.metaAreas.length (1 + (88 + 8 * peakCount) / 101) ∧
     (∀ k : Nat, k < sc → ∀ hk1 : k < st'.ctx.active.length, ∀ hk0 : k < st0.ctx.active.length,
       st'.ctx.active[k]'hk1 = st0.ctx.active[k]'hk0) ∧
     sf.readReg32 .x0 = BitVec.ofNat 32 idx ∧ idx ≤ 31 ∧
     (∃ g ∈ st'.groups, ∃ hAct : sc < st'.ctx.active.length, ∃ hIdx : idx < g.slots.length,
       g.sc = sc ∧ req + 4 ≤ g.stride ∧ g.metaPtr = st'.ctx.active[sc]'hAct ∧ g.slots[idx]'hIdx = .claimed ∧
       (g.isMmapped = true → ∀ a : BitVec 64, InRegion (g.slotStart idx) g.stride a → st'.byteVal a = 0#8)) ∧
     MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st') s0.mem sf.mem ∧
     MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1)) (allocSlotPlacedByteBound sc peakCount) s0.mem sf.mem ∧
     (totalClaimedSlots st0 = 0 → ∀ U : Nat, peakCount ≤ U →
       Cost.GroupsGrpBound U st0.groups → Cost.GroupsGrpBound U st'.groups)⌝ ∗
    stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) ∗ MallocngRoTablesA maddrs ∗
    MallocngRuntime maddrs tp ∗ MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st'

@[expose] def AllocSlotAtDepthFullStmt (sc : Nat) : Prop :=
  ∀ [MallocngMultiPlacement] (req inflight : Nat) (_hSc : sc < 48) (_hReq : req ≤ nominalSlotCap sc)
    (_hInflight : inflight + allocSlotDepthBound sc ≤ 6) (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat) (st : MallocngSt) (_hCount : totalLiveCount st ≤ peakCount),
    subroutine_ok (mallocngBlockProg mmpl 8 msvc) (mbase 8) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart ∧ (s0.readReg32 .x0).toNat = sc ∧ (s0.readReg64 .x1).toNat = req⌝ ∗
        stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) ∗ MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightA inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗ MallocngRuntime maddrs tp
      post := fun _ s0 sf =>
        AllocSlotFullPostProp sc req inflight γ tp brkStart liveCost peakCost peakCount st s0 sf
      onOom := fun _ s0 sf =>
        ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1)) (allocSlotPlacedByteBound sc peakCount) s0 sf⌝ })

abbrev AllocSlotFullPostBody [MallocngMultiPlacement]
    (sc req inflight : Nat) (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat) (st0 : MallocngSt) (s0 sf : State) (P_f : SepProp) : Prop :=
  P_f ⊢ AllocSlotFullPostProp sc req inflight γ tp brkStart liveCost peakCost peakCount st0 s0 sf

abbrev AllocSlotFullPost [MallocngMultiPlacement]
    (sc req inflight : Nat) (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat) (st0 : MallocngSt) (s0 sf : State) (P_f : SepProp) : Prop :=
  AllocSlotFullPostBody sc req inflight γ tp brkStart liveCost peakCost peakCount st0 s0 sf P_f ∧
  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

@[expose] def AllocGroupAtOffFullStmt : Prop :=
  ∀ [MallocngMultiPlacement] (sc req inflight : Nat) (_hSc : sc < 48) (_hReq : req ≤ nominalSlotCap sc)
    (_hInflight : inflight + allocSlotDepthBound sc ≤ 6)
    (_hRec : ∀ pSc, pSc < 48 → allocSlotDepthBound pSc < allocSlotDepthBound sc → AllocSlotAtDepthFullStmt pSc)
    (γ : GhostName) (tp brkStart : BitVec 64) (liveCost peakCost peakCount : Nat) (st0 st : MallocngSt)
    (_hCount : totalLiveCount st ≤ peakCount) (_hAct0 : ∀ h : sc < st.ctx.active.length, st.ctx.active[sc]'h = 0#64)
    (_hStRel : st.reservedMetas = st0.reservedMetas ∧ st.liveMap = st0.liveMap ∧
      totalLiveEffCost st = totalLiveEffCost st0 ∧ totalLiveCount st = totalLiveCount st0 ∧
      st.metaAreas = st0.metaAreas ∧ dynamicRootRegions st = dynamicRootRegions st0 ∧
      (∀ k : Nat, k < sc → ∀ hk1 : k < st.ctx.active.length, ∀ hk0 : k < st0.ctx.active.length,
        st.ctx.active[k]'hk1 = st0.ctx.active[k]'hk0) ∧
      Cost.GroupsGrpMono st0.groups st.groups ∧ (totalClaimedSlots st0 = 0 → totalClaimedSlots st = 0))
    (s0 s : State) (_hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (_hpc : s.pc = mbase 8 + allocSlotOff_ag) (_hrun : s.status = .Running) (_hsp : s.sp = s0.sp - 96#64)
    (_hsAl : s.spAligned = true) (_htp : s0.tpidrEl0 = tp) (_hbrkS : s0.brkStart = brkStart)
    (_hpsp : PureStatePres s0 s) (_hperm : s.mem.perm = s0.mem.perm)
    (_hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx) (_hx23 : s.readReg64 .x23 = BitVec.ofNat 64 sc)
    (_hx21 : s.readReg64 .x21 = BitVec.ofNat 64 sc) (_hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req),
    SepWP (mallocngBlockProg mmpl 8 msvc) (s0.readReg64 .x30) s
      (AllocSlotSaved12 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
        (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
        (s0.readReg64 .x27) (s0.readReg64 .x28) ∗
       stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗
       MallocngRoTablesA maddrs ∗ MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
       MallocngRuntime maddrs tp)
      (AllocSlotFullPost sc req inflight γ tp brkStart liveCost peakCost peakCount st0 s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1))
                   (allocSlotPlacedByteBound sc peakCount) s0 sf⌝)

/-! ## Accounting, Entry, and Spatial Helpers -/

theorem mallocngNoOrphanMappings_trans
    {ivs0 ivs1 ivs2 : List (BitVec 64 × Nat)} {m0 m1 m2 : Memory}
    (h01 : MallocngNoOrphanMappings ivs0 ivs1 m0 m1) (h12 : MallocngNoOrphanMappings ivs1 ivs2 m1 m2) :
    MallocngNoOrphanMappings ivs0 ivs2 m0 m2 := fun a hm2 hsrc0 => by
  by_cases hm1 : (m1.perm a).mapped = false
  · exact h12 a hm2 (Or.inl hm1)
  · have hm1t : (m1.perm a).mapped = true := by cases h : (m1.perm a).mapped <;> simp_all
    exact h12 a hm2 (Or.inr (h01 a hm1t hsrc0))

theorem mallocngNoOrphanMappings_root_step
    {ivs0 ivs1 ivsf : List (BitVec 64 × Nat)} {mb : BitVec 64} {len : Nat} {m0 m1 m2 m3 m4 mf : Memory}
    (h01 : m1.perm = m0.perm) (hMeta : MallocngNoOrphanMappings ivs0 ivs1 m1 m2) (h23 : m3.perm = m2.perm)
    (hMmap : ∀ a : BitVec 64, (m4.perm a).mapped = true → (m3.perm a).mapped = true ∨ InRegion mb len a)
    (h4f : mf.perm = m4.perm) (hSub1 : ∀ iv ∈ ivs1, iv ∈ ivsf) (hMbIn : (mb, len) ∈ ivsf) :
    MallocngNoOrphanMappings ivs0 ivsf m0 mf := fun a hmf hsrc0 => by
  have hm4 : (m4.perm a).mapped = true := by rwa [← h4f]
  rcases hMmap a hm4 with hm3 | hInMb
  · have hm2 : (m2.perm a).mapped = true := by rwa [← h23]
    rw [← h01] at hsrc0; obtain ⟨iv, hiv, haIv⟩ := hMeta a hm2 hsrc0
    exact ⟨iv, hSub1 iv hiv, haIv⟩
  · exact ⟨(mb, len), hMbIn, hInMb⟩

private theorem ag_entry_strides {sc : Nat} (hsc : sc < 48) :
    let u16 := BitVec.ofNat 16 (sizeClass sc)
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 u16) <<< 4) = BitVec.ofNat 64 (slotStride sc) ∧
    (BitVec.setWidth 64 u16 &&& 65535#64) <<< 4 = BitVec.ofNat 64 (slotStride sc) := by
  intro u16; have ⟨hlo, hhi⟩ := slotStride_bounds_48 hsc; have hstr : slotStride sc = 16 * sizeClass sc := rfl
  have hm1 : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 u16) <<< 4) = BitVec.zeroExtend 64 u16 <<< 4 := by bv_bits
  have hm2 : (BitVec.setWidth 64 u16 &&& 65535#64) <<< 4 = BitVec.zeroExtend 64 u16 <<< 4 := by bv_bits
  have hsh : BitVec.zeroExtend 64 u16 <<< 4 = BitVec.ofNat 64 (slotStride sc) := by dsimp [u16]; rw [hstr]; bv_omega
  exact ⟨hm1.trans hsh, hm2.trans hsh⟩

theorem wp_ag_entry [MallocngMultiPlacement] {svc : State → State}
    (s : State) (sc : Nat) (Frame : SepProp) (_hw564 : Blk08HasWords564 svc) (_hr564 : Blk08Range564)
    (hsc : sc < 48) (hpc : s.pc = mbase 8 + allocSlotOff_ag) (hrun : s.status = .Running)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 sc) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc svc) (mbase 7) s
      ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ Frame)
      (fun sf P_f => sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ PureStatePres s sf ∧
        sf.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc) ∧ sf.readReg64 .x26 = Obj.pageOf maddrs.sizeClasses ∧
        sf.readReg64 .x27 = BitVec.ofNat 64 (slotStride sc) ∧ sf.readReg64 .lr = mbase 8 + allocSlotOff_after_meta ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x24 → r ≠ .x26 → r ≠ .x27 → r ≠ .x30 → sf.readReg64 r = s.readReg64 r) ∧
        P_f = ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ Frame))
      (fun _ => ⌜False⌝) := by
  dsimp only [allocSlotOff_ag, allocSlotOff_after_meta] at hpc ⊢
  obtain ⟨RestSc, hSplitSc⟩ := split_sizeClass_ro maddrs.sizeClasses hsc Frame
  have hScAddr : maddrs.sizeClasses + (BitVec.ofNat 64 sc <<< 1) = maddrs.sizeClasses + BitVec.ofNat 64 (2 * sc) := by
    have : BitVec.ofNat 64 sc <<< 1 = BitVec.ofNat 64 (2 * sc) := by bv_omega
    rw [this]
  have ⟨hStr27, hStr24⟩ := ag_entry_strides hsc
  conv => arg 4; rw [hSplitSc, ← hScAddr]
  wp_sym_steps
  conv => arg 4; rw [hScAddr, ← hSplitSc]
  refine SepWP.done (by simp [mbase]; bv_omega) (by simp [hrun])
    ⟨by simp [hrun], by simp, by simp [State.spAligned], psp_rfl,
     by simpa using hStr24, by simp, by simpa using hStr27, by simp, fun r hr0 hr1 hr24 hr26 hr27 hr30 => ?_, rfl⟩
  simp only [State.readReg64_setPC, State.readReg64_writeReg64_ne _ _ _ _ hr30,
    State.readReg64_writeReg64_ne _ _ _ _ hr24, State.readReg64_writeReg64_ne _ _ _ _ hr27,
    State.readReg64_writeReg64_ne _ _ _ _ hr1, State.readReg64_writeReg64_ne _ _ _ _ hr0,
    State.readReg64_writeReg64_ne _ _ _ _ hr26]

theorem words64_focus_set (ptr : BitVec 64) (ws : List (BitVec 64)) (i : Nat) (hi : i < ws.length) :
    ∃ Rest : SepProp,
      ((ptr ↦₆₄* ws) = (((ptr + BitVec.ofNat 64 (8 * i)) ↦₆₄ (ws[i]'hi)) ∗ Rest)) ∧
      (∀ w' : BitVec 64, (((ptr + BitVec.ofNat 64 (8 * i)) ↦₆₄ w') ∗ Rest) = (ptr ↦₆₄* (ws.set i w'))) := by
  refine ⟨pointsToArray 8 (· ↦₆₄ ·) ptr (ws.take i) ∗
      pointsToArray 8 (· ↦₆₄ ·) (ptr + BitVec.ofNat 64 (8 * (i + 1))) (ws.drop (i + 1)), ?_, ?_⟩
  · rw [pointsToWords64_eq_pointsToArray, pointsToArray_focus 8 (· ↦₆₄ ·) ptr ws i hi]
    have hget : ws.getD i default = ws[i]'hi := by simp [List.getD, hi]
    rw [hget]
  · intro w'; rw [pointsToWords64_eq_pointsToArray, pointsToArray_update 8 (· ↦₆₄ ·) ptr ws i w' hi]

theorem stackFrameAt_split_top (sp : BitVec 64) (k n : Nat) (hk : k ≤ n) (hn : n < 2 ^ 64) :
    stackFrameAt sp n = stackFrameAt sp k ∗ stackFrameAt (sp - BitVec.ofNat 64 k) (n - k) := by
  rw [solver_stackFrameAt_eq_memRegion sp n (by omega), solver_stackFrameAt_eq_memRegion sp k (by omega),
      solver_stackFrameAt_eq_memRegion (sp - BitVec.ofNat 64 k) (n - k) (by omega)]
  have hn_eq : n = (n - k) + k := by omega
  conv => lhs; arg 2; rw [hn_eq]
  rw [memRegion_split (sp - BitVec.ofNat 64 n) (n - k) k (by omega), sepConj_comm]
  have haddr1 : sp - BitVec.ofNat 64 n + BitVec.ofNat 64 (n - k) = sp - BitVec.ofNat 64 k := by bv_omega
  have haddr2 : sp - BitVec.ofNat 64 k - BitVec.ofNat 64 (n - k) = sp - BitVec.ofNat 64 n := by bv_omega
  rw [haddr1, haddr2]

theorem ctx_split_fields (a : BitVec 64) (c : CtxFields)
    (hAct : c.active.length = 48) (hUse : c.usageByClass.length = 48)
    (hUnm : c.unmapSeq.length = 32) (hBnc : c.bounces.length = 32) :
    ∃ CtxRest : SepProp,
      ((a ↦ₛ c.toBytes) = (((a + 12#64) ↦₃₂ c.mmapCounter) ∗ ((a + 80#64) ↦₆₄* c.active) ∗
        ((a + 464#64) ↦₆₄* c.usageByClass) ∗ ((a + 848#64) ↦ₛ c.unmapSeq) ∗
        ((a + 880#64) ↦ₛ c.bounces) ∗ ((a + 912#64) ↦₈ c.seq) ∗ CtxRest)) ∧
      (∀ (mc' : BitVec 32) (act' use' : List (BitVec 64)) (unm' bnc' : List (BitVec 8)) (seq' : BitVec 8),
        act'.length = 48 → use'.length = 48 → unm'.length = 32 → bnc'.length = 32 →
        (((a + 12#64) ↦₃₂ mc') ∗ ((a + 80#64) ↦₆₄* act') ∗ ((a + 464#64) ↦₆₄* use') ∗
         ((a + 848#64) ↦ₛ unm') ∗ ((a + 880#64) ↦ₛ bnc') ∗ ((a + 912#64) ↦₈ seq') ∗ CtxRest) =
          (a ↦ₛ ({ c with mmapCounter := mc', active := act', usageByClass := use',
                          unmapSeq := unm', bounces := bnc', seq := seq' }).toBytes)) := by
  refine ⟨(a ↦₆₄ c.secret) ∗ ((a + 8#64) ↦₃₂ c.initDone) ∗
      ((a + 16#64) ↦ₛ (unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
        unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
        unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas)) ∗
      ((a + 913#64) ↦ₛ (c.seqPad ++ unpack64 c.brk)), ?_, ?_⟩
  · rw [CtxFields.toBytes_pointsTo a c hAct hUse hUnm hBnc]; ac_rfl
  · intro mc' act' use' unm' bnc' seq' hAct' hUse' hUnm' hBnc'
    rw [CtxFields.toBytes_pointsTo a _ hAct' hUse' hUnm' hBnc']; ac_rfl

theorem saved12_rejoin_stackFrame (s0 : State) (sc : Nat)
    (r29 ret_pc r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 : BitVec 64) :
    (AllocSlotSaved12 s0.sp r29 ret_pc r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 ∗
     stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224)) ⊢
      stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) := by
  have hd : allocSlotDepthBound sc ≤ 3 := by unfold allocSlotDepthBound; repeat (first | split | omega)
  have hEq : stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) =
      (stackFrameAt s0.sp 96 ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224)) := by
    unfold stackFrame
    rw [← solver_stackFrameAt_eq_memRegion s0.sp ((allocSlotDepthBound sc + 1) * 96 + 224) (by omega),
        stackFrameAt_split_top s0.sp 96 ((allocSlotDepthBound sc + 1) * 96 + 224) (by omega) (by omega)]
    have hsub : (allocSlotDepthBound sc + 1) * 96 + 224 - 96 = allocSlotDepthBound sc * 96 + 224 := by omega
    rw [hsub]
  rw [hEq]
  exact sepConj_mono_left (saved12_entails_stackFrame96 s0.sp r29 ret_pc r19 r20 r21 r22 r23 r24 r25 r26 r27 r28)

theorem calleeSaved_of_epilogue {s0 sf : State}
    (h19 : sf.readReg64 .x19 = s0.readReg64 .x19) (h20 : sf.readReg64 .x20 = s0.readReg64 .x20) (h21 : sf.readReg64 .x21 = s0.readReg64 .x21)
    (h22 : sf.readReg64 .x22 = s0.readReg64 .x22) (h23 : sf.readReg64 .x23 = s0.readReg64 .x23) (h24 : sf.readReg64 .x24 = s0.readReg64 .x24)
    (h25 : sf.readReg64 .x25 = s0.readReg64 .x25) (h26 : sf.readReg64 .x26 = s0.readReg64 .x26) (h27 : sf.readReg64 .x27 = s0.readReg64 .x27)
    (h28 : sf.readReg64 .x28 = s0.readReg64 .x28) (h29 : sf.readReg64 .x29 = s0.readReg64 .x29) (hv : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    CalleeSavedPreserved s0 sf := ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hv⟩

theorem root_mappedDelta_combine {sc peakCount len : Nat} {m0 m1 m2 m3 mf : Memory}
    (hd1 : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) m0 m1) (hp12 : m2.perm = m1.perm)
    (hdMmap : MallocngMappedDelta 1 len m2 m3) (hp3f : mf.perm = m3.perm)
    (hlenHi : len ≤ Cost.mallocngRootGroupBoundAt peakCount) :
    MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1)) (allocSlotPlacedByteBound sc peakCount) m0 mf := by
  have hsum : allocMetaPlacedByteBound peakCount + len ≤ allocSlotPlacedByteBound sc peakCount :=
    allocSlotPlacedByteBound_root_add hlenHi
  exact MallocngMappedDelta.mono (by omega) hsum
    (MallocngMappedDelta.trans (mappedDelta_perm_right hd1 hp12) (mappedDelta_perm_right hdMmap hp3f))

theorem nested_mappedDelta_combine {sc pSc peakCount : Nat} {m0 m1 m2 m3 mf : Memory}
    (hdepth : allocSlotDepthBound pSc + 1 ≤ allocSlotDepthBound sc)
    (hd1 : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) m0 m1) (hp12 : m2.perm = m1.perm)
    (hdRec : MallocngMappedDelta (2 * (allocSlotDepthBound pSc + 1)) (allocSlotPlacedByteBound pSc peakCount) m2 m3)
    (hp3f : mf.perm = m3.perm) :
    MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1)) (allocSlotPlacedByteBound sc peakCount) m0 mf := by
  have hsum : allocMetaPlacedByteBound peakCount + allocSlotPlacedByteBound pSc peakCount ≤
      allocSlotPlacedByteBound sc peakCount :=
    allocSlotPlacedByteBound_nested_add hdepth
  exact MallocngMappedDelta.mono (by omega) hsum
    (MallocngMappedDelta.trans (mappedDelta_perm_right hd1 hp12) (mappedDelta_perm_right hdRec hp3f))

theorem root_stride_ge_req {sc req lastIdx maplen : Nat}
    (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc)
    (hMapPos : 0 < maplen) (hReqLen : lastIdx = 0 → req + 20 ≤ maplen * 4096) :
    req + 4 ≤ (if lastIdx == 0 && 0 < maplen then maplen * 4096 - 16 else slotStride sc) := by
  have ⟨hslo, _⟩ := slotStride_bounds_48 hsc
  unfold nominalSlotCap at hReq; unfold slotStride at hslo ⊢
  by_cases h0 : lastIdx = 0
  · subst h0; simp only [beq_self_eq_true, Bool.true_and, decide_eq_true hMapPos, ↓reduceIte]; have := hReqLen rfl; omega
  · simp only [beq_false_of_ne h0, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; omega

/-! ## Count Dispatch and Root Size-Rounding Helpers -/

private theorem wp_cnt_check_mem [MallocngMultiPlacement]
    (target_pc : BitVec 64) (s : State) (sc cnt : Nat) (P : SepProp)
    {post : State → SepProp → Prop} {oom : State → SepProp} (_hw768 : Blk08HasWords768Msvc)
    (hsc : sc < 48) (hlo : 2 ≤ cnt) (hhi : cnt ≤ 32) (hprod : cnt * slotStride sc ≤ 1048575)
    (h25 : sc ≤ 25 → cnt * slotStride sc + 20 ≤ 65536)
    (hsm : sc ≤ 8 → ∃ j, j < 3 ∧ cnt = (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat)
    (hpc : s.pc = mbase 8 + allocSlotOff_cnt_check) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt) (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 cnt)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc)) (hx1 : s.readReg64 .x1 = 2048#64)
    (hNested : ∀ sn : State, sn.pc = mbase 8 + allocSlotOff_nested → sn.status = .Running → sn.mem = s.mem →
      sn.sp = s.sp → sn.spAligned = s.spAligned → PureStatePres s sn → ValidNestedCnt sc cnt →
      sn.readReg64 .x0 = BitVec.ofNat 64 (cnt * slotStride sc) → sn.readReg64 .x20 = BitVec.ofNat 64 cnt →
      sn.readReg64 .x28 = BitVec.ofNat 64 cnt → (∀ r, r ≠ .x0 → r ≠ .x3 → sn.readReg64 r = s.readReg64 r) →
      SepWP (mallocngBlockProg mmpl 8 msvc) target_pc sn P post oom)
    (hRoot : ∀ sr : State, sr.pc = mbase 8 + allocSlotOff_root → sr.status = .Running → sr.mem = s.mem →
      sr.sp = s.sp → sr.spAligned = s.spAligned → PureStatePres s sr → 2048 < cnt * slotStride sc + 16 →
      cnt * slotStride sc ≤ 1048575 → (sc ≤ 25 → cnt * slotStride sc + 20 ≤ 65536) →
      sr.readReg64 .x0 = BitVec.ofNat 64 (cnt * slotStride sc) → sr.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt) →
      sr.readReg64 .x20 = BitVec.ofNat 64 cnt → sr.readReg64 .x28 = BitVec.ofNat 64 cnt →
      (∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x6 → sr.readReg64 r = s.readReg64 r) →
      SepWP (mallocngBlockProg mmpl 8 msvc) target_pc sr P post oom) :
    SepWP (mallocngBlockProg mmpl 8 msvc) target_pc s P post oom := by
  dsimp only [allocSlotOff_cnt_check] at hpc
  have ⟨_, hshi⟩ := slotStride_bounds_48 hsc; have hbd : cnt * slotStride sc ≤ 32 * 131056 := Nat.mul_le_mul hhi hshi
  have hmul_eq : BitVec.ofNat 64 (slotStride sc) * BitVec.ofNat 64 cnt = BitVec.ofNat 64 (cnt * slotStride sc) := by
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  wp_sym_steps; wp_if hls
  · have hle2048 : cnt * slotStride sc + 16 ≤ 2048 := by
      rw [BitVec.ule, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hls
      change ((cnt * slotStride sc) % (2 ^ 64) + 16) % (2 ^ 64) ≤ 2048 at hls
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hls; exact hls
    have hvnc : ValidNestedCnt sc cnt := ⟨hlo, hhi, hle2048, fun h8 => by
      obtain ⟨j, hj, rfl⟩ := hsm h8; rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> simp⟩
    exact hNested _ rfl (by simp [hrun]) rfl (by simp) (by simp [State.spAligned]) psp_rfl hvnc
      (by simp) (by simpa using hx20) (by simpa using hx28) fun r h0 h3 => by
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ h3, State.readReg64_writeReg64_ne _ _ _ _ h0]
  · have hgt2048 : 2048 < cnt * slotStride sc + 16 := by
      rw [BitVec.ule, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hls
      change ¬ (((cnt * slotStride sc) % (2 ^ 64) + 16) % (2 ^ 64) ≤ 2048) at hls
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hls; omega
    refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_root)
      (fun sr => sr.mem = s.mem ∧ sr.sp = s.sp ∧ sr.spAligned = s.spAligned ∧ PureStatePres s sr ∧
        sr.readReg64 .x0 = BitVec.ofNat 64 (cnt * slotStride sc) ∧ sr.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt) ∧
        sr.readReg64 .x20 = BitVec.ofNat 64 cnt ∧ sr.readReg64 .x28 = BitVec.ofNat 64 cnt ∧
        ∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x6 → sr.readReg64 r = s.readReg64 r) ?_
      (fun sr hpcr hrunr ⟨hm, hs, ha, hp, h0, h6, h20, h28, hr⟩ =>
        hRoot sr hpcr hrunr hm hs ha hp hgt2048 hprod h25 h0 h6 h20 h28 hr)
    dsimp only [allocSlotOff_root]; wp_sym_steps
    have hb29 : (BitVec.ofNat 32 cnt)[29] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]; change Nat.testBit (cnt % (2 ^ 32)) 29 = false
      rw [Nat.mod_eq_of_lt (by omega)]; exact Nat.testBit_lt_two_pow (by omega)
    refine SepWP.done rfl (by simp [hrun]) ⟨⟨rfl, by simp, by simp [State.spAligned], psp_rfl,
      by simp, ?_, by simpa using hx20, by simpa using hx28, fun r h0 h3 h6 => by
        simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ h6,
          State.readReg64_writeReg64_ne _ _ _ _ h3, State.readReg64_writeReg64_ne _ _ _ _ h0]⟩, by sep_entail⟩
    simp [hb29]
    have h1 : BitVec.setWidth 64 (BitVec.ofNat 32 cnt <<< 2) = BitVec.ofNat 64 (4 * cnt) := by bv_omega
    have h2 : (BitVec.ofNat 64 (4 * cnt)).ult 133#64 = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
      change (4 * cnt) % (2 ^ 64) < 133; rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [h1]; revert h2; bv_robdd

theorem wp_cnt_dispatch_mem [MallocngMultiPlacement]
    (target_pc : BitVec 64) (s : State) (sc cnt : Nat) (P : SepProp)
    {post : State → SepProp → Prop} {oom : State → SepProp} (hw768 : Blk08HasWords768Msvc)
    (hsc : sc < 48) (hlo : 1 ≤ cnt) (hhi : cnt ≤ 32) (hprod : cnt * slotStride sc ≤ 1048575)
    (h25 : sc ≤ 25 → cnt * slotStride sc + 20 ≤ 65536)
    (hsm : sc ≤ 8 → ∃ j, j < 3 ∧ cnt = (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat)
    (hc1 : cnt = 1 → 9 ≤ sc) (hpc : s.pc = mbase 8 + allocSlotOff_cnt_join) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc)) (hx4 : s.readReg64 .x4 = 4096#64)
    (hNested : ∀ (cnt' : Nat) (sn : State),
      sn.pc = mbase 8 + allocSlotOff_nested → sn.status = .Running → sn.mem = s.mem → sn.sp = s.sp →
      sn.spAligned = s.spAligned → PureStatePres s sn → ValidNestedCnt sc cnt' →
      sn.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc) → sn.readReg64 .x20 = BitVec.ofNat 64 cnt' →
      sn.readReg64 .x28 = BitVec.ofNat 64 cnt' →
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → r ≠ .x28 → sn.readReg64 r = s.readReg64 r) →
      SepWP (mallocngBlockProg mmpl 8 msvc) target_pc sn P post oom)
    (hRoot : ∀ (cnt' : Nat) (sr : State),
      sr.pc = mbase 8 + allocSlotOff_root → sr.status = .Running → sr.mem = s.mem → sr.sp = s.sp →
      sr.spAligned = s.spAligned → PureStatePres s sr → cnt' = Cost.cntBump sc cnt → 1 ≤ cnt' → cnt' ≤ 32 →
      2048 < cnt' * slotStride sc + 16 → cnt' * slotStride sc ≤ 1048575 →
      (sc ≤ 25 → cnt' * slotStride sc + 20 ≤ 65536) →
      sr.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc) → sr.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt') →
      sr.readReg64 .x20 = BitVec.ofNat 64 cnt' → sr.readReg64 .x28 = BitVec.ofNat 64 cnt' →
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x6 → r ≠ .x20 → r ≠ .x28 → sr.readReg64 r = s.readReg64 r) →
      SepWP (mallocngBlockProg mmpl 8 msvc) target_pc sr P post oom) :
    SepWP (mallocngBlockProg mmpl 8 msvc) target_pc s P post oom := by
  dsimp only [allocSlotOff_cnt_join] at hpc; have ⟨_, hshi⟩ := slotStride_bounds_48 hsc; wp_sym_steps; wp_if heq1
  · have hcnt1 : cnt = 1 := by
      have hw : BitVec.setWidth 32 (BitVec.ofNat 64 cnt) = BitVec.ofNat 32 cnt := by bv_omega
      have ht := congrArg BitVec.toNat (hw ▸ heq1); simp only [BitVec.toNat_ofNat] at ht
      change cnt % (2 ^ 32) = 1 at ht; rw [Nat.mod_eq_of_lt (by omega)] at ht; exact ht
    subst hcnt1; have hsc9 : 9 ≤ sc := hc1 rfl; wp_sym_steps; wp_if hhi1
    · have hgt2048 : 2048 < 1 * slotStride sc + 16 := by
        rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hhi1
        change 2048 < (slotStride sc % (2 ^ 64) + 16) % (2 ^ 64) at hhi1
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hhi1; omega
      refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_root)
        (fun sr => sr.mem = s.mem ∧ sr.sp = s.sp ∧ sr.spAligned = s.spAligned ∧ PureStatePres s sr ∧
          sr.readReg64 .x0 = BitVec.ofNat 64 (1 * slotStride sc) ∧ sr.readReg64 .x6 = BitVec.ofNat 64 (4 * 1) ∧
          sr.readReg64 .x20 = BitVec.ofNat 64 1 ∧ sr.readReg64 .x28 = BitVec.ofNat 64 1 ∧
          ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x6 → r ≠ .x20 → r ≠ .x28 → sr.readReg64 r = s.readReg64 r) ?_
        (fun sr hpcr hrunr ⟨hm, hs, ha, hp, h0, h6, h20, h28, hr⟩ =>
          hRoot 1 sr hpcr hrunr hm hs ha hp (by simp only [Cost.cntBump]; split <;> omega)
            (by omega) (by omega) hgt2048 hprod h25 h0 h6 h20 h28 hr)
      dsimp only [allocSlotOff_root]; wp_sym_steps
      refine SepWP.done rfl (by simp [hrun]) ⟨⟨rfl, by simp, by simp [State.spAligned], psp_rfl,
        by simp, by simp, by simpa using hx20, by simp, fun r h0 h1 _ h6 _ h28 => by
          simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ h6,
            State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h1,
            State.readReg64_writeReg64_ne _ _ _ _ h28]⟩, by sep_entail⟩
    · have hle2048 : slotStride sc + 16 ≤ 2048 := by
        rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hhi1
        change ¬ (2048 < (slotStride sc % (2 ^ 64) + 16) % (2 ^ 64)) at hhi1
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hhi1; omega
      refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_cnt_check)
        (fun sj => sj.mem = s.mem ∧ sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧
          sj.readReg64 .x20 = BitVec.ofNat 64 2 ∧ sj.readReg64 .x28 = BitVec.ofNat 64 2 ∧
          sj.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc) ∧ sj.readReg64 .x1 = 2048#64 ∧
          ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x20 → r ≠ .x28 → sj.readReg64 r = s.readReg64 r) ?_ ?_
      · dsimp only [allocSlotOff_cnt_check]; wp_sym_steps
        refine SepWP.done rfl (by simp [hrun]) ⟨⟨rfl, by simp, by simp [State.spAligned], psp_rfl,
          by simp, by simp, by simpa using hx24, by simp, fun r h0 h1 h20 h28 => by
            simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ h20,
              State.readReg64_writeReg64_ne _ _ _ _ h28, State.readReg64_writeReg64_ne _ _ _ _ h0,
              State.readReg64_writeReg64_ne _ _ _ _ h1]⟩, by sep_entail⟩
      · intro sj hjpc hjrun ⟨hmj, hspj, halj, hpspj, hj20, hj28, hj24, hj1, hjr⟩
        exact wp_cnt_check_mem target_pc sj sc 2 P hw768 hsc
          (by omega) (by omega) (by omega) (fun _ => by omega) (fun _ => by omega) hjpc hjrun hj20 hj28 hj24 hj1
          (fun sn hp hr hm hs ha hp2 hv h0 h20 h28 hrg => hNested 2 sn hp hr (hm.trans hmj)
            (hs.trans hspj) (ha.trans halj) (hpspj.trans hp2) hv h0 h20 h28
            fun r r0 r1 r3 r20 r28 => (hrg r r0 r3).trans (hjr r r0 r1 r20 r28))
          (fun sr hp hr hm hs ha hp2 hgt hpr h25' h0 h6 h20 h28 hrg => hRoot 2 sr hp hr (hm.trans hmj)
            (hs.trans hspj) (ha.trans halj) (hpspj.trans hp2) (by simp only [Cost.cntBump, true_and, hle2048, ite_true])
            (by omega) (by omega) hgt hpr h25' h0 h6 h20 h28
            fun r r0 r1 r3 r6 r20 r28 => (hrg r r0 r3 r6).trans (hjr r r0 r1 r20 r28))
  · have hge2 : 2 ≤ cnt := Classical.byContradiction fun hlt => heq1 (by obtain rfl : cnt = 1 := (by omega); rfl)
    have hb31 : (BitVec.ofNat 64 cnt)[31] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]; change Nat.testBit (cnt % (2 ^ 64)) 31 = false
      rw [Nat.mod_eq_of_lt (by omega)]; exact Nat.testBit_lt_two_pow (by omega)
    have hand32 : BitVec.ofNat 64 cnt &&& 4294967295#64 = BitVec.ofNat 64 cnt := by
      have hlt : (BitVec.ofNat 64 cnt).ult 33#64 = true := by
        rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
        change cnt % (2 ^ 64) < 33; rw [Nat.mod_eq_of_lt (by omega)]; omega
      revert hlt; bv_robdd
    exact wp_cnt_check_mem target_pc _ sc cnt P hw768 hsc hge2 hhi hprod h25 hsm rfl (by simp [hrun])
      (by simpa using hx20) (by simp [hb31]; exact hand32) (by simpa using hx24) (by simp)
      (fun sn hp hr hm hs ha hp2 hv h0 h20 h28 hrg => hNested cnt sn hp hr hm
        (hs.trans (by simp)) (ha.trans (by simp [State.spAligned])) (PureStatePres.trans psp_rfl hp2)
        hv h0 h20 h28 fun r r0 r1 r3 _ r28 => (hrg r r0 r3).trans (by
          simp only [State.readReg64_setPC, State.readReg64_setPState,
            State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r28]))
      (fun sr hp hr hm hs ha hp2 hgt hpr h25' h0 h6 h20 h28 hrg => hRoot cnt sr hp hr hm
        (hs.trans (by simp)) (ha.trans (by simp [State.spAligned])) (PureStatePres.trans psp_rfl hp2)
        (by simp only [Cost.cntBump]; split <;> omega) (by omega) hhi hgt hpr h25' h0 h6 h20 h28
        fun r r0 r1 r3 r6 _ r28 => (hrg r r0 r3 r6).trans (by
          simp only [State.readReg64_setPC, State.readReg64_setPState,
            State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r28]))

theorem sc_ge_28_of_req {sc req : Nat} (hReq : req ≤ nominalSlotCap sc) (h4077 : 4077 ≤ req) :
    28 ≤ sc := Classical.byContradiction fun hlt => by
  have hchk : ((List.range 28).all fun s => decide (nominalSlotCap s ≤ 4076)) = true := by decide +kernel
  have := of_decide_eq_true (List.all_eq_true.mp hchk sc (List.mem_range.mpr (by omega))); omega

private theorem lsl1_32_eq {cnt : Nat} (hhi : cnt ≤ 32) :
    (BitVec.ofNat 32 cnt)[30] = false ∧
    BitVec.setWidth 64 (BitVec.ofNat 32 cnt <<< 1) &&& 4294967295#64 = BitVec.ofNat 64 (2 * cnt) := by
  refine ⟨?_, ?_⟩
  · rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]; change Nat.testBit (cnt % (2 ^ 32)) 30 = false
    rw [Nat.mod_eq_of_lt (by omega)]; exact Nat.testBit_lt_two_pow (by omega)
  · have h1 : BitVec.setWidth 64 (BitVec.ofNat 32 cnt <<< 1) = BitVec.ofNat 64 (2 * cnt) := by bv_omega
    have h2 : (BitVec.ofNat 64 (2 * cnt)).ult 65#64 = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
      change (2 * cnt) % (2 ^ 64) < 65; rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [h1]; revert h2; bv_robdd

private theorem wp_root_req_round_req [MallocngMultiPlacement] {svc : State → State}
    (s : State) (sc req cnt_cur len_cur : Nat) (Frame : SepProp) (_hw768 : Blk08HasWords768 svc)
    (hsc28 : 28 ≤ sc) (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc)
    (hCur : RootMmapParamsOk sc cnt_cur len_cur) (hCurReq : cnt_cur = 1 → req + 20 ≤ len_cur)
    (hCurLen : len_cur = pageAlignUp (cnt_cur * slotStride sc + 16))
    (hpc : s.pc = mbase 8 + allocSlotOff_req_round) (hrun : s.status = .Running)
    (hx3 : s.readReg64 .x3 = 4095#64) (hx4 : s.readReg64 .x4 = 4096#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt_cur) (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req) (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 len_cur) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc svc) (mbase 8 + allocSlotOff_mmap_go) s Frame
      (fun sf P_f => ∃ cnt_f len, RootMmapParamsOk sc cnt_f len ∧ (cnt_f = 1 → req + 20 ≤ len) ∧
        (∀ x5, Cost.RootLenOk sc cnt_cur len (s.readReg64 .x2) x5) ∧
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ PureStatePres s sf ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧ sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
        (∀ r, r ≠ .x0 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → sf.readReg64 r = s.readReg64 r) ∧ P_f = Frame)
      (fun _ => ⌜False⌝) := by
  dsimp only [allocSlotOff_req_round, allocSlotOff_mmap_go] at hpc ⊢
  have ⟨hslo, hshi⟩ := slotStride_bounds_48 hsc
  have hreq_hi : req + 20 ≤ slotStride sc + 16 := by unfold nominalSlotCap at hReq; unfold slotStride at hslo ⊢; omega
  obtain ⟨hbv_req, h4096_req, hdvd_req, hle1M_req, _⟩ := align4096_bv_eq (m := req + 20) (by omega) (by omega)
  have hge_req := pageAlignUp_le (req + 20); have hlt_req := pageAlignUp_lt (req + 20)
  have h4_req : 0 < pageAlignUp (req + 20) / 4096 := Nat.div_pos h4096_req (by omega)
  have hcap_req : 12 + 1 * (if (1 : Nat) - 1 == 0 && 0 < pageAlignUp (req + 20) / 4096
      then pageAlignUp (req + 20) - 16 else slotStride sc) < pageAlignUp (req + 20) := by
    simp only [Nat.sub_self, beq_self_eq_true, Bool.true_and, decide_eq_true h4_req, ↓reduceIte]; omega
  have hr20 : BitVec.ofNat 64 req + 20#64 = BitVec.ofNat 64 (req + 20) := (BitVec.ofNat_add req 20).symm
  have hx25_eq : ∀ c_neg : BitVec 64, c_neg + 20#64 = 0#64 →
      ((c_neg - BitVec.ofNat 64 req) &&& 4095#64) + BitVec.ofNat 64 (req + 20) = BitVec.ofNat 64 (pageAlignUp (req + 20)) :=
    fun c_neg hc => by rw [neg_k_sub 20#64 _ _ hc, hr20, hbv_req]
  have hx0_nat : (BitVec.ofNat 64 (slotStride sc) + 16#64).toNat = slotStride sc + 16 := by
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  wp_sym_steps; wp_if hlo1
  · have hlt_str : pageAlignUp (req + 20) < slotStride sc + 16 := by
      rw [hx25_eq _ (by decide), BitVec.ult, decide_eq_true_eq, hx0_nat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64)] at hlo1; exact hlo1
    have hOk1 : RootMmapParamsOk sc 1 (pageAlignUp (req + 20)) :=
      ⟨by omega, by omega, h4096_req, hdvd_req, hle1M_req, fun hs => by omega, fun _ => Or.inl (by omega), hcap_req⟩
    have hLen1 : ∀ x5, Cost.RootLenOk sc cnt_cur (pageAlignUp (req + 20)) (s.readReg64 .x2) x5 :=
      fun _ => Or.inl (by have := pageAlignUp_le (slotStride sc + 16); omega)
    wp_sym_steps
    refine SepWP.done rfl (by simp [hrun]) ⟨1, pageAlignUp (req + 20), hOk1, fun _ => hge_req, hLen1,
      by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, by simp,
      by simp; rw [neg_k_sub 20#64 _ _ (by decide), hr20, hbv_req], fun r h0 h20 h25 h26 => by
        simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ h20,
          State.readReg64_writeReg64_ne _ _ _ _ h26, State.readReg64_writeReg64_ne _ _ _ _ h0,
          State.readReg64_writeReg64_ne _ _ _ _ h25], rfl⟩
  · have hge_str : slotStride sc + 16 ≤ pageAlignUp (req + 20) := by
      rw [hx25_eq _ (by decide), BitVec.ult, decide_eq_true_eq, hx0_nat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64)] at hlo1; omega
    wp_sym_steps; wp_if hlo2
    · have hlt16k : pageAlignUp (req + 20) < 16384 := by
        rw [hx25_eq _ (by decide), BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64)] at hlo2
        change pageAlignUp (req + 20) < 16384 at hlo2; exact hlo2
      have hLenCur : ∀ x5, Cost.RootLenOk sc cnt_cur len_cur (s.readReg64 .x2) x5 :=
        fun _ => Or.inr ⟨hCurLen, fun _ _ h => absurd h (by omega)⟩
      refine SepWP.done rfl (by simp [hrun]) ⟨cnt_cur, len_cur, hCur, hCurReq, hLenCur,
        by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, by simpa using hx20, by simpa using hx26,
        fun r h0 _ h25 _ => by simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h25], rfl⟩
    · have hge16k : 16384 ≤ pageAlignUp (req + 20) := by
        rw [hx25_eq _ (by decide), BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64)] at hlo2
        change ¬ pageAlignUp (req + 20) < 16384 at hlo2; omega
      have hAlignEq : pageAlignUp (req + 20) = pageAlignUp (slotStride sc + 16) := by
        obtain ⟨qr, hqr⟩ := hdvd_req; obtain ⟨qs, hqs⟩ := pageAlignUp_dvd (slotStride sc + 16)
        have := pageAlignUp_le (slotStride sc + 16); have := pageAlignUp_lt (slotStride sc + 16); omega
      have hOk2 : RootMmapParamsOk sc 1 (pageAlignUp (req + 20)) :=
        ⟨by omega, by omega, h4096_req, hdvd_req, hle1M_req, fun hs => by omega,
         fun _ => Or.inr ⟨by omega, hAlignEq⟩, hcap_req⟩
      wp_sym_steps; have hhi_cur : cnt_cur ≤ 32 := hCur.2.1
      have hw20 : BitVec.setWidth 64 (BitVec.ofNat 32 cnt_cur) = BitVec.ofNat 64 cnt_cur := by bv_omega
      have ⟨hc30, hlsl1⟩ := lsl1_32_eq hhi_cur
      by_cases hcond : (BitVec.ofNat 64 (2 * cnt_cur)).ule (s.readReg64 (Reg.gpr 2#5)) = true
      · have hLenCur : ∀ x5, Cost.RootLenOk sc cnt_cur len_cur (s.readReg64 .x2) x5 :=
          fun _ => Or.inr ⟨hCurLen, fun _ _ _ => hcond⟩
        refine SepWP.done rfl (by simp [hrun]) ⟨cnt_cur, len_cur, hCur, hCurReq, hLenCur,
          by simp [hrun], by simp, by simp [State.spAligned], psp_rfl,
          by simp [hc30, hlsl1, hcond, hw20], by simp [hc30, hlsl1, hcond, hCurLen], fun r h0 h20 h25 h26 => by
            simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ h20,
              State.readReg64_writeReg64_ne _ _ _ _ h26, State.readReg64_writeReg64_ne _ _ _ _ h0,
              State.readReg64_writeReg64_ne _ _ _ _ h25], rfl⟩
      · have hLen2 : ∀ x5, Cost.RootLenOk sc cnt_cur (pageAlignUp (req + 20)) (s.readReg64 .x2) x5 :=
          fun _ => Or.inl (Nat.le_of_eq hAlignEq)
        refine SepWP.done rfl (by simp [hrun]) ⟨1, pageAlignUp (req + 20), hOk2, fun _ => hge_req, hLen2,
          by simp [hrun], by simp, by simp [State.spAligned], psp_rfl,
          by simp [hc30, hlsl1, hcond],
          by simp [hc30, hlsl1, hcond]; rw [neg_k_sub 20#64 _ _ (by decide), hr20, hbv_req],
          fun r h0 h20 h25 h26 => by
            simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ h20,
              State.readReg64_writeReg64_ne _ _ _ _ h26, State.readReg64_writeReg64_ne _ _ _ _ h0,
              State.readReg64_writeReg64_ne _ _ _ _ h25], rfl⟩

theorem wp_root_mmap_prep_req [MallocngMultiPlacement] {svc : State → State}
    (s : State) (sc req cnt' : Nat) (Frame : SepProp) (hw768 : Blk08HasWords768 svc)
    (hsc28 : 28 ≤ sc) (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc) (hlo : 1 ≤ cnt') (hhi : cnt' ≤ 32)
    (hprod : cnt' * slotStride sc ≤ 1048575) (hpc : s.pc = mbase 8 + allocSlotOff_mmap_prep) (hrun : s.status = .Running)
    (hx4 : s.readReg64 .x4 = 4096#64) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt')
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc)) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (slotStride sc)) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc svc) (mbase 8 + allocSlotOff_mmap_go) s Frame
      (fun sf P_f => ∃ cnt_f len, RootMmapParamsOk sc cnt_f len ∧ (cnt_f = 1 → req + 20 ≤ len) ∧
        Cost.RootLenOk sc cnt' len (s.readReg64 .x2) (s.readReg64 .x5) ∧
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ PureStatePres s sf ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧ sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 → sf.readReg64 r = s.readReg64 r) ∧
        P_f = Frame) (fun _ => ⌜False⌝) := by
  have ⟨hslo, hshi⟩ := slotStride_bounds_48 hsc; have h1M := stride_prod_plus16_le hsc hprod
  obtain ⟨hbv_c, _⟩ := align4096_bv_eq (m := cnt' * slotStride sc + 16) (by omega) h1M
  have hOk_c := rootMmapParams_of_cnt (by omega) hlo hhi h1M (fun hs => by omega) (fun _ => by omega)
  have hCurReq : cnt' = 1 → req + 20 ≤ pageAlignUp (cnt' * slotStride sc + 16) := fun hc1 => by
    subst hc1; have : req + 20 ≤ 1 * slotStride sc + 16 := by unfold nominalSlotCap at hReq; unfold slotStride at hslo ⊢; omega
    have := pageAlignUp_le (1 * slotStride sc + 16); omega
  have hadd16 : BitVec.ofNat 64 (cnt' * slotStride sc) + 16#64 = BitVec.ofNat 64 (cnt' * slotStride sc + 16) := (BitVec.ofNat_add _ 16).symm
  dsimp only [allocSlotOff_mmap_prep, allocSlotOff_mmap_go] at hpc ⊢; wp_sym_steps; wp_if hne
  · refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_req_round)
      (fun sj => sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧ sj.readReg64 .x3 = 4095#64 ∧
        sj.readReg64 .x4 = 4096#64 ∧ sj.readReg64 .x20 = BitVec.ofNat 64 cnt' ∧ sj.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc) ∧
        sj.readReg64 .x25 = BitVec.ofNat 64 req ∧ sj.readReg64 .x26 = BitVec.ofNat 64 (pageAlignUp (cnt' * slotStride sc + 16)) ∧
        ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x26 → r ≠ .x27 → sj.readReg64 r = s.readReg64 r) ?_ ?_
    · dsimp only [allocSlotOff_req_round]; refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
        by simp, by simpa using hx4, by simpa using hx20, by simpa using hx24, by simpa using hx25,
        by rw [smull_stride_cnt' hhi hshi]; simp; rw [neg_k_sub 16#64 _ _ (by decide), hadd16, hbv_c],
        fun r r0 r1 r3 r26 r27 => by simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ r26,
          State.readReg64_writeReg64_ne _ _ _ _ r27, State.readReg64_writeReg64_ne _ _ _ _ r0,
          State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r3]⟩, by sep_entail⟩
    · intro sj hjpc hjrun ⟨hsp, hal, hpsp, hj3, hj4, hj20, hj24, hj25, hj26, hjr⟩
      have hr := wp_root_req_round_req sj sc req cnt' (pageAlignUp (cnt' * slotStride sc + 16)) Frame hw768 hsc28 hsc hReq hOk_c hCurReq rfl hjpc hjrun hj3 hj4 hj20 hj24 hj25 hj26
      dsimp only [allocSlotOff_mmap_go] at hr; refine SepWP.mono hr fun sf P_f _ _ ⟨cnt_f, len, hOk, hRq, hLen, h1, h2, h3, hpsp2, h6, h7, hregs, hPf⟩ =>
        ⟨cnt_f, len, hOk, hRq, (hjr .x2 (by decide) (by decide) (by decide) (by decide) (by decide)) ▸ hLen _, h1, h2.trans hsp, h3.trans hal, hpsp.trans hpsp2, h6, h7,
          fun r r0 r1 r3 r20 r25 r26 r27 => (hregs r r0 r20 r25 r26).trans (hjr r r0 r1 r3 r26 r27), hPf⟩
  · refine SepWP.done rfl (by simp [hrun]) ⟨cnt', pageAlignUp (cnt' * slotStride sc + 16), hOk_c, hCurReq,
      Or.inr ⟨rfl, fun hc hx5 _ => (root_skip_x5_ne hc hx5 hne).elim⟩,
      by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, by simpa using hx20,
      by rw [smull_stride_cnt' hhi hshi]; simp; rw [neg_k_sub 16#64 _ _ (by decide), hadd16, hbv_c],
      fun r r0 r1 r3 _ _ r26 r27 => by simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ r26,
        State.readReg64_writeReg64_ne _ _ _ _ r27, State.readReg64_writeReg64_ne _ _ _ _ r0,
        State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r3], rfl⟩

theorem wp_root_cnt_mul_req [MallocngMultiPlacement] {svc : State → State}
    (s : State) (sc req c : Nat) (Frame : SepProp) (hw768 : Blk08HasWords768 svc)
    (hsc28 : 28 ≤ sc) (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc) (hclo : 2 ≤ c) (hchi : c ≤ 5)
    (hpc : s.pc = mbase 8 + allocSlotOff_cnt_mul) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 c) (hx4 : s.readReg64 .x4 = 4096#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 c) (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc svc) (mbase 8 + allocSlotOff_mmap_go) s Frame
      (fun sf P_f => ∃ cnt_f len, RootMmapParamsOk sc cnt_f len ∧ (cnt_f = 1 → req + 20 ≤ len) ∧
        (∀ x5, Cost.RootLenOk sc c len (s.readReg64 .x2) x5) ∧
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ PureStatePres s sf ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧ sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
        (∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → sf.readReg64 r = s.readReg64 r) ∧ P_f = Frame)
      (fun _ => ⌜False⌝) := by
  have ⟨hslo, hshi⟩ := slotStride_bounds_48 hsc; have h1M : c * slotStride sc + 16 ≤ 1048576 := by have := Nat.mul_le_mul hchi hshi; omega
  obtain ⟨hbv_c, _⟩ := align4096_bv_eq (m := c * slotStride sc + 16) (by omega) h1M
  have hOk_c := rootMmapParams_of_cnt (by omega) (by omega) (by omega) h1M (fun _ => by omega) (by omega)
  have hadd16 : BitVec.ofNat 64 (c * slotStride sc) + 16#64 = BitVec.ofNat 64 (c * slotStride sc + 16) := (BitVec.ofNat_add _ 16).symm
  have hmul_eq : BitVec.ofNat 64 (slotStride sc) * BitVec.ofNat 64 c = BitVec.ofNat 64 (c * slotStride sc) := by rw [← BitVec.ofNat_mul, Nat.mul_comm]
  refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_req_round)
    (fun sj => sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧ sj.readReg64 .x3 = 4095#64 ∧
      sj.readReg64 .x4 = 4096#64 ∧ sj.readReg64 .x20 = BitVec.ofNat 64 c ∧ sj.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc) ∧
      sj.readReg64 .x25 = BitVec.ofNat 64 req ∧ sj.readReg64 .x26 = BitVec.ofNat 64 (pageAlignUp (c * slotStride sc + 16)) ∧
      ∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x26 → sj.readReg64 r = s.readReg64 r) ?_ ?_
  · dsimp only [allocSlotOff_cnt_mul, allocSlotOff_req_round] at hpc ⊢; wp_sym_steps
    refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
      by simp, by simpa using hx4, by simpa using hx20, by simpa using hx24, by simpa using hx25,
      by simp; rw [hmul_eq, neg_k_sub 16#64 _ _ (by decide), hadd16, hbv_c],
      fun r h0 h3 h26 => by simp only [State.readReg64_setPC, State.readReg64_writeReg64_ne _ _ _ _ h26,
        State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h3]⟩, by sep_entail⟩
  · intro sj hjpc hjrun ⟨hsp, hal, hpsp, hj3, hj4, hj20, hj24, hj25, hj26, hjr⟩
    refine SepWP.mono (wp_root_req_round_req sj sc req c (pageAlignUp (c * slotStride sc + 16)) Frame hw768 hsc28 hsc hReq hOk_c (by omega) rfl hjpc hjrun hj3 hj4 hj20 hj24 hj25 hj26)
      fun sf P_f _ _ ⟨cnt_f, len, hOk, hRq, hLen, h1, h2, h3, hpsp2, h6, h7, hregs, hPf⟩ =>
        ⟨cnt_f, len, hOk, hRq, (hjr .x2 (by decide) (by decide) (by decide)) ▸ hLen, h1, h2.trans hsp, h3.trans hal, hpsp.trans hpsp2, h6, h7,
          fun r r0 r3 r20 r25 r26 => (hregs r r0 r20 r25 r26).trans (hjr r r0 r3 r26), hPf⟩

/-! ## Nested Parent-Slot Extraction and enframe Byte-Map Invariants -/

theorem claimed_parent_extract {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {pg : GroupDesc} (hpg : pg ∈ st.groups) {pIdx pSc : Nat} (hpIdx : pIdx < pg.slots.length)
    (hClaimed : pg.slots[pIdx]'hpIdx = .claimed) (hpSc : pg.sc = pSc) (hpSc24 : pSc ≤ 24) :
    let slotBase := pg.slotStart pIdx - 4#64
    let bs := readBytesFromMap st.byteVal slotBase (pg.stride + 1)
    pIdx ≤ 31 ∧ pg.lastIdx ≤ 31 ∧ pg.maplen < 2 ^ 52 ∧
    (pg.maplen = 0 → 1 ≤ pg.lastIdx) ∧ (0 < pg.maplen → pg.maplen * 4096 ≤ 2 ^ 48) ∧
    16 ≤ slotStride pSc ∧ slotStride pSc % 16 = 0 ∧
    slotStride pSc ≤ pg.stride ∧ pg.stride ≤ 65524 ∧ pg.stride % 16 = 0 ∧
    (pg.slotEnd pIdx).toNat - pg.storage.toNat ≤ 65520 ∧
    (pg.slotStart pIdx).toNat = pg.mem.toNat + 16 + pIdx * pg.stride ∧
    (pg.slotEnd pIdx).toNat = pg.mem.toNat + 12 + (pIdx + 1) * pg.stride ∧
    slotBase.toNat = pg.mem.toNat + 12 + pIdx * pg.stride ∧ pg.storage.toNat = pg.mem.toNat + 16 ∧
    pg.mem.toNat + 12 + (pIdx + 1) * pg.stride ≤ 2 ^ 48 ∧
    slotBase + BitVec.ofNat 64 pg.stride = pg.slotEnd pIdx ∧
    bs.length = pg.stride + 1 ∧ bs.getD 0 0#8 = 0#8 ∧ bs.getD pg.stride 0#8 = 0#8 ∧
    ∃ PgRest : SepProp,
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal = ((slotBase ↦ₛ bs) ∗ (pg.metaPtr ↦ₛ pg.metaBytes) ∗ PgRest) ∧
      ((pg.metaPtr ↦ₛ pg.metaBytes) ∗ PgRest) =
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion slotBase (pg.stride + 1) a) st.byteVal := by
  intro slotBase bs
  have hpgWf := hwf.groups_wf pg hpg; have hpGs := group_slot_toNat hpgWf
  have hpCnt : pIdx < pg.cnt := hpgWf.2.2.1 ▸ hpIdx; have hpLast31 : pg.lastIdx ≤ 31 := hpgWf.2.1
  have hpIdx31 : pIdx ≤ 31 := by unfold GroupDesc.cnt at hpCnt; omega
  have hMemTot : pg.mem.toNat + pg.totalBytes ≤ 2 ^ 48 := hpgWf.2.2.2.2.2.2.1
  have hMapHi : 0 < pg.maplen → pg.maplen * 4096 ≤ 2 ^ 48 := fun hp => by
    have : pg.totalBytes = pg.maplen * 4096 := by simp [GroupDesc.totalBytes, hp]
    omega
  have hMap52 : pg.maplen < 2 ^ 52 := if hp : 0 < pg.maplen then by have := hMapHi hp; omega else by omega
  obtain ⟨hStrLe0, hStrHi, hEndStor⟩ := parent_slot_bounds hwf hpg (hpSc ▸ hpSc24) hpIdx
  obtain ⟨hpStNat, hpEnNat, hpSbNat⟩ := hpGs.2.2.2.2.2 pIdx hpCnt
  have hMulCnt : (pIdx + 1) * pg.stride ≤ pg.cnt * pg.stride := Nat.mul_le_mul_right _ hpCnt
  have hMemHi : pg.mem.toNat + 12 + (pIdx + 1) * pg.stride ≤ 2 ^ 48 := by have := hpGs.2.2.2.2.1; omega
  obtain ⟨hCl0, hClEnd, hClOwn⟩ := claimed_slot_ownedRw hwf hpg hpIdx hClaimed
  have hbs0 : bs.getD 0 0#8 = 0#8 := by
    have hi : 0 < bs.length := by simp [bs]
    rw [List.getD, List.getElem?_eq_getElem hi, Option.getD_some, readBytesFromMap_getElem _ _ _ 0 hi, BitVec.add_zero]
    exact hCl0
  have hSbEnd : slotBase + BitVec.ofNat 64 pg.stride = pg.slotEnd pIdx := by
    have hpEn' : (pg.slotEnd pIdx).toNat = pg.mem.toNat + 12 + (pIdx * pg.stride + pg.stride) := by
      rw [Nat.add_one_mul] at hpEnNat; exact hpEnNat
    have hMemHi' : pg.mem.toNat + 12 + (pIdx * pg.stride + pg.stride) ≤ 2 ^ 48 := by
      rw [Nat.add_one_mul] at hMemHi; exact hMemHi
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, show slotBase.toNat = pg.mem.toNat + 12 + pIdx * pg.stride from hpSbNat, hpEn',
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pg.stride < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]; omega
  have hbsEnd : bs.getD pg.stride 0#8 = 0#8 := by
    have hi : pg.stride < bs.length := by simp [bs]
    rw [List.getD, List.getElem?_eq_getElem hi, Option.getD_some, readBytesFromMap_getElem _ _ _ pg.stride hi, hSbEnd]
    exact hClEnd
  have hBm1 := ByteMap_extract_slice hwf.masterDom_wf.1 (keep := OwnedRwByte st) st.byteVal slotBase
    (n := pg.stride + 1) (by omega) (fun a ha => (hClOwn a ha).2) (fun a ha => (hClOwn a ha).1)
  obtain ⟨_, _, _, hMetaBs, hMetaOwn⟩ := meta_ownedRw_of_mem_groups hwf hpg
  have hgAll : pg.metaPtr ∈ allMetaSlots st := (hwf.free_bump_metas_wf.2.2.2.2.2 pg.metaPtr).mp
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hpg))))
  obtain ⟨gr, hgr, hgrPos, hGrLo, _, hGrStrict⟩ := group_root_containment hwf hpg
  have hDisjGr := ((mem_allMetaSlots_props hwf).1 pg.metaPtr hgAll).2.2.2.2.1 gr hgr hgrPos
  have hGrFit : gr.mem.toNat + gr.maplen * 4096 ≤ 2 ^ 48 := by
    have := (hwf.groups_wf gr hgr).2.2.2.2.2.2.1; simp [GroupDesc.totalBytes, hgrPos] at this; exact this
  have hMetaNotSl : ∀ a, InRegion pg.metaPtr 40 a → ¬ InRegion slotBase (pg.stride + 1) a := fun a haM haS => by
    have hMemHi' : pg.mem.toNat + 12 + (pIdx * pg.stride + pg.stride) ≤ 2 ^ 48 := by
      rw [Nat.add_one_mul] at hMemHi; exact hMemHi
    have haS' := (inRegion_bounds (by dsimp [slotBase]; omega)).mp haS
    exact DisjointRegions.not_both hDisjGr haM
      ((inRegion_bounds (by omega)).mpr ⟨by dsimp [slotBase] at haS'; omega,
        by dsimp [slotBase] at haS'; have := hpGs.2.2.2.1; rw [Nat.add_one_mul] at hMulCnt; omega⟩)
  have hBm2 := ByteMap_extract_slice hwf.masterDom_wf.1
    (keep := fun a => OwnedRwByte st a ∧ ¬ InRegion slotBase (pg.stride + 1) a) st.byteVal pg.metaPtr
    (n := 40) (by decide) (fun a ha => (hMetaOwn a ha).2) (fun a ha => ⟨(hMetaOwn a ha).1, hMetaNotSl a ha⟩)
  rw [hMetaBs] at hBm2
  have hStrMod16 : pg.stride % 16 = 0 := by
    unfold GroupDesc.stride; split
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega
    · unfold slotStride; omega
  refine ⟨hpIdx31, hpLast31, hMap52, fun h0 => (hpgWf.2.2.2.2.2.2.2.2.2.2.2.2.1 h0).1, hMapHi,
    (slotStride_bounds_48 (by omega)).1, by unfold slotStride; omega, hpSc ▸ hStrLe0, hStrHi, hStrMod16, hEndStor,
    hpStNat, hpEnNat, hpSbNat, hpGs.2.2.1, hMemHi, hSbEnd, readBytesFromMap_length _ _ _, hbs0, hbsEnd,
    _, by rw [hBm1, hBm2], hBm2.symm⟩

theorem enframe_geom_bounds (pg : GroupDesc) (pSc pIdx off sc cnt' : Nat)
    (hpStNat : (pg.slotStart pIdx).toNat = pg.mem.toNat + 16 + pIdx * pg.stride)
    (hpEnNat : (pg.slotEnd pIdx).toNat = pg.mem.toNat + 12 + (pIdx + 1) * pg.stride)
    (hpSbNat : (pg.slotStart pIdx - 4#64).toNat = pg.mem.toNat + 12 + pIdx * pg.stride)
    (hpStorNat : pg.storage.toNat = pg.mem.toNat + 16)
    (hMemHi : pg.mem.toNat + 12 + (pIdx + 1) * pg.stride ≤ 2 ^ 48)
    (hpStrLo : 16 ≤ slotStride pSc) (hStrLe : slotStride pSc ≤ pg.stride) (hStrHi : pg.stride ≤ 65524)
    (hEndStor : (pg.slotEnd pIdx).toNat - pg.storage.toNat ≤ 65520)
    (hoffLe : off ≤ (pg.stride - slotStride pSc) / 16)
    (hNeedLe : cnt' * slotStride sc + 12 ≤ nominalSlotCap pSc) :
    let slotBase := pg.slotStart pIdx - 4#64; let mb := pg.slotStart pIdx + BitVec.ofNat 64 (16 * off)
    pg.storage.toNat + pIdx * pg.stride + 16 * off < 2 ^ 64 ∧
    16 * off + 16 + cnt' * slotStride sc ≤ pg.stride ∧
    slotBase + BitVec.ofNat 64 (16 * off + 16) = mb + 12#64 ∧ slotBase + BitVec.ofNat 64 (16 * off + 4) = mb ∧
    (pg.slotStart pIdx).toNat ≤ mb.toNat ∧ (mb.toNat - (pg.slotStart pIdx).toNat) % 16 = 0 ∧
    mb.toNat + (slotStride pSc - 4) ≤ (pg.slotEnd pIdx).toNat ∧
    (mb.toNat - pg.storage.toNat) / 16 ≤ 65535 ∧ 12 + cnt' * slotStride sc ≤ slotStride pSc - 4 := by
  dsimp only; rw [Nat.add_one_mul] at hpEnNat hMemHi
  rw [show nominalSlotCap pSc = slotStride pSc - 4 from rfl] at hNeedLe
  have hoff16 : 16 * off ≤ pg.stride - slotStride pSc := by omega
  have hmbNat : (pg.slotStart pIdx + BitVec.ofNat 64 (16 * off)).toNat = pg.mem.toNat + 16 + pIdx * pg.stride + 16 * off := by
    rw [BitVec.toNat_add, hpStNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 16 * off < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega, by omega, ?_, ?_, by omega, by omega, by omega, by omega, by omega⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hpSbNat, BitVec.toNat_add, hmbNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 16 * off + 16 < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    change pg.mem.toNat + 12 + pIdx * pg.stride + (16 * off + 16) = (pg.mem.toNat + 16 + pIdx * pg.stride + 16 * off + 12) % (2 ^ 64)
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hpSbNat, hmbNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 16 * off + 4 < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]; omega

theorem groups_set_claimed_roots : ∀ (gs : List GroupDesc), (gs.map (·.metaPtr)).Nodup →
    ∀ {pg : GroupDesc}, pg ∈ gs → ∀ (pIdx : Nat) (m : BitVec 64),
    let f := fun g : GroupDesc => if g.metaPtr == pg.metaPtr then { pg with slots := pg.slots.set pIdx (.liveNested m) } else g
    ((gs.map f).filter fun g => decide (0 < g.maplen)).map (fun g => (g.mem, g.maplen * 4096)) =
      (gs.filter fun g => decide (0 < g.maplen)).map (fun g => (g.mem, g.maplen * 4096))
  | [], _, _, hpg, _, _ => by cases hpg
  | g :: rest, hnd, pg, hpg, pIdx, m => by
    obtain ⟨hNotIn, hndR⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hpg with hEqPg | hpgR
    · subst hEqPg
      have hId : ∀ ls : List GroupDesc, pg.metaPtr ∉ ls.map (·.metaPtr) →
          ls.map (fun x => if x.metaPtr == pg.metaPtr then { pg with slots := pg.slots.set pIdx (.liveNested m) } else x) = ls := by
        intro ls; induction ls with
        | nil => intro _; rfl
        | cons x xs ih =>
          intro hn
          have hne : (x.metaPtr == pg.metaPtr) = false := beq_false_of_ne fun h => hn (by rw [← h]; exact List.Mem.head _)
          simp only [List.map_cons, hne, Bool.false_eq_true, ↓reduceIte, ih fun h => hn (List.Mem.tail _ h)]
      simp only [List.map_cons, beq_self_eq_true, ↓reduceIte, hId rest hNotIn]; by_cases hp : 0 < pg.maplen <;> simp [hp]
    · have hNe : (g.metaPtr == pg.metaPtr) = false :=
        beq_false_of_ne fun h => by dsimp only at hNotIn; rw [h] at hNotIn; exact hNotIn (List.mem_map_of_mem hpgR)
      have ih := groups_set_claimed_roots rest hndR hpgR pIdx m
      simp only [List.map_cons, hNe, Bool.false_eq_true, ↓reduceIte]; by_cases hg : 0 < g.maplen
      · rw [List.filter_cons_of_pos (by simp [hg]), List.filter_cons_of_pos (by simp [hg]), List.map_cons, List.map_cons, ih]
      · rw [List.filter_cons_of_neg (by simp [hg]), List.filter_cons_of_neg (by simp [hg])]; exact ih

end VerifiedLibraries.Mallocng.Proofs
