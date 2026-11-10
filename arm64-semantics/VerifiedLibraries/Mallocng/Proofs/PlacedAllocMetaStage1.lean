/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.InternalPlaced
public import VerifiedLibraries.Mallocng.Proofs.PlacedLeavesProof
public import VerifiedLibraries.Mallocng.Proofs.MallocLargeProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaHelpers2
import VerifiedLibraries.Mallocng.Proofs.MemcpySym

/-!
# Stage 1 Symbolic Execution Helpers for Placed `__malloc_alloc_meta`

Cross-block `SepWP` / `withCL` combinators, 224-byte stack frame decompositions, and Stage 1
symbolic execution lemmas (`sepWP_epilogue_278`, `sepWP_epilogue_26c`, `sepWP_activate_2a0`,
`sepWP_mprotect_224`) for `placed_allocMeta_ok` on `mallocngBlockProg mmpl 7 msvc`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

theorem MallocngProcPreserved.trans {s0 s1 s2 : State}
    (h01 : MallocngProcPreserved s0 s1) (h12 : MallocngProcPreserved s1 s2) :
    MallocngProcPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

theorem sepWP_lift_noSyscalls_cl [MallocngMultiPlacement] {idx : Nat}
    {target_pc : BitVec 64} {s0 : State} {P : SepProp}
    (post : State → SepProp → Prop) {oom : State → SepProp}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem)
    (h : SepWP ((mallocngBlockProg mmpl idx msvc).withSvc mallocngFaultSvc) target_pc s0 P post (fun _ => ⌜False⌝)) :
    SepWP (mallocngBlockProg mmpl idx msvc) target_pc s0 P
      (fun sf P_f =>
        sf.mem.perm = s0.mem.perm ∧
        MallocngMappedDelta 0 0 s0.mem sf.mem ∧
        VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem ∧
        post sf P_f)
      oom := by
  refine sepWP_mono_cl hcl (SepWP.lift_noSyscalls rfl rfl h) ?_
  intro sf P_f _ _ hcl_f ⟨hpost, hperm⟩
  exact ⟨hperm, ⟨[], Nat.zero_le 0, Nat.zero_le 0, fun a ha => Or.inl (hperm ▸ ha)⟩, hcl_f, hpost⟩

theorem call_withCL_frame_auto {α : Type} {prog : Program} {mpl : MultiPlacement}
    {entry target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withCL mpl spec))
    {x : α} {s : State} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {ret_pc : BitVec 64}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mpl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      VerifiedLibraries.mallocngLib.CodeLoaded mpl sf.mem →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post oom)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)) := by sep_frame)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.call_subroutine_frame (F := F) hcall hpc hrun hsp_align hlr
    (fun R hm => ?_) h_no_panic h_no_exit (fun sf hpc' hrun' hsp' hcs' => ?_) h_oom
  · have hm' := hpre R hm
    dsimp only [withCL]
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_right (Entails.pure_right hcl (Entails.refl _))) hm'
  · dsimp only [withCL]
    rw [sepConj_assoc, sepConj_comm ⌜_⌝, ← sepConj_assoc, sepConj_comm _ ⌜_⌝]
    exact SepWP.pure_elim (hnext sf hpc' hrun' hsp' hcs')

theorem and_4095_eq_zero_of_dvd {x : BitVec 64} (h : 4096 ∣ x.toNat) :
    x &&& 4095#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  change x.toNat &&& (2 ^ 12 - 1) = 0
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_zero_of_dvd h

theorem placed_memcpy8_mapped_ok [MallocngMultiPlacement] {P : Program}
    (dst src dstVal srcVal : BitVec 64)
    (_hDstFit : dst.toNat + 8 ≤ 2 ^ 64) (_hSrcFit : src.toNat + 8 ≤ 2 ^ 64)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 20) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ s0.readReg64 .x2 = 8#64⌝ ∗
        (dst ↦₆₄ dstVal) ∗ (src ↦₆₄ srcVal)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.readReg64 .x0 = dst ∧
         MallocngMappedDelta 0 0 s0.mem sf.mem⌝ ∗
        (dst ↦₆₄ srcVal) ∗ (src ↦₆₄ srcVal)
    }) := by
  refine subroutine_ok_block_to_block_plain (j := 20) (by decide) ?_ hext hsvc
  have hwords : ((mallocngBlockProg mmpl 20 msvc).withSvc mallocngFaultSvc).hasWords (mbase 20) memcpySymWords :=
    Program.hasWords_withSvc (hasWords_blk_relocFree (i := 20) (by decide) (ws := memcpySymWords) (by decide +kernel))
  wp_init x s0
  refine SepWP.mono
    (SepWP.lift_noSyscalls rfl rfl
      (post := sepPost (fun sf =>
        MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.readReg64 .x0 = dst ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((dst ↦₆₄ srcVal) ∗ (src ↦₆₄ srcVal))) ?_) ?_
  · wp_sym_steps
    have hSubAdd : dst + 8#64 - 8#64 = dst := by bv_arith
    have hSrcSubAdd : src + 8#64 - 8#64 = src := by bv_arith
    simp only [hSubAdd, hSrcSubAdd] at *
    wp_done
  · intro sf P_f _ _ ⟨⟨⟨hProc, hBrk, hx0, hsp, hcs⟩, hent⟩, hperm⟩
    refine ⟨fun hm => ?_, hsp, hcs⟩
    have hm' := Satisfies.mono (sepConj_mono_left hent) hm
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm' ⊢
    exact ⟨⟨hProc, hBrk, hx0, ⟨[], Nat.zero_le 0, Nat.zero_le 0, fun a ha => Or.inl (hperm ▸ ha)⟩⟩, hm'⟩

theorem freeMeta_toBytes_eq_cells (fm : FreeMetaDesc) :
    (fm.ptr ↦ₛ fm.toBytes) = ((fm.ptr ↦₆₄ fm.prev) ∗ ((fm.ptr + 8#64) ↦₆₄ fm.next) ∗ ((fm.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) := by
  simp only [FreeMetaDesc.toBytes, List.append_assoc, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes, addr_norm]

theorem zero40_eq_cells (m : BitVec 64) :
    (m ↦ₛ List.replicate 40 0#8) = ((m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦ₛ List.replicate 24 0#8)) := by
  rw [show List.replicate 40 0#8 = unpack64 0#64 ++ (unpack64 0#64 ++ List.replicate 24 0#8) by decide]
  simp only [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes, addr_norm]

theorem metaHdrBytes_eq_cells (b sec next : BitVec 64) :
    (b ↦ₛ metaHdrBytes sec next) = ((b ↦₆₄ sec) ∗ ((b + 8#64) ↦₆₄ next) ∗ ((b + 16#64) ↦₃₂ 101#32) ∗ ((b + 20#64) ↦₃₂ 0#32)) := by
  simp only [metaHdrBytes, List.append_assoc, pointsToBytes_append, unpack64_length, unpack32_length, ← pointsTo64_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes, addr_norm]

theorem zeroPage_eq_metaArea_cells (ap : BitVec 64) :
    (ap ↦ₛ List.replicate 4096 0#8) = ((ap ↦₆₄ 0#64) ∗ ((ap + 8#64) ↦₆₄ 0#64) ∗ ((ap + 16#64) ↦₃₂ 0#32) ∗ ((ap + 20#64) ↦₃₂ 0#32) ∗ ((ap + 24#64) ↦ₛ List.replicate 40 0#8) ∗ ((ap + 64#64) ↦ₛ List.replicate 4032 0#8)) := by
  have h8 : List.replicate 8 0#8 = unpack64 0#64 := by decide
  have h4 : List.replicate 4 0#8 = unpack32 0#32 := by decide
  have hSplit : List.replicate 4096 0#8 = unpack64 0#64 ++ (unpack64 0#64 ++ (unpack32 0#32 ++ (unpack32 0#32 ++ (List.replicate 40 0#8 ++ List.replicate 4032 0#8)))) := by
    rw [show (4096 : Nat) = 8 + (8 + (4 + (4 + (40 + 4032)))) by decide]
    simp only [List.replicate_add, h8, h4]
  rw [hSplit]; simp only [pointsToBytes_append, unpack64_length, unpack32_length, List.length_replicate, ← pointsTo64_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes, addr_norm]

abbrev Cs21Preserved (s0 s : State) : Prop :=
  s.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) ∧ s.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧
  s.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧ s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧ s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧ s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

abbrev Cs25Preserved (s0 s : State) : Prop :=
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧ s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧ s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

abbrev Cs23Preserved (s0 s : State) : Prop :=
  s.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧ s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧ Cs25Preserved s0 s

abbrev AllocMetaPlacedPost [MallocngMultiPlacement] (inflight : Nat) (γ : GhostName)
    (tp brkStart : BitVec 64) (liveCost peakCost peakCount : Nat) (st : MallocngSt)
    (s0 sf : State) (P_f : SepProp) : Prop :=
  (P_f ⊢ ∃∗ st' : MallocngSt, ∃∗ m : BitVec 64,
    ⌜MallocngProcPreserved s0 sf ∧ sf.readReg64 .x0 = m ∧ m ≠ 0#64 ∧
     4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧
     m ∉ st.reservedMetas ∧ st'.reservedMetas = m :: st.reservedMetas ∧
     st'.groups = st.groups ∧ st'.activeLists = st.activeLists ∧
     st'.liveMap = st.liveMap ∧ totalLiveCount st' = totalLiveCount st ∧
     st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
     st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧
     st'.ctx.seq = st.ctx.seq ∧
     (∀ g ∈ st.groups, ∀ a : BitVec 64,
       (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) ∧
     MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem sf.mem⌝ ∗
    stackFrame s0 224 ∗ MallocngRuntime maddrs tp ∗ (m ↦ₛ List.replicate 40 0#8) ∗
    MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st') ∧
  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

def StaticFrameA (γ : GhostName) (A : MallocngAddrs)
    (liveMap : MallocngLiveMap) : SepProp :=
  MallocngLiveAuth γ liveMap ∗ (A.lock ↦₃₂ 0#32) ∗ (A.replaced ↦₃₂ 0#32) ∗ (A.aaReplaced ↦₃₂ 0#32) ∗ ((A.libc + 3#64) ↦₈ 0#8)

abbrev SavedRegs0 (s0 : State) : SepProp :=
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x20)

abbrev SavedRegs21 (s0 : State) : SepProp :=
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x24)

abbrev StackFrameOpen (s0 : State) : SepProp :=
  memRegion (s0.sp - 224#64) 80 ∗ (stackAt (s0.sp - 80#64) 64 ∗ (SavedRegs0 s0 ∗ cells (s0.sp - 48#64) 6))

abbrev StackFrameSlow (s0 : State) : SepProp :=
  memRegion (s0.sp - 224#64) 80 ∗ (stackAt (s0.sp - 80#64) 64 ∗ (SavedRegs0 s0 ∗ (SavedRegs21 s0 ∗ cells (s0.sp - 16#64) 2)))

theorem stack224_fold (s0 : State) :
    StackFrameOpen s0 ⊢ stackFrame s0 224 := by
  have hCells : (SavedRegs0 s0 ∗ cells (s0.sp - 48#64) 6) ⊢ cells (s0.sp - 80#64) 10 := by
    rw [SavedRegs0, sepConj_assoc, sepConj_assoc, sepConj_assoc]
    exact cells_sub_succ_entails 80 10 (cells_sub_succ_entails 72 9 (cells_sub_succ_entails 64 8 (cells_sub_succ_entails 56 7 (Entails.refl _))))
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right hCells)) ?_
  have hSplit : stackAt s0.sp 224 = (memRegion (s0.sp - 224#64) 80 ∗ (stackAt (s0.sp - 80#64) 64 ∗ cells (s0.sp - 80#64) 10)) :=
    wrapperFrame_split s0.sp (wrapperStack := 224) (hookStack := 64) 10 (by decide)
  rw [← hSplit, stackAt_eq_stackFrameAt s0.sp 224, stackFrameAt_eq_memRegion s0.sp 224]
  dsimp only [stackFrame]
  exact Entails.refl _

theorem stackSlow_to_open (s0 : State) : StackFrameSlow s0 ⊢ StackFrameOpen s0 := by
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  rw [SavedRegs21, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  exact cells_sub_succ_entails 48 6 (cells_sub_succ_entails 40 5 (cells_sub_succ_entails 32 4 (cells_sub_succ_entails 24 3 (Entails.refl _))))

theorem allocMetaPlacedPost_congr [MallocngMultiPlacement] {inflight : Nat} {γ : GhostName}
    {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat} {st1 st2 : MallocngSt} {s0 sf : State} {P_f : SepProp}
    (hEq : st1.reservedMetas = st2.reservedMetas ∧ st1.groups = st2.groups ∧ st1.activeLists = st2.activeLists ∧
      st1.liveMap = st2.liveMap ∧ st1.ctx.active = st2.ctx.active ∧ st1.ctx.usageByClass = st2.ctx.usageByClass ∧
      st1.ctx.unmapSeq = st2.ctx.unmapSeq ∧ st1.ctx.bounces = st2.ctx.bounces ∧ st1.ctx.seq = st2.ctx.seq ∧ st1.byteVal = st2.byteVal)
    (hPost : AllocMetaPlacedPost inflight γ tp brkStart liveCost peakCost peakCount st1 s0 sf P_f) :
    AllocMetaPlacedPost inflight γ tp brkStart liveCost peakCost peakCount st2 s0 sf P_f := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := hEq
  have rCnt : totalLiveCount st1 = totalLiveCount st2 := by unfold totalLiveCount; rw [r2]
  unfold AllocMetaPlacedPost at hPost ⊢; rwa [r1, r2, r3, r4, rCnt, r5, r6, r7, r8, r9, r10] at hPost

def blk07Words : List (BitVec 32) := [
  0xa9bb7bfd#32, 0x910003fd#32, 0xa90153f3#32, 0x90000014#32, 0x91000280#32, 0xb9400800#32, 0x34000220#32, 0x91000281#32, 0xf9400833#32, 0xb40011d3#32,
  0xf9400660#32, 0xeb00027f#32, 0x54000560#32, 0xf9400262#32, 0xf9000440#32, 0xf9400262#32, 0xf9000002#32, 0xf9400820#32, 0xeb00027f#32, 0x54001161#32,
  0xf9400660#32, 0xf9000820#32, 0x14000088#32, 0xd289cda1#32, 0xa9025bf5#32, 0x910123f5#32, 0xf2a838c1#32, 0x90000000#32, 0x91000000#32, 0xd2800013#32,
  0x9b017ea1#32, 0xaa0003f6#32, 0xf90027e1#32, 0xf9400400#32, 0x14000009#32, 0x8b130001#32, 0xd2800102#32, 0xaa1503e0#32, 0xf9400421#32, 0x8b020021#32,
  0x94000000#32, 0xf94006c0#32, 0x91004273#32, 0xf8736801#32, 0xf100643f#32, 0xb4000061#32, 0x54ffff81#32, 0x17fffff4#32, 0x91000280#32, 0x52800021#32,
  0xf94027e2#32, 0xf9000282#32, 0xb9000801#32, 0xa9425bf5#32, 0x17ffffd1#32, 0xf900083f#32, 0x14000066#32, 0x90000000#32, 0xa9025bf5#32, 0xd2820003#32,
  0xa90363f7#32, 0xf9400000#32, 0xf9401422#32, 0xeb03001f#32, 0x9a832018#32, 0xb5000c42#32, 0xf941cc35#32, 0xb10006bf#32, 0x540001a0#32, 0xb40004b5#32,
  0x8b1802b6#32, 0xd2801ac8#32, 0xaa1603e0#32, 0xd4000001#32, 0xeb0002df#32, 0x54000680#32, 0x91000280#32, 0x92800002#32, 0xf9401401#32, 0xf901cc02#32,
  0xb5000681#32, 0x91000297#32, 0xd2800056#32, 0xd2800005#32, 0x12800004#32, 0x52800443#32, 0x52800002#32, 0xf9401ae1#32, 0xd2800000#32, 0x9ac122d6#32,
  0x9b167f01#32, 0x94000000#32, 0xb100041f#32, 0x540006a0#32, 0xd10006c1#32, 0xd34cff16#32, 0xf9401ae2#32, 0x8b180015#32, 0xd1000700#32, 0x9b167c36#32,
  0xea0002bf#32, 0x91000441#32, 0x1a9f17e0#32, 0xa90286f6#32, 0xf90026f5#32, 0x1400003e#32, 0xd2801ac8#32, 0xd2800000#32, 0xd4000001#32, 0xcb0003e2#32,
  0xd1000716#32, 0x8a160056#32, 0x8b0002d6#32, 0xf901cc36#32, 0x8b1806d6#32, 0xaa1603e0#32, 0xd4000001#32, 0xeb0002df#32, 0x54fffac1#32, 0xf941cc20#32,
  0xcb1802d5#32, 0xaa1803e1#32, 0xd2800005#32, 0x12800004#32, 0x52800643#32, 0x52800002#32, 0x94000000#32, 0x91000281#32, 0xd34cff00#32, 0xf9001420#32,
  0xf901cc36#32, 0x14000025#32, 0xf9402415#32, 0xd1000700#32, 0xea0002bf#32, 0x1a9f17e0#32, 0x1400001f#32, 0xaa1803e1#32, 0xaa1503e0#32, 0x52800062#32,
  0x94000000#32, 0x34000360#32, 0x94000000#32, 0xb9400000#32, 0x7100981f#32, 0x540002e0#32, 0xa9425bf5#32, 0xa94363f7#32, 0x1400000b#32, 0xf9001c15#32,
  0x1400001b#32, 0xf9401020#32, 0xb4fff420#32, 0xf9400c33#32, 0xd1000400#32, 0x91000294#32, 0x9100a261#32, 0xa9018281#32, 0xa9007e7f#32, 0xaa1303e0#32,
  0xa94153f3#32, 0xa8c57bfd#32, 0xd65f03c0#32, 0xf9402435#32, 0xd1000700#32, 0xea0002bf#32, 0x1a9f17e0#32, 0x35fffc40#32, 0x91000280#32, 0x914006a2#32,
  0xf9401401#32, 0xf9002402#32, 0xf9402002#32, 0xd1000421#32, 0xf9001401#32, 0xb4fffcc2#32, 0xf9000455#32, 0x91000281#32, 0x52800ca3#32, 0xf9400282#32,
  0xd2800c80#32, 0xf9002035#32, 0xf90002a2#32, 0xf9402022#32, 0xb9001043#32, 0xf9402033#32, 0xa9425bf5#32, 0x91006273#32, 0xa94363f7#32, 0x17ffffde#32]

abbrev blk07Relocs : List Obj.RelocEntry := VerifiedLibraries.mallocng_blk07_malloc_alloc_meta.relocs

@[simp, arm64_norm, wp_norm] theorem addSignedAddr_48 (x : BitVec 64) :
    Obj.addSignedAddr x 48 = x + 48#64 := rfl

theorem hasWords_blk_seg [MallocngMultiPlacement] {i : Nat} (hi : i < 24) (fo : Nat)
    {ws : List (BitVec 32)} {R : List Obj.RelocEntry}
    (hchk : VerifiedLibraries.mallocngLib.blocks[i].checkSegment fo ws R = true) :
    (mallocngBlockProg mmpl i msvc).hasWords (mbase i + BitVec.ofNat 64 fo)
        (Obj.patchRelocs R ws (mbase i + BitVec.ofNat 64 fo) (VerifiedLibraries.mallocngLib.resolve mmpl)) ∧
      ∀ r ∈ R, Obj.CodeRelocInRange r.kind
        (mbase i + BitVec.ofNat 64 fo + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (VerifiedLibraries.mallocngLib.resolve mmpl r.sym) r.addend) :=
  Obj.MultiPlacedLib.hasWords_of_checkSegment
    (lib := VerifiedLibraries.mallocngLib) (mpl := mmpl) (i := i)
    (by simpa using hi) (fo := fo) (X := fun _ => none) (svc := msvc)
    MallocngMultiPlacement.placeable hchk

theorem hasWords_blk_seg0 [MallocngMultiPlacement] {i : Nat} (hi : i < 24)
    {ws : List (BitVec 32)} {R : List Obj.RelocEntry}
    (hchk : VerifiedLibraries.mallocngLib.blocks[i].checkSegment 0 ws R = true) :
    (mallocngBlockProg mmpl i msvc).hasWords (mbase i)
        (Obj.patchRelocs R ws (mbase i) (VerifiedLibraries.mallocngLib.resolve mmpl)) ∧
      ∀ r ∈ R, Obj.CodeRelocInRange r.kind
        (mbase i + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (VerifiedLibraries.mallocngLib.resolve mmpl r.sym) r.addend) := by
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hasWords_blk_seg hi 0 hchk

def blk07Words0 : List (BitVec 32) := blk07Words.take 27
def blk07Relocs0 : List Obj.RelocEntry :=
  VerifiedLibraries.mallocng_blk07_malloc_alloc_meta.segRelocs 0 (4 * 27)

def blk07Words116 : List (BitVec 32) := blk07Words.drop 29
def blk07Relocs116 : List Obj.RelocEntry :=
  VerifiedLibraries.mallocng_blk07_malloc_alloc_meta.segRelocs 116 (4 * 161)

macro "Blk07HasWords0" svc:term : term =>
  `(((mallocngBlockProg mmpl 7 msvc).withSvc $svc).hasWords (mbase 7)
      (Obj.patchRelocs blk07Relocs0 blk07Words0 (mbase 7) (VerifiedLibraries.mallocngLib.resolve mmpl)))

macro "Blk07Range0" : term =>
  `(∀ r ∈ blk07Relocs0, Obj.CodeRelocInRange r.kind
      (mbase 7 + BitVec.ofNat 64 r.off)
      (Obj.addSignedAddr (VerifiedLibraries.mallocngLib.resolve mmpl r.sym) r.addend))

macro "Blk07HasWords116" svc:term : term =>
  `(((mallocngBlockProg mmpl 7 msvc).withSvc $svc).hasWords (mbase 7 + 116#64)
      (Obj.patchRelocs blk07Relocs116 blk07Words116 (mbase 7 + 116#64) (VerifiedLibraries.mallocngLib.resolve mmpl)))

macro "Blk07Range116" : term =>
  `(∀ r ∈ blk07Relocs116, Obj.CodeRelocInRange r.kind
      (mbase 7 + 116#64 + BitVec.ofNat 64 r.off)
      (Obj.addSignedAddr (VerifiedLibraries.mallocngLib.resolve mmpl r.sym) r.addend))

theorem sepWP_epilogue_278 [MallocngMultiPlacement]
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {st st' : MallocngSt} {m w0 w1 : BitVec 64} {errnoVal : BitVec 32} {s0 s : State} {oom : State → SepProp}
    (hWords : Blk07HasWords116 mallocngFaultSvc)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hPc : s.pc = mbase 7 + (words_ret_off% blk07Words - 16#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = m) (hCs21 : Cs21Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hDelta : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem s.mem)
    (hmProps : m ≠ 0#64 ∧ 4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧ m ∉ st.reservedMetas)
    (hWf' : MallocngWFInflight (inflight + 1) maddrs.base brkStart s.brk liveCost peakCost st')
    (hPres : st'.reservedMetas = m :: st.reservedMetas ∧ st'.groups = st.groups ∧ st'.activeLists = st.activeLists ∧
      st'.liveMap = st.liveMap ∧ st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
      st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧ st'.ctx.seq = st.ctx.seq)
    (hGrpPost : ∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          (m ↦₆₄ w0) ∗ ((m + 8#64) ↦₆₄ w1) ∗ ((m + 16#64) ↦ₛ List.replicate 24 0#8) ∗
          CtxCells maddrs.ctx st'.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
          ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
          MappedSet st'.masterDom (OwnedMappedByte st'))))
      (AllocMetaPlacedPost inflight γ tp brkStart liveCost peakCost peakCount st s0) oom := by
  have hSpA : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hSp0
  have hSpSub : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 80#64 hSpA
  have hSubAddSp : s0.sp - 80#64 + 80#64 = s0.sp := BitVec.sub_add_cancel s0.sp 80#64
  refine SepWP.mono (sepWP_lift_noSyscalls_cl
    (sepPost (fun sf => MallocngProcPreserved s0 sf ∧ sf.brk = s.brk ∧ sf.readReg64 .x0 = m ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          (m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦ₛ List.replicate 24 0#8) ∗
          CtxCells maddrs.ctx st'.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
          ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
          MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl ?_) ?_
  · unfold StackFrameOpen SavedRegs0
    simp only [BitVec.reduceSub] at hPc
    wp_sym_steps
    simp only [hSubAddSp] at *
    obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc
    obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21
    wp_done
  · intro sf P_f _ _ ⟨_, hD2, _, ⟨hProcF, hBrkF, hx0F, hSpF, hCsF⟩, hEnt⟩
    refine ⟨Entails.trans hEnt ?_, hSpF, hCsF⟩
    refine Entails.sepExists_right st' (Entails.sepExists_right m ?_)
    have hDeltaF : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem sf.mem :=
      MallocngMappedDelta.mono (by decide) (by omega) (MallocngMappedDelta.trans hDelta hD2)
    have ⟨hActL, hUseL, hUnmapL, hBncL, hPadEq, _⟩ := hWf'.ctx_lens
    have hCtxEq := (ctx_toBytes_eq_cells maddrs.ctx st'.ctx hActL hUseL hUnmapL hBncL (by rw [hPadEq]; rfl)).symm
    have hZ40 := (zero40_eq_cells m).symm
    have hWfF : MallocngWFInflight (inflight + 1) maddrs.base brkStart sf.brk liveCost peakCost st' := hBrkF ▸ hWf'
    have hCntEq : totalLiveCount st' = totalLiveCount st := by unfold totalLiveCount; rw [hPres.2.1]
    refine Entails.pure_right ⟨hProcF, hx0F, hmProps.1, hmProps.2.1, hmProps.2.2.1, hmProps.2.2.2.1, hmProps.2.2.2.2,
      hPres.1, hPres.2.1, hPres.2.2.1, hPres.2.2.2.1, hCntEq, hPres.2.2.2.2.1, hPres.2.2.2.2.2.1,
      hPres.2.2.2.2.2.2.1, hPres.2.2.2.2.2.2.2.1, hPres.2.2.2.2.2.2.2.2, hGrpPost, hDeltaF⟩ ?_
    refine Entails.trans (sepConj_mono_left (stack224_fold s0)) ?_
    unfold StaticFrameA MallocngCoreStInflightA MallocngRuntime
    rw [← hCtxEq, ← hZ40, pure_sepConj_of_true hWfF]
    sep_frame

theorem sepWP_epilogue_26c [MallocngMultiPlacement]
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {st st' : MallocngSt} {m oldAv oldCnt : BitVec 64} {errnoVal : BitVec 32} {s0 s : State} {oom : State → SepProp}
    (hWords : Blk07HasWords116 mallocngFaultSvc)
    (_hRange : Blk07Range116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hPc : s.pc = mbase 7 + (words_ret_off% blk07Words - 28#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = m) (hx0 : s.readReg64 .x0 = st'.ctx.availMetaCount)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx)
    (hAvEq : st'.ctx.availMeta = m + 40#64)
    (hCs21 : Cs21Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hDelta : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem s.mem)
    (hmProps : m ≠ 0#64 ∧ 4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧ m ∉ st.reservedMetas)
    (hWf' : MallocngWFInflight (inflight + 1) maddrs.base brkStart s.brk liveCost peakCost st')
    (hPres : st'.reservedMetas = m :: st.reservedMetas ∧ st'.groups = st.groups ∧ st'.activeLists = st.activeLists ∧
      st'.liveMap = st.liveMap ∧ st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
      st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧ st'.ctx.seq = st.ctx.seq)
    (hGrpPost : ∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          (m ↦ₛ List.replicate 40 0#8) ∗
          CtxCells maddrs.ctx { st'.ctx with availMeta := oldAv, availMetaCount := oldCnt } ∗
          ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
          ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
          MappedSet st'.masterDom (OwnedMappedByte st'))))
      (AllocMetaPlacedPost inflight γ tp brkStart liveCost peakCost peakCount st s0) oom := by
  rw [zero40_eq_cells m]
  refine SepWP.cut_at_off (mbase 7) (words_ret_off% blk07Words - 16#64)
    (SepWP.mono (sepWP_lift_noSyscalls_cl (sepPost (fun s1 =>
      s1.pc = mbase 7 + (words_ret_off% blk07Words - 16#64) ∧
      s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧ s1.readReg64 .x19 = m ∧
      Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          (m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦ₛ List.replicate 24 0#8) ∗
          CtxCells maddrs.ctx st'.ctx ∗ ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
          ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
          MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl ?_) ?_)
  · unfold CtxCells; dsimp only [ctxMiddleBytes]
    simp only [BitVec.reduceSub] at hPc
    conv => arg 2; simp only [BitVec.reduceSub]
    wp_sym_steps
    simp only [← hAvEq] at *
    obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc
    obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21
    wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    exact SepWP.weaken_pre hEnt1 (sepWP_epilogue_278 hWords hcl1 hPc1 hRun1 hSp1 hSp0 hx19_1 hCs1 hProc1
      (MallocngMappedDelta.mono (by decide) (by omega) (MallocngMappedDelta.trans hDelta hD1))
      hmProps (hBrk1 ▸ hWf') hPres hGrpPost)

theorem sepWP_activate_2a0 [MallocngMultiPlacement]
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {st st' : MallocngSt} {ap oldAv oldCnt oldHd oldTl oldAreas : BitVec 64}
    {bv0 bv1 : BitVec 64 → BitVec 8} {errnoVal : BitVec 32} {s0 s : State} {oom : State → SepProp}
    (hWords : Blk07HasWords116 mallocngFaultSvc)
    (hRange : Blk07Range116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hPc : s.pc = mbase 7 + (words_ret_off% blk07Words + 24#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx)
    (hx21 : s.readReg64 .x21 = ap) (hCs25 : Cs25Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hDelta : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem s.mem)
    (hCtxEqs : st'.ctx.availMeta = ap + 64#64 ∧ st'.ctx.availMetaCount = 100#64 ∧
      st'.ctx.metaAreaTail = ap ∧ st'.ctx.availMetaAreas = ap + 4096#64 ∧
      (st.metaAreas = [] → oldTl = 0#64 ∧ st'.ctx.metaAreaHead = ap) ∧
      (∀ hne : st.metaAreas ≠ [], oldTl = (st.metaAreas.getLast hne).base ∧ oldHd = st'.ctx.metaAreaHead ∧ (oldTl == 0#64) = false))
    (hTailBm : ∀ hne : st.metaAreas ≠ [], let tb := (st.metaAreas.getLast hne).base
      ByteMap st'.masterDom (OwnedRwByte st) bv0 = ((tb ↦ₛ metaHdrBytes st'.ctx.secret 0#64) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) ∧
      ((tb ↦ₛ metaHdrBytes st'.ctx.secret ap) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) = ByteMap st'.masterDom (OwnedRwByte st) bv1)
    (hNilBv : st.metaAreas = [] → bv1 = bv0)
    (hApBm : ((ap ↦ₛ metaHdrBytes st'.ctx.secret 0#64) ∗ ((ap + 64#64) ↦ₛ List.replicate 4032 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st) bv1) = ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal)
    (hmProps : (ap + 24#64) ≠ 0#64 ∧ 4096 ≤ (ap + 24#64).toNat ∧ (ap + 24#64).toNat % 8 = 0 ∧ (ap + 24#64).toNat + 40 ≤ 2 ^ 48 ∧ (ap + 24#64) ∉ st.reservedMetas)
    (hWf' : MallocngWFInflight (inflight + 1) maddrs.base brkStart s.brk liveCost peakCost st')
    (hPres : st'.reservedMetas = (ap + 24#64) :: st.reservedMetas ∧ st'.groups = st.groups ∧ st'.activeLists = st.activeLists ∧
      st'.liveMap = st.liveMap ∧ st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
      st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧ st'.ctx.seq = st.ctx.seq)
    (hGrpPost : ∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          (ap ↦ₛ List.replicate 4096 0#8) ∗
          CtxCells maddrs.ctx { st'.ctx with availMeta := oldAv, availMetaCount := oldCnt, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := oldHd, metaAreaTail := oldTl, availMetaAreas := oldAreas } ∗
          ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
          ByteMap st'.masterDom (OwnedRwByte st) bv0 ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
          MappedSet st'.masterDom (OwnedMappedByte st'))))
      (AllocMetaPlacedPost inflight γ tp brkStart liveCost peakCost peakCount st s0) oom := by
  have hSpA : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hSp0
  have hSpSub : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 80#64 hSpA
  have hCntSub : st'.ctx.availMetaAreaCount + 1#64 - 1#64 = st'.ctx.availMetaAreaCount := BitVec.add_sub_cancel _ _
  have hAv64 : (ap + 24#64) + 40#64 = ap + 64#64 := by bv_arith
  rw [zeroPage_eq_metaArea_cells ap]
  refine SepWP.cut_at_off (mbase 7) (words_ret_off% blk07Words - 28#64)
    (SepWP.mono (sepWP_lift_noSyscalls_cl (sepPost (fun s1 =>
      s1.pc = mbase 7 + (words_ret_off% blk07Words - 28#64) ∧
      s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧ s1.readReg64 .x19 = ap + 24#64 ∧
      s1.readReg64 .x0 = st'.ctx.availMetaCount ∧ s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧
      Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          ((ap + 24#64) ↦ₛ List.replicate 40 0#8) ∗
          CtxCells maddrs.ctx { st'.ctx with availMeta := oldAv, availMetaCount := oldCnt } ∗
          ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
          ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
          MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl ?_) ?_)
  · rw [← hApBm, metaHdrBytes_eq_cells]
    unfold StackFrameSlow SavedRegs21 CtxCells; dsimp only [ctxMiddleBytes]
    conv => arg 2; simp only [BitVec.reduceSub]
    cases hMaEq : st.metaAreas with
    | nil =>
      obtain ⟨hTl0, hHdAp⟩ := hCtxEqs.2.2.2.2.1 hMaEq
      rw [hNilBv hMaEq, hTl0]
      wp_sym_steps
      simp only [hCntSub, ← hHdAp, ← hCtxEqs.2.1] at *
      obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25
      wp_done
    | cons hd tl =>
      have hne : st.metaAreas ≠ [] := by simp [hMaEq]
      obtain ⟨hTlEq, hHdEq, hTlBeq⟩ := hCtxEqs.2.2.2.2.2 hne
      obtain ⟨hExT, hAbsT⟩ := hTailBm hne
      rw [hExT, ← hAbsT, metaHdrBytes_eq_cells, metaHdrBytes_eq_cells, hTlEq, hHdEq]
      rw [hTlEq] at hTlBeq
      simp only [hMaEq] at hTlBeq ⊢
      wp_sym_steps
      simp only [hCntSub, ← hCtxEqs.2.1] at *
      obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25
      wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hx0_1, hx20_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    have hEnt2 := Entails.trans hEnt1 (sepConj_mono_left (stackSlow_to_open s0))
    exact SepWP.weaken_pre hEnt2 (sepWP_epilogue_26c hWords hRange hcl1 hPc1 hRun1 hSp1 hSp0
      hx19_1 hx0_1 hx20_1 (hCtxEqs.1.trans hAv64.symm) hCs1 hProc1
      (MallocngMappedDelta.mono (by decide) (by omega) (MallocngMappedDelta.trans hDelta hD1))
      hmProps (hBrk1 ▸ hWf') hPres hGrpPost)

theorem stack64_split_48 {s : State} {sp : BitVec 64} (hSp : s.sp = sp) :
    stackAt sp 64 = (memRegion (sp - 64#64) 16 ∗ stackFrame s 48) := by
  have h1 : stackAt sp 64 = (memRegion (sp - 64#64) 16 ∗ stackAt sp 48) := stackAt_split_bottom sp 48 16 (by decide)
  rw [h1, stackAt_eq_stackFrameAt sp 48, stackFrameAt_eq_memRegion sp 48]; unfold stackFrame; rw [hSp]

theorem sepWP_mprotect_224 [MallocngMultiPlacement]
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {st st' : MallocngSt} {ap oldAv oldCnt oldHd oldTl oldAreas : BitVec 64}
    {bv0 bv1 : BitVec 64 → BitVec 8} {errnoVal : BitVec 32} {s0 s : State}
    (hWords : Blk07HasWords116 mallocngFaultSvc)
    (hRange : Blk07Range116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hPc : s.pc = mbase 7 + (reloc_call_off% blk07Relocs "mprotect" - 12#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hTp0 : s0.tpidrEl0 = tp)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx) (hx21 : s.readReg64 .x21 = ap) (hx24 : s.readReg64 .x24 = 4096#64)
    (hApAlign : 4096 ∣ ap.toNat) (hApFit : ap.toNat + 4096 ≤ 2 ^ 48)
    (hCs25 : Cs25Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hDelta : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount - 4096) s0.mem s.mem)
    (hCtxEqs : st'.ctx.availMeta = ap + 64#64 ∧ st'.ctx.availMetaCount = 100#64 ∧
      st'.ctx.metaAreaTail = ap ∧ st'.ctx.availMetaAreas = ap + 4096#64 ∧
      (st.metaAreas = [] → oldTl = 0#64 ∧ st'.ctx.metaAreaHead = ap) ∧
      (∀ hne : st.metaAreas ≠ [], oldTl = (st.metaAreas.getLast hne).base ∧ oldHd = st'.ctx.metaAreaHead ∧ (oldTl == 0#64) = false))
    (hTailBm : ∀ hne : st.metaAreas ≠ [], let tb := (st.metaAreas.getLast hne).base
      ByteMap st'.masterDom (OwnedRwByte st) bv0 = ((tb ↦ₛ metaHdrBytes st'.ctx.secret 0#64) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) ∧
      ((tb ↦ₛ metaHdrBytes st'.ctx.secret ap) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) = ByteMap st'.masterDom (OwnedRwByte st) bv1)
    (hNilBv : st.metaAreas = [] → bv1 = bv0)
    (hApBm : ((ap ↦ₛ metaHdrBytes st'.ctx.secret 0#64) ∗ ((ap + 64#64) ↦ₛ List.replicate 4032 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st) bv1) = ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal)
    (hmProps : (ap + 24#64) ≠ 0#64 ∧ 4096 ≤ (ap + 24#64).toNat ∧ (ap + 24#64).toNat % 8 = 0 ∧ (ap + 24#64).toNat + 40 ≤ 2 ^ 48 ∧ (ap + 24#64) ∉ st.reservedMetas)
    (hWf' : MallocngWFInflight (inflight + 1) maddrs.base brkStart s.brk liveCost peakCost st')
    (hPres : st'.reservedMetas = (ap + 24#64) :: st.reservedMetas ∧ st'.groups = st.groups ∧ st'.activeLists = st.activeLists ∧
      st'.liveMap = st.liveMap ∧ st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
      st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧ st'.ctx.seq = st.ctx.seq)
    (hGrpPost : ∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          (ap ↦ₙ List.replicate 4096 0#8) ∗
          CtxCells maddrs.ctx { st'.ctx with availMeta := oldAv, availMetaCount := oldCnt, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := oldHd, metaAreaTail := oldTl, availMetaAreas := oldAreas } ∗
          ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
          ByteMap st'.masterDom (OwnedRwByte st) bv0 ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
          MappedSet st'.masterDom (OwnedMappedByte st'))))
      (AllocMetaPlacedPost inflight γ tp brkStart liveCost peakCost peakCount st s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc 1 (allocMetaPlacedByteBound peakCount) s0 sf⌝) := by
  let P_rest := StaticFrameA γ maddrs st'.liveMap ∗
    CtxCells maddrs.ctx { st'.ctx with availMeta := oldAv, availMetaCount := oldCnt, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := oldHd, metaAreaTail := oldTl, availMetaAreas := oldAreas } ∗
    ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
    ByteMap st'.masterDom (OwnedRwByte st) bv0 ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
    MappedSet st'.masterDom (OwnedMappedByte st')
  let retPc := mbase 7 + (reloc_call_off% blk07Relocs "mprotect" + 4#64)
  refine SepWP.cut (mid := mbase 17)
    (SepWP.mono (sepWP_lift_noSyscalls_cl (sepPost (fun s1 =>
      s1.pc = mbase 17 ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 Reg.lr = retPc ∧ s1.readReg64 .x0 = ap ∧ s1.readReg64 .x1 = 4096#64 ∧ s1.readReg32 .x2 = 3#32 ∧
      s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s1.readReg64 .x21 = ap ∧
      Cs25Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ ((ap ↦ₙ List.replicate 4096 0#8) ∗ P_rest))))) hcl ?_) ?_)
  · dsimp only [P_rest, retPc] at hPc ⊢
    simp only [BitVec.reduceSub] at hPc
    wp_sym_steps
    simp only [show ∀ x y : BitVec 64, x + (y - x) = y from fun _ _ => by bv_arith] at *
    obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25
    wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hLr1, hx0_1, hx1_1, hx2_1, hx20_1, hx21_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    refine SepWP.weaken_pre hEnt1 ?_
    unfold StackFrameSlow; rw [stack64_split_48 hSp1]
    have hSpA1 : s1.spAligned = true := by rw [State.spAligned, hSp1]; exact spAligned_sub s0.sp 80#64 (by simpa [State.spAligned] using hSp0)
    have hTp1 : s1.tpidrEl0 = tp := hProc1.2.2.1.trans hTp0
    have hx1Nat : (s1.readReg64 .x1).toNat = 4096 := by rw [hx1_1]; rfl
    refine call_withCL_frame_auto (x := ())
      (placed_mprotectRwWrapper_ok (P := mallocngBlockProg mmpl 7 msvc) tp ap errnoVal (List.replicate 4096 0#8) 4096 List.length_replicate (by decide) (by decide) hApAlign hApFit (by intro pc; simp) rfl)
      hcl1 hPc1 hRun1 hSpA1 hLr1 (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (h_oom := fun R' sf _ hSatOom => by
        have hDrop := Satisfies.drop_mid hSatOom
        rw [satisfies_pure_sepConj] at hDrop ⊢
        obtain ⟨hFsEq, hTrEq, hSigEq, _, hDMp, hPhysLt⟩ := hDrop.1
        exact ⟨MallocngPlacedOomCond.of_delta (hFsEq.trans hProc1.1) (hTrEq.trans hProc1.2.1)
          (hSigEq.trans hProc1.2.2.2.2.2.2) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta hD1) hDMp)
          (by decide) (by unfold allocMetaPlacedByteBound; omega)
          fun _ => ⟨4096, by decide, by decide, by unfold allocMetaPlacedByteBound; omega, Or.inr hPhysLt⟩, hDrop.2⟩) ?_
    intro s2 hPc2 hRun2 hSp2 hCsCall hcl2
    dsimp only
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hProcCall, hBrk2, hw0_2, hDCall⟩
    refine SepWP.weaken_pre (Entails.trans
      (Q := (memRegion (s0.sp - 80#64 - 64#64) 16 ∗ stackFrame s1 48) ∗
        (memRegion (s0.sp - 224#64) 80 ∗ SavedRegs0 s0 ∗ SavedRegs21 s0 ∗ cells (s0.sp - 16#64) 2 ∗
          (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ (ap ↦ₛ List.replicate 4096 0#8) ∗ P_rest))))
      (R := StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ (ap ↦ₛ List.replicate 4096 0#8) ∗ P_rest)))
      (by unfold SavedRegs0 SavedRegs21; dsimp only [P_rest]; sep_frame)
      (by rw [← stack64_split_48 hSp1]; unfold StackFrameSlow; sep_frame)) ?_
    refine SepWP.cut_at_off (mbase 7) (words_ret_off% blk07Words + 24#64)
      (SepWP.mono (sepWP_lift_noSyscalls_cl (sepPost (fun s3 =>
        s3.pc = mbase 7 + (words_ret_off% blk07Words + 24#64) ∧
        s3.status = .Running ∧ s3.sp = s0.sp - 80#64 ∧
        s3.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s3.readReg64 .x21 = ap ∧
        Cs25Preserved s0 s3 ∧ MallocngProcPreserved s0 s3 ∧ s3.brk = s.brk)
        (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ (ap ↦ₛ List.replicate 4096 0#8) ∗ P_rest)))) hcl2 ?_) ?_)
    · dsimp only [retPc] at hPc2
      have hx20_2 : s2.readReg64 .x20 = Obj.pageOf maddrs.ctx := hCsCall.2.1.trans hx20_1
      have hx21_2 : s2.readReg64 .x21 = ap := hCsCall.2.2.1.trans hx21_1
      have hCs2 : Cs25Preserved s0 s2 := ⟨hCsCall.2.2.2.2.2.2.1.trans hCs1.1, hCsCall.2.2.2.2.2.2.2.1.trans hCs1.2.1,
        hCsCall.2.2.2.2.2.2.2.2.1.trans hCs1.2.2.1, hCsCall.2.2.2.2.2.2.2.2.2.1.trans hCs1.2.2.2.1, hCsCall.2.2.2.2.2.2.2.2.2.2.2.trans hCs1.2.2.2.2⟩
      have hProc2 : MallocngProcPreserved s0 s2 := MallocngProcPreserved.trans hProc1 hProcCall
      have hw0Cond : (BitVec.zeroExtend 64 (BitVec.truncate 32 (s2.readReg64 (Reg.gpr 0#5))) == 0#64) = true := by
        change (BitVec.zeroExtend 64 (s2.readReg32 .x0) == 0#64) = true; rw [hw0_2]; rfl
      dsimp only [P_rest]
      conv => arg 2; simp only [BitVec.reduceAdd]
      wp_sym_steps
      obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc2; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs2
      rw [← hBrk1, ← hBrk2]
      wp_done
    · intro s3 P3 hPc3 hRun3 ⟨_, hD3, hcl3, ⟨_, _, hSp3, hx20_3, hx21_3, hCs3, hProc3, hBrk3⟩, hEnt3⟩
      have hDTot : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem s3.mem := by
        refine MallocngMappedDelta.mono ?_ ?_
          (MallocngMappedDelta.trans (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta hD1) hDCall) hD3)
        all_goals omega
      exact SepWP.weaken_pre (Entails.trans hEnt3 (by dsimp only [P_rest]; sep_frame))
        (sepWP_activate_2a0 hWords hRange hcl3 hPc3 hRun3 hSp3 hSp0
          hx20_3 hx21_3 hCs3 hProc3 hDTot hCtxEqs hTailBm hNilBv hApBm hmProps (hBrk3 ▸ hWf') hPres hGrpPost)

theorem metaAreas_ctx_eqs {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat}
    {st st' : MallocngSt} {ap : BitVec 64}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (h1 : st'.ctx.availMeta = ap + 64#64) (h2 : st'.ctx.availMetaCount = 100#64)
    (h3 : st'.ctx.metaAreaTail = ap) (h4 : st'.ctx.availMetaAreas = ap + 4096#64)
    (h5 : st'.ctx.metaAreaHead = match st.metaAreas with | [] => ap | hd :: _ => hd.base) :
    st'.ctx.availMeta = ap + 64#64 ∧ st'.ctx.availMetaCount = 100#64 ∧
      st'.ctx.metaAreaTail = ap ∧ st'.ctx.availMetaAreas = ap + 4096#64 ∧
      (st.metaAreas = [] → st.ctx.metaAreaTail = 0#64 ∧ st'.ctx.metaAreaHead = ap) ∧
      (∀ hne : st.metaAreas ≠ [], st.ctx.metaAreaTail = (st.metaAreas.getLast hne).base ∧ st.ctx.metaAreaHead = st'.ctx.metaAreaHead ∧ (st.ctx.metaAreaTail == 0#64) = false) := by
  refine ⟨h1, h2, h3, h4, fun hNil => ?_, ?_⟩
  · have hM := hwf.metaAreas_wf.2.2; simp only [hNil] at hM h5; exact ⟨hM.2, h5⟩
  · have hM := hwf.metaAreas_wf.2.2; have hB := hwf.metaAreas_wf.2.1
    cases hEq : st.metaAreas with
    | nil => intro hne; exact False.elim (hne rfl)
    | cons hd tl =>
      intro hne; simp only [hEq] at hM hB h5
      have hTl := (hM.2.1 hne).1
      have hGe := (hB _ (List.getLast_mem hne)).1
      exact ⟨hTl, hM.1.trans h5.symm, beq_false_of_ne fun h0 => by rw [← hTl, h0] at hGe; exact absurd hGe (by decide)⟩

end VerifiedLibraries.Mallocng.Proofs
