/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.BV
public import ProofLib.ProgramReflection
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.StdStartup.NonVmSteps
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
public import VerifiedLibraries.Mallocng.Proofs.RdlAllocProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocHelpers
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.IfaceBudgetBaseBridges

/-!
# Placed Rust Global-Allocator Shim Contracts for `mallocngRustCliAllocBudget`

Cost-model-parametric verification of the compiled `rustc` global-allocator shims
`__rustc::__rdl_{alloc,dealloc,realloc}` and 1-instruction `B`-thunk entry points
`__rustc::__rust_{alloc,dealloc,realloc}` against `LibsignalBinary.Heap.IfaceBudget` for any
`(M, I)` satisfying `MallocngCostModelSound M I`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap

open Arm64 Arm64.Obj Arm64.CType ProofLib.SepLogic ProofLib.ProgramReflection ProofLib.StdStartup
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open CryptoVerification.RustHeap (allocHookStack)
open VerifiedLibraries.Mallocng (
  IsPow2Align MallocngAddrs MallocngLayoutFit MallocngMaxAllocSize MaxAlignedAllocAlign
  alignedAllocAlignOk mallocngAddrsOfPlacement mallocngAlignedEffSize
  mallocngPosixMemalignOk mallocngPosixMemalignRet mallocngStackBytes
)
open VerifiedLibraries.Mallocng.Proofs (
  ProgContainsMallocng cond_eq_subs32_iff_eq copyFinish_entails copyPrep_entails effAlign_props
  isPow2Align_alignedAllocOk isPow2Align_dvd_16 isPow2Align_dvd_max16
  isPow2Align_of_toNat_pow2 memRegion_entails_exists_pointsToBytes
  not_layoutFit_imp_gt_2pow62 pack_stack64 pow2_dvd_16_of_le_16 pow2_dvd_max16
  rdlRealloc_effAlign_props spAligned_sub64 subroutine_ok_of_b_thunk
)
open VerifiedLibraries.RustStd (
  MallocngCEntryAddrs RustStdAllocAddrs RustStdRdlShimCode RustStdThunkCode
  allocCallPreserved_of_fields_eq allocCallPreserved_trans
  fetch_instr_at fetch_instr_at0 hookFrame_eq_stack1024 hookFrame_eq_stack32_1024
  hookFrame_eq_stack64_1024 mallocngPlacedCAddrs rdlAllocInstrs rdlDeallocInstrs rdlReallocInstrs
)

/-! ## Address Conversions -/

def RustAllocAddrs.toRustStd (a : RustAllocAddrs) : RustStdAllocAddrs where
  alloc   := a.alloc
  dealloc := a.dealloc
  realloc := a.realloc

def RustAllocAddrs.ofRustStd (a : RustStdAllocAddrs) : RustAllocAddrs where
  alloc   := a.alloc
  dealloc := a.dealloc
  realloc := a.realloc

@[simp] theorem RustAllocAddrs.toRustStd_alloc (a : RustAllocAddrs) :
    a.toRustStd.alloc = a.alloc := rfl

@[simp] theorem RustAllocAddrs.toRustStd_dealloc (a : RustAllocAddrs) :
    a.toRustStd.dealloc = a.dealloc := rfl

@[simp] theorem RustAllocAddrs.toRustStd_realloc (a : RustAllocAddrs) :
    a.toRustStd.realloc = a.realloc := rfl

/-! ## State-Preservation, Spatial, and Alignment Helpers -/

attribute [local simp] Memory.perm_write8 Memory.perm_write16 Memory.perm_write32
  Memory.perm_write64 Memory.perm_writeBytes

@[local simp] private theorem physMemAvail_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).physMemAvail = s.physMemAvail := by cases s; rfl

@[local simp] private theorem physMemAvail_advancePC (s : State) :
    s.advancePC.physMemAvail = s.physMemAvail := by cases s; rfl

@[local simp] private theorem physMemAvail_setPState (s : State) (ps : PState) :
    (s.setPState ps).physMemAvail = s.physMemAvail := by cases s; rfl

@[local simp] private theorem physMemAvail_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).physMemAvail = s.physMemAvail := by cases s; cases r <;> rfl

@[local simp] private theorem physMemAvail_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).physMemAvail = s.physMemAvail := physMemAvail_writeReg64 s r _

@[local simp] private theorem physMemAvail_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).physMemAvail = s.physMemAvail := physMemAvail_writeReg64 s r _

@[local simp] private theorem physMemAvail_setMem (s : State) (m : Memory) :
    (s.setMem m).physMemAvail = s.physMemAvail := by cases s; rfl

@[local simp] private theorem perm_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).mem.perm = s.mem.perm := by cases s; rfl

@[local simp] private theorem perm_advancePC (s : State) :
    s.advancePC.mem.perm = s.mem.perm := by cases s; rfl

@[local simp] private theorem perm_setPState (s : State) (ps : PState) :
    (s.setPState ps).mem.perm = s.mem.perm := by cases s; rfl

@[local simp] private theorem perm_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem.perm = s.mem.perm := by cases s; cases r <;> rfl

@[local simp] private theorem perm_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).mem.perm = s.mem.perm := perm_writeReg64 s r _

@[local simp] private theorem perm_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).mem.perm = s.mem.perm := perm_writeReg64 s r _

@[local simp] private theorem perm_setMem (s : State) (m : Memory) :
    (s.setMem m).mem.perm = m.perm := by cases s; rfl

private theorem step_str64_perm {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 64}
    (hfetch : prog.fetch pc = some (.str .X64 rt addr))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val)
    (hstore : SepStore64 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .X64 rt addr) := hpc.symm ▸ hfetch
  let m' := s.mem.write64 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea _ = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .X64 rt addr) s = s'.setMem m' := by
    rw [evalInst_eq_execInst_of_not_isSvc0 prog rfl s, ← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write64 s.mem ea val)) hm'

private theorem step_stp64_perm {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1)
    (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W64 rt1 rt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [evalInst_eq_execInst_of_not_isSvc0 prog rfl s, ← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1))) hm2

local macro "wp_str64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_str64_perm $hf
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_sep_access
  · wp_focus_close wp_norm_lhs
  intro $m $hm
  try wp_norm_state))

local macro "wp_stp64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_stp64_perm $hf
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_sep_access
  · wp_focus_close wp_sep_access
  · wp_focus_close wp_norm_lhs
  intro $m $hm
  try wp_norm_state))

private theorem mallocngBudgetPoolAt_setPC (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mAddrs : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) (s : State) (pc : BitVec 64) :
    mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st (s.setPC pc) =
      mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s :=
  mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim st
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

private theorem mallocngBudgetPoolAt_setPState (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mAddrs : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) (s : State) (ps : PState) :
    mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st (s.setPState ps) =
      mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s :=
  mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim st
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun _ => by cases s; rfl, fun _ _ _ => by cases s; rfl⟩

private theorem mallocngBudgetPoolAt_writeReg64 (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mAddrs : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) (s : State) (r : Reg) (v : BitVec 64) :
    mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st (s.writeReg64 r v) =
      mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s :=
  mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim st
    ⟨⟨rfl, rfl, rfl⟩, by cases s; cases r <;> rfl, fun _ => by cases s; cases r <;> rfl,
     fun _ _ _ => by cases s; cases r <;> rfl⟩

private theorem mallocngBudgetPoolAt_setMem_of_perm (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mAddrs : MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) (s : State) {m : Memory} (hm : m.perm = s.mem.perm) :
    mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st (s.setMem m) =
      mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s :=
  mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim st
    ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun a => by cases s; exact congrFun hm a,
     fun _ _ _ => by cases s; rfl⟩

private theorem vmPreserved_of_eq {s0 s1 : State}
    (hbs : s1.brkStart = s0.brkStart) (hbrk : s1.brk = s0.brk)
    (htp : s1.tpidrEl0 = s0.tpidrEl0) (hphys : s1.physMemAvail = s0.physMemAvail)
    (hperm : s1.mem.perm = s0.mem.perm)
    (hfs : s1.fs = s0.fs := by simp [arm64_norm]) :
    VmPreserved s0 s1 :=
  ⟨⟨hbs, hbrk, htp⟩, hphys, fun a => congrFun hperm a, FdsHiFrame.of_fs_eq hfs⟩

private theorem vmPreserved_trans {s0 s1 s2 : State}
    (h01 : VmPreserved s0 s1) (h12 : VmPreserved s1 s2) :
    VmPreserved s0 s2 :=
  h01.trans h12

private theorem vmPreserved_of_fields_eq {s0 s1 sf : State}
    (hbs : s1.brkStart = s0.brkStart) (hbrk : s1.brk = s0.brk)
    (htp : s1.tpidrEl0 = s0.tpidrEl0) (hphys : s1.physMemAvail = s0.physMemAvail)
    (hperm : s1.mem.perm = s0.mem.perm) (h1f : VmPreserved s1 sf)
    (hfs : s1.fs = s0.fs := by simp [arm64_norm]) :
    VmPreserved s0 sf :=
  vmPreserved_trans (vmPreserved_of_eq hbs hbrk htp hphys hperm hfs) h1f

private theorem oomPreserved_of_allocCallPreserved {s0 s1 sf : State}
    (h01 : AllocCallPreserved s0 s1) (h1f : OomPreserved s1 sf) :
    OomPreserved s0 sf :=
  ⟨h1f.1.trans h01.1, h1f.2.1.trans h01.2.1, h1f.2.2.trans h01.2.2.1⟩

private theorem oomPreserved_of_fields_eq {s0 s1 sf : State}
    (hfs : s1.fs = s0.fs) (htr : s1.trace = s0.trace) (hsig : s1.sigActions = s0.sigActions)
    (h1f : OomPreserved s1 sf) : OomPreserved s0 sf :=
  ⟨h1f.1.trans hfs, h1f.2.1.trans htr, h1f.2.2.trans hsig⟩

private theorem allocCallPreserved_of_eq {s0 sf : State}
    (hfs : sf.fs = s0.fs) (htr : sf.trace = s0.trace) (hsig : sf.sigActions = s0.sigActions)
    (htp : sf.tpidrEl0 = s0.tpidrEl0) (hbs : sf.brkStart = s0.brkStart)
    (horc : sf.oracle = s0.oracle) (hsym : sf.symtab = s0.symtab) :
    VerifiedLibraries.RustStd.AllocCallPreserved s0 sf :=
  ⟨hfs, htr, hsig, htp, hbs, horc, hsym⟩

private theorem sixteen_dvd_max16_of_layoutOk {sz al : Nat} (h : RustLayoutOk sz al) :
    16 ∣ max al 16 := by
  obtain ⟨_, ⟨k, rfl⟩, _⟩ := h.1
  by_cases hk : k ≤ 4
  · have hle : 2 ^ k ≤ 16 := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    rw [Nat.max_eq_right hle]
    exact Nat.dvd_refl 16
  · have hge : 16 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ k)
    rw [Nat.max_eq_left hge, show k = 4 + (k - 4) by omega, Nat.pow_add]
    exact Nat.dvd_mul_right 16 (2 ^ (k - 4))

private theorem calleeSavedPreserved_trans {s0 s1 s2 : State}
    (h01 : CalleeSavedPreserved s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 :=
  VerifiedLibraries.Mallocng.Proofs.calleeSavedPreserved_trans h01 h12

private theorem stackAt_eq_hookFrame (sp : BitVec 64) :
    stackAt sp allocHookStack = Rust.hookFrame sp := rfl

private theorem unpackLiveM {M : AllocCostModel} {I : MallocngCostModelIface M}
    (γ : GhostName) (p : BitVec 64) (n al : Nat) :
    mallocngLiveM M I γ p n al ⊢
      ⌜p ≠ 0#64 ∧ al ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗
      I.BlockM γ p n (max al 16) := by
  unfold mallocngLiveM
  rw [sepConj_comm]
  exact Entails.refl _

private theorem packLiveM {M : AllocCostModel} {I : MallocngCostModelIface M}
    (γ : GhostName) {p : BitVec 64} {n al : Nat}
    (hpNe : p ≠ 0#64) (hAl : al ∣ p.toNat) (h16 : 16 ∣ p.toNat)
    (hFit : p.toNat + n < 2 ^ 64) (hLay : RustLayoutOk n al) :
    I.BlockM γ p n (max al 16) ⊢ mallocngLiveM M I γ p n al := by
  unfold mallocngLiveM
  rw [sepConj_comm]
  exact Entails.pure_right ⟨hpNe, hAl, h16, hFit, hLay⟩ (Entails.refl _)

private theorem packLiveM_16 {M : AllocCostModel} {I : MallocngCostModelIface M}
    (γ : GhostName) {p : BitVec 64} {n al : Nat}
    (hAl16 : al ≤ 16) (hpNe : p ≠ 0#64) (hAl : al ∣ p.toNat) (h16 : 16 ∣ p.toNat)
    (hFit : p.toNat + n < 2 ^ 64) (hLay : RustLayoutOk n al) :
    I.BlockM γ p n 16 ⊢ mallocngLiveM M I γ p n al := by
  have hm : max al 16 = 16 := Nat.max_eq_right hAl16
  rw [← hm]
  exact packLiveM γ hpNe hAl h16 hFit hLay

private theorem memRegion8_entails_pointsTo64 (a : BitVec 64) :
    memRegion a 8 ⊢ ∃∗ w : BitVec 64, a ↦₆₄ w := by
  refine Entails.trans (memRegion_entails_exists_pointsToBytes 8 a (by decide)) ?_
  refine Entails.sepExists_elim fun bs => Entails.pure_left fun hlen => ?_
  have htake : (bs.drop 0).take 8 = bs := by
    simp [List.take_of_length_le (by omega : bs.length ≤ 8)]
  have heq := pointsToBytes_take8_eq_pointsTo64 a bs 0 (by omega)
  rw [htake] at heq
  rw [heq]
  exact Entails.sepExists_right _ (Entails.refl _)

private theorem stackFrameAt32_eq (sp : BitVec 64) :
    stackFrameAt sp 32 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]

private theorem pack_stack32 (sp w0 w1 w2 w3 : BitVec 64) :
    (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
     ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ⊢ stackFrameAt sp 32 := by
  rw [stackFrameAt32_eq sp]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.refl _))))

private theorem spAligned_sub32 {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 32#64) &&& 15#64 == 0#64) = true := by
  revert h; bv_robdd

private theorem repack_hookFrame_64 (sp w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    (((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗
     ((sp - 48#64) ↦₆₄ w2) ∗ ((sp - 40#64) ↦₆₄ w3) ∗
     ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
     ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) ∗
    (stackFrameAt (sp - 64#64) mallocngStackBytes ∗
     stackFrameAt (sp - 64#64 - 1024#64) 3008) ⊢
      Rust.hookFrame sp := by
  rw [hookFrame_eq_stack64_1024 sp]
  exact sepConj_mono_left (pack_stack64 sp w0 w1 w2 w3 w4 w5 w6 w7)

private theorem repack_stack64_to_1024 (sp w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    (((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗
     ((sp - 48#64) ↦₆₄ w2) ∗ ((sp - 40#64) ↦₆₄ w3) ∗
     ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
     ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) ∗
    (stackFrameAt (sp - 64#64) mallocngStackBytes ∗
     stackFrameAt (sp - 64#64 - 1024#64) 3008) ⊢
      stackFrameAt sp mallocngStackBytes ∗ stackFrameAt (sp - 1024#64) 3072 := by
  rw [← hookFrame_eq_stack1024 sp]
  exact repack_hookFrame_64 sp w0 w1 w2 w3 w4 w5 w6 w7

private theorem unpack_stack64 (sp : BitVec 64) :
    stackFrameAt sp 64 ⊢
      ∃∗ sv0 : BitVec 64, ∃∗ sv1 : BitVec 64, ∃∗ sv2 : BitVec 64, ∃∗ sv3 : BitVec 64,
      ∃∗ sv4 : BitVec 64, ∃∗ sv5 : BitVec 64, ∃∗ sv6 : BitVec 64, ∃∗ sv7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ sv0) ∗ ((sp - 56#64) ↦₆₄ sv1) ∗ ((sp - 48#64) ↦₆₄ sv2) ∗
        ((sp - 40#64) ↦₆₄ sv3) ∗ ((sp - 32#64) ↦₆₄ sv4) ∗ ((sp - 24#64) ↦₆₄ sv5) ∗
        ((sp - 16#64) ↦₆₄ sv6) ∗ ((sp - 8#64) ↦₆₄ sv7) := by
  dsimp only [reduceStackFrameAt]; exact Entails.refl _

private theorem allocMemcpy_prep_entails (p q : BitVec 64) (bs : List (BitVec 8))
    (oldLen newLen copyLen : Nat)
    (h1 : bs.length ≤ copyLen) (h2 : copyLen ≤ oldLen) (h3 : copyLen ≤ newLen)
    (h4 : oldLen ≤ 2 ^ 64) (h5 : newLen ≤ 2 ^ 64) :
    ((p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (oldLen - bs.length) ∗
     memRegion q newLen) ⊢
    ∃∗ midBs : List (BitVec 8),
      ⌜(bs ++ midBs).length = copyLen⌝ ∗
      (memRegion q (bs ++ midBs).length ∗ (p ↦ₛ (bs ++ midBs))) ∗
      (memRegion (p + BitVec.ofNat 64 copyLen) (oldLen - copyLen) ∗
       memRegion (q + BitVec.ofNat 64 copyLen) (newLen - copyLen)) := by
  refine Entails.trans (copyPrep_entails p q bs oldLen newLen copyLen h1 h2 h3 h4 h5) ?_
  refine Entails.sepExists_elim fun dstBs => Entails.sepExists_elim fun midBs => ?_
  refine Entails.sepExists_right midBs ?_
  refine Entails.pure_left fun ⟨hdst, hmid⟩ => ?_
  refine Entails.pure_right hmid ?_
  have hqReg : (q ↦ₛ dstBs) ⊢ memRegion q (bs ++ midBs).length := by
    rw [hmid, ← hdst]
    exact (IsBlock.pointsToBytes q dstBs).entails_memRegion
  refine Entails.trans (sepConj_mono_left hqReg) ?_
  exact Entails.of_eq (by ac_rfl)

private theorem effAlign_disj_extra {align effAlign : BitVec 64}
    (hPow2 : IsPow2Align align)
    (hEff : (effAlign = align ∧ 8 < align.toNat) ∨ (effAlign = 8#64 ∧ align.toNat ≤ 8)) :
    effAlign.toNat = max align.toNat 8 ∧
    8 ≤ effAlign.toNat ∧
    alignedAllocAlignOk effAlign = true := by
  rcases hEff with ⟨rfl, hgt⟩ | ⟨rfl, hle⟩
  · exact ⟨by omega, by omega, isPow2Align_alignedAllocOk hPow2⟩
  · refine ⟨?_, by decide, by decide⟩
    change 8 = max align.toNat 8
    omega

/-! ## Placed `__rustc::__rdl_dealloc` -/

/-- Any `free` entry point satisfying `mallocngBudgetFreeCSpec` satisfies
    `rustCliDeallocBudgetSpec` over `mallocngRustCliAllocBudgetAt`. -/
theorem free_satisfies_rustCliDeallocBudgetSpec {M : AllocCostModel}
    {I : MallocngCostModelIface M} (hS : MallocngCostModelSound M I)
    (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart freeAddr : BitVec 64} {lim : BudgetLimits}
    (hFree : subroutine_ok P freeAddr (mallocngBudgetFreeCSpec M I γ mAddrs tp brkStart lim)) :
    subroutine_ok P freeAddr
      (rustCliDeallocBudgetSpecBase M (mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart) lim) := by
  let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
  apply subroutine_ok.of_codeLoaded
  rintro ⟨p, size, align, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [rustCliDeallocBudgetSpecBase, A, mallocngRustCliAllocBudgetAt] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, _hx1, _hx2⟩, hpre⟩ := hpre
  have hUnpack :
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
        (mallocngLiveM M I γ p size align ∗
          (memRegion p size ∗ stackAt s0.sp allocHookStack))) ∗ R ⊢
      ⌜p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64⌝ ∗
      ((⌜s0.readReg64 .x0 = p ∧
            (if p = 0#64 then size = 0 else 16 ∣ p.toNat ∧ p.toNat + size < 2 ^ 64)⌝ ∗
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
          (if p = 0#64 then emp else I.BlockM γ p size (max align 16) ∗ memRegion p size) ∗
          stackFrameAt s0.sp mallocngStackBytes) ∗
        (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R)) := by
    rw [stackAt_eq_hookFrame s0.sp, hookFrame_eq_stack1024 s0.sp]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (unpackLiveM γ p size align)))) ?_
    have hPull :
        (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
          ((⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧
              p.toNat + size < 2 ^ 64 ∧ RustLayoutOk size align⌝ ∗
            I.BlockM γ p size (max align 16)) ∗
           (memRegion p size ∗
             (stackFrameAt s0.sp mallocngStackBytes ∗ stackFrameAt (s0.sp - 1024#64) 3072)))) ∗ R =
        ⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧
            p.toNat + size < 2 ^ 64 ∧ RustLayoutOk size align⌝ ∗
          (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
            (I.BlockM γ p size (max align 16) ∗ memRegion p size) ∗
            stackFrameAt s0.sp mallocngStackBytes ∗
            (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R)) := by
      generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 = Ppool
      generalize stackFrameAt s0.sp mallocngStackBytes = Pstk1
      generalize stackFrameAt (s0.sp - 1024#64) 3072 = Pstk2
      ac_rfl
    rw [hPull]
    refine Entails.pure_left fun ⟨hpNe, _hAl, h16, hFit64, _hLay⟩ => ?_
    simp only [hpNe, ↓reduceIte]
    refine Entails.pure_right ⟨hpNe, h16, hFit64⟩ ?_
    refine Entails.trans ?_
      (sepConj_mono_left (Entails.pure_right ⟨hx0, h16, hFit64⟩ (Entails.refl _)))
    exact Entails.of_eq (by
      generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 = Ppool
      generalize stackFrameAt s0.sp mallocngStackBytes = Pstk1
      generalize stackFrameAt (s0.sp - 1024#64) 3072 = Pstk2
      ac_rfl)
  have hpre2 := Satisfies.mono hUnpack hpre
  rw [satisfies_pure_sepConj] at hpre2
  obtain ⟨⟨hpNe, _, _⟩, hpreFree⟩ := hpre2
  have hbeqF : (p == 0#64) = false := beq_false_of_ne hpNe
  refine subroutine_ok.mono_outcome hFree (p, size, align, st)
    (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R) s0 hpc hrun hpreFree hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [mallocngBudgetFreeCSpec] at hq
    dsimp only [rustCliDeallocBudgetSpecBase, A, mallocngRustCliAllocBudgetAt]
    rw [hbeqF] at hq
    simp only [Bool.false_eq_true, ↓reduceIte] at hq
    have hEvEq : M.stepEvents (rustDeallocEvents size align) st = M.step (.free align size) st := rfl
    have hLb : M.liveBytes (M.step (.free align size) st) ≤ M.liveBytes st :=
      M.liveBytes_free_le align size st
    rw [hEvEq]
    refine Satisfies.mono ?_ hq
    rw [stackAt_eq_hookFrame s0.sp, hookFrame_eq_stack1024 s0.sp]
    have hRearr :
        (⌜AllocCallPreserved s0 sf⌝ ∗
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim (M.step (.free align size) st) sf ∗
          stackFrameAt s0.sp mallocngStackBytes) ∗
          (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R) =
        (⌜AllocCallPreserved s0 sf⌝ ∗
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim (M.step (.free align size) st) sf ∗
          stackFrameAt s0.sp mallocngStackBytes ∗ stackFrameAt (s0.sp - 1024#64) 3072) ∗ R := by
      generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim (M.step (.free align size) st) sf = Ppool
      generalize stackFrameAt s0.sp mallocngStackBytes = Pstk1
      generalize stackFrameAt (s0.sp - 1024#64) 3072 = Pstk2
      ac_rfl
    rw [hRearr]
    refine sepConj_mono_left ?_
    refine Entails.pure_left fun hPres => ?_
    exact Entails.pure_right ⟨hPres, hLb⟩ (Entails.refl _)
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- Placed `rustc 1.98.1` `__rustc::__rdl_dealloc` (`1` instruction: `b free`) satisfies
    `rustCliDeallocBudgetSpec` over `mallocngRustCliAllocBudgetAt`. -/
theorem rdlDealloc_budget_placed_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart : BitVec 64}
    {cAddrs : MallocngCEntryAddrs} {callocAddr : BitVec 64}
    (deallocAddr : BitVec 64) (lim : BudgetLimits)
    (hCode : hasInstrs P deallocAddr (rdlDeallocInstrs deallocAddr cAddrs.free))
    (hC : MallocngProgBudgetCContracts M I γ mAddrs tp brkStart P cAddrs callocAddr) :
    subroutine_ok P deallocAddr
      (rustCliDeallocBudgetSpecBase M (mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart) lim) := by
  let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
  exact subroutine_ok_of_b_thunk (fetch_instr_at0 hCode)
    (hpre_pc := by
      rintro ⟨p, size, align, st⟩ s pc'
      dsimp only [rustCliDeallocBudgetSpecBase]
      rw [A.pool_setPC]
      cases s; rfl)
    (hpost_pc := by
      rintro ⟨_, _, _, _⟩ s0 _ _
      dsimp only [rustCliDeallocBudgetSpecBase, AllocCallPreserved]
      cases s0; rfl)
    (hoom_pc := by rintro ⟨_, _, _, _⟩ _ _ _; rfl)
    (hok := free_satisfies_rustCliDeallocBudgetSpec hS γ (hC.free_ok lim))

/-! ## Placed `__rustc::__rdl_alloc` -/

private theorem rdlAlloc_budget_fast_path {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart mallocAddr : BitVec 64} {lim : BudgetLimits}
    (hMalloc : subroutine_ok P mallocAddr (mallocngBudgetMallocCSpec M I γ mAddrs tp brkStart lim))
    (sizeBv alignBv : BitVec 64) (st : M.σ) (R : SepProp) (s0 s1 : State)
    (hsp_align : s0.spAligned = true)
    (hLayout : RustLayoutOk sizeBv.toNat alignBv.toNat)
    (hPow2 : IsPow2Align alignBv) (hAl16 : alignBv.toNat ≤ 16)
    (hAlSz : alignBv.toNat ≤ sizeBv.toNat)
    (hpc1 : s1.pc = mallocAddr) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp) (hx0_1 : s1.readReg64 .x0 = sizeBv)
    (hlr1 : s1.readReg64 Reg.lr = s0.readReg64 Reg.lr)
    (hcs1 : CalleeSavedPreserved s0 s1)
    (hpres01 : AllocCallPreserved s0 s1) (hvm01 : VmPreserved s0 s1) :
    let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
    let xR := (sizeBv.toNat, alignBv.toNat, st)
    SepWP P (s0.readReg64 Reg.lr) s1
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗ Rust.hookFrame s0.sp)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (rustCliAllocBudgetSpecBase M A lim false).post xR s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => (rustCliAllocBudgetSpecBase M A lim false).onOom xR s0 sf) := by
  intro A xR
  have hEvs : rustAllocEvents sizeBv.toNat alignBv.toNat = [.alloc sizeBv.toNat] := by
    unfold rustAllocEvents; simp [hAl16, hAlSz]
  have hEff : mallocngAlignedEffSize alignBv.toNat sizeBv.toNat = sizeBv.toNat := by
    unfold mallocngAlignedEffSize; simp [hAl16]
  have hOkEq :
      decide (sizeBv.toNat ≤ MallocngMaxAllocSize) = decide (MallocngLayoutFit sizeBv alignBv) := by
    simp [MallocngLayoutFit, hEff]
  have hPool1 :
      mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 =
        mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s1 :=
    (mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim st hvm01).symm
  let F := stackFrameAt (s0.sp - 1024#64) 3072
  refine SepWP.call_subroutine_frame (F := F) (x := (sizeBv, st)) hMalloc
    (ret_pc := s0.readReg64 Reg.lr)
    hpc1 hrun1 (by simpa [State.spAligned, hsp1] using hsp_align) hlr1
    (fun R' hsat => ?_)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
    (fun R' sf _ ho => ?_)
  · dsimp only [mallocngBudgetMallocCSpec, F]
    rw [hookFrame_eq_stack1024 s0.sp, hPool1] at hsat
    rw [hsp1]
    have hsat' : s1.mem ⊨
        (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s1 ∗
          stackFrameAt s0.sp mallocngStackBytes) ∗
        (stackFrameAt (s0.sp - 1024#64) 3072 ∗ R') :=
      Satisfies.mono (Entails.of_eq (by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s1 = Ppool
        generalize stackFrameAt s0.sp mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 1024#64) 3072 = Pstk2
        ac_rfl)) hsat
    exact Satisfies.mono (sepConj_mono_left (Entails.pure_right hx0_1 (Entails.refl _))) hsat'
  · refine SepWP.done hpc_f hrun_f
      ⟨fun hsat => ?_, hsp_f.trans hsp1, calleeSavedPreserved_trans hcs1 hcs_f⟩
    dsimp only [mallocngBudgetMallocCSpec, F] at hsat
    dsimp only [rustCliAllocBudgetSpecBase, A, mallocngRustCliAllocBudgetAt, xR]
    rw [hOkEq, hsp1] at hsat
    rw [hEvs, stackAt_eq_hookFrame s0.sp]
    by_cases hFit : MallocngLayoutFit sizeBv alignBv
    · rw [decide_eq_true hFit] at hsat
      simp only [↓reduceIte] at hsat ⊢
      refine Satisfies.mono ?_ hsat
      have hPull :
          ((⌜AllocCallPreserved s1 sf⌝ ∗
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim (M.step (.alloc sizeBv.toNat) st) sf ∗
            stackFrameAt s0.sp mallocngStackBytes ∗
            (⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                (sf.readReg64 .x0).toNat + sizeBv.toNat < 2 ^ 64⌝ ∗
              I.BlockM γ (sf.readReg64 .x0) sizeBv.toNat 16 ∗
              memRegion (sf.readReg64 .x0) sizeBv.toNat)) ∗
           stackFrameAt (s0.sp - 1024#64) 3072) ∗ R =
          ⌜AllocCallPreserved s1 sf⌝ ∗
            (⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                (sf.readReg64 .x0).toNat + sizeBv.toNat < 2 ^ 64⌝ ∗
              (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim (M.step (.alloc sizeBv.toNat) st) sf ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗ stackFrameAt (s0.sp - 1024#64) 3072) ∗
                I.BlockM γ (sf.readReg64 .x0) sizeBv.toNat 16 ∗
                memRegion (sf.readReg64 .x0) sizeBv.toNat ∗ R)) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim
          (M.step (.alloc sizeBv.toNat) st) sf = Ppool
        generalize stackFrameAt s0.sp mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 1024#64) 3072 = Pstk2
        ac_rfl
      rw [hPull, ← hookFrame_eq_stack1024 s0.sp]
      refine Entails.pure_left fun hAcc1 => Entails.pure_left fun ⟨hNe, h16, hFit64⟩ => ?_
      have hNe0 : sf.readReg64 .x0 ≠ 0 := hNe
      simp only [hNe0, Bool.false_eq_true, ↓reduceIte, AllocCostModel.stepEvents_cons,
        AllocCostModel.stepEvents_nil]
      have hAlDvd : alignBv.toNat ∣ (sf.readReg64 .x0).toNat :=
        Nat.dvd_trans (pow2_dvd_16_of_le_16 hPow2 hAl16) h16
      have hMod : (sf.readReg64 .x0).toNat % alignBv.toNat = 0 := Nat.mod_eq_zero_of_dvd hAlDvd
      have hPres0f : AllocCallPreserved s0 sf := allocCallPreserved_trans hpres01 hAcc1
      have hLive := packLiveM_16 (M := M) (I := I) γ hAl16 hNe hAlDvd h16 hFit64 hLayout
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hLive))) ?_
      have hGoalEq :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim (M.step (.alloc sizeBv.toNat) st) sf ∗
            Rust.hookFrame s0.sp ∗
            (⌜(sf.readReg64 .x0).toNat % alignBv.toNat = 0⌝ ∗
              mallocngLiveM M I γ (sf.readReg64 .x0) sizeBv.toNat alignBv.toNat ∗
              memRegion (sf.readReg64 .x0) sizeBv.toNat)) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜(sf.readReg64 .x0).toNat % alignBv.toNat = 0⌝ ∗
              (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim (M.step (.alloc sizeBv.toNat) st) sf ∗
                (Rust.hookFrame s0.sp ∗
                  (mallocngLiveM M I γ (sf.readReg64 .x0) sizeBv.toNat alignBv.toNat ∗
                    (memRegion (sf.readReg64 .x0) sizeBv.toNat ∗ R))))) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim
          (M.step (.alloc sizeBv.toNat) st) sf = Ppool
        generalize Rust.hookFrame s0.sp = Phook
        generalize mallocngLiveM M I γ (sf.readReg64 .x0) sizeBv.toNat alignBv.toNat = Plive
        ac_rfl
      rw [hGoalEq]
      exact Entails.pure_right hPres0f (Entails.pure_right hMod (Entails.refl _))
    · rw [decide_eq_false hFit] at hsat
      simp only [Bool.false_eq_true, ↓reduceIte] at hsat
      have hNull : NullAllowed sizeBv.toNat alignBv.toNat := not_layoutFit_imp_gt_2pow62 hFit
      refine Satisfies.mono ?_ hsat
      have hPull :
          ((⌜AllocCallPreserved s1 sf⌝ ∗
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf ∗
            stackFrameAt s0.sp mallocngStackBytes ∗
            ⌜sf.readReg64 .x0 = 0#64⌝) ∗
           stackFrameAt (s0.sp - 1024#64) 3072) ∗ R =
          ⌜AllocCallPreserved s1 sf⌝ ∗
            (⌜sf.readReg64 .x0 = 0#64⌝ ∗
              (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf ∗
                (stackFrameAt s0.sp mallocngStackBytes ∗ stackFrameAt (s0.sp - 1024#64) 3072) ∗ R)) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf = Ppool
        generalize stackFrameAt s0.sp mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 1024#64) 3072 = Pstk2
        ac_rfl
      rw [hPull, ← hookFrame_eq_stack1024 s0.sp]
      refine Entails.pure_left fun hAcc1 => Entails.pure_left fun hret0 => ?_
      have hret0' : sf.readReg64 .x0 = 0 := hret0
      simp only [hret0', ↓reduceIte]
      have hPres0f : AllocCallPreserved s0 sf := allocCallPreserved_trans hpres01 hAcc1
      have hGoalEq :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf ∗
            Rust.hookFrame s0.sp ∗
            ⌜NullAllowed sizeBv.toNat alignBv.toNat⌝) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜NullAllowed sizeBv.toNat alignBv.toNat⌝ ∗
              (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf ∗
                (Rust.hookFrame s0.sp ∗ R))) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf = Ppool
        generalize Rust.hookFrame s0.sp = Phook
        ac_rfl
      rw [hGoalEq]
      exact Entails.pure_right hPres0f (Entails.pure_right hNull (Entails.refl _))
  · dsimp only [mallocngBudgetMallocCSpec] at ho
    dsimp only [rustCliAllocBudgetSpecBase, A, xR]
    rw [hEvs]
    rw [satisfies_pure_sepConj] at ho ⊢
    obtain ⟨⟨hNotFit, hOom1f⟩, hFR⟩ := ho
    have hNotEvs : ¬ FitsEvents M lim st [.alloc sizeBv.toNat] := fun h => hNotFit h.1
    exact ⟨⟨hNotEvs, oomPreserved_of_allocCallPreserved hpres01 hOom1f⟩, Satisfies.drop_left hFR⟩

private theorem rdlAlloc_budget_epilogue {P : Program}
    {allocAddr mallocAddr posixMemalignAddr : BitVec 64}
    (hCode : hasInstrs P allocAddr (rdlAllocInstrs allocAddr mallocAddr posixMemalignAddr))
    (s0 s3 : State) (w0 q : BitVec 64) (Rest : SepProp)
    (post : State → SepProp → Prop) (oom : State → SepProp)
    (hsp_align : s0.spAligned = true)
    (hpc3 : s3.pc = allocAddr + 0x40#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 32#64)
    (hcs3 : ∀ r ∈ ([.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
      s3.readReg64 r = s0.readReg64 r)
    (hv3 : calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hpost : ∀ sf : State,
      sf.readReg64 .x0 =
        (if ConditionHolds .EQ (subsPState32 (s3.readReg32 .x0) 0#32) then q else 0#64) →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      AllocCallPreserved s3 sf →
      VmPreserved s3 sf →
      post sf (Rust.hookFrame s0.sp ∗ Rest)) :
    SepWP P (s0.readReg64 Reg.lr) s3
      ((((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ q) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
       (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 32#64 - 1024#64) 3040) ∗ Rest)
      post oom := by
  have hf16 := fetch_instr_at 16 hCode
  have hf17 := fetch_instr_at 17 hCode
  have hf18 := fetch_instr_at 18 hCode
  have hf19 := fetch_instr_at 19 hCode
  have hf20 := fetch_instr_at 20 hCode
  have hf21 := fetch_instr_at 21 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp_align
  have hspAl32 : decide (s3.sp &&& 15#64 = 0#64) = true := by
    rw [hsp3]; exact decide_eq_true (beq_iff_eq.mp (spAligned_sub32 hspAl0))
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  have hRepack :
      ((((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ q) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
       (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 32#64 - 1024#64) 3040) ∗ Rest) ⊢
      Rust.hookFrame s0.sp ∗ Rest := by
    rw [hookFrame_eq_stack32_1024 s0.sp, ← sepConj_assoc]
    exact sepConj_mono_left (sepConj_mono_left (pack_stack32 s0.sp w0 q _ _))
  refine SepWP.weaken_pre hRepack ?_
  refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun3]) ?_
  refine hpost _ (by simp [arm64_norm]) (by simp [arm64_norm]) ?_
    (by unfold AllocCallPreserved; simp [arm64_norm])
    (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]))
  refine ⟨by simpa [arm64_norm] using hcs3 .x19 (by simp),
    by simpa [arm64_norm] using hcs3 .x20 (by simp),
    by simpa [arm64_norm] using hcs3 .x21 (by simp),
    by simpa [arm64_norm] using hcs3 .x22 (by simp),
    by simpa [arm64_norm] using hcs3 .x23 (by simp),
    by simpa [arm64_norm] using hcs3 .x24 (by simp),
    by simpa [arm64_norm] using hcs3 .x25 (by simp),
    by simpa [arm64_norm] using hcs3 .x26 (by simp),
    by simpa [arm64_norm] using hcs3 .x27 (by simp),
    by simpa [arm64_norm] using hcs3 .x28 (by simp),
    by simp [arm64_norm], by simpa [calleeSavedVRegs, arm64_norm] using hv3⟩

private theorem rdlAlloc_budget_posix_call {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart : BitVec 64} {cAddrs : MallocngCEntryAddrs}
    {lim : BudgetLimits} (allocAddr : BitVec 64)
    (hCode : hasInstrs P allocAddr
      (rdlAllocInstrs allocAddr cAddrs.malloc cAddrs.posixMemalign))
    (hPosix : subroutine_ok P cAddrs.posixMemalign
      (mallocngBudgetPosixMemalignCSpec M I γ mAddrs tp brkStart lim))
    (sizeBv alignBv w0 : BitVec 64) (st : M.σ) (R : SepProp) (s0 s2 : State)
    (hsp_align : s0.spAligned = true)
    (hLayout : RustLayoutOk sizeBv.toNat alignBv.toNat)
    (hPow2 : IsPow2Align alignBv) (hAlMax : alignBv.toNat ≤ MaxAlignedAllocAlign)
    (hSlow : ¬ (alignBv.toNat ≤ 16 ∧ alignBv.toNat ≤ sizeBv.toNat)) :
    let effAlign := if ConditionHolds .HI (subsPState64 alignBv 8#64) then alignBv else 8#64
    let retPC := allocAddr + 0x40#64
    let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
    let xR := (sizeBv.toNat, alignBv.toNat, st)
    s2.pc = cAddrs.posixMemalign →
    s2.status = .Running →
    s2.sp = s0.sp - 32#64 →
    s2.readReg64 .x0 = s0.sp - 24#64 →
    s2.readReg64 .x1 = effAlign →
    s2.readReg64 .x2 = sizeBv →
    s2.readReg64 Reg.lr = retPC →
    (∀ r ∈ ([.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
      s2.readReg64 r = s0.readReg64 r) →
    calleeSavedVRegs s2 = calleeSavedVRegs s0 →
    AllocCallPreserved s0 s2 →
    VmPreserved s0 s2 →
    SepWP P (s0.readReg64 Reg.lr) s2
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
        stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 ∗
        ((s0.sp - 32#64) ↦₆₄ w0) ∗
        ((s0.sp - 24#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (rustCliAllocBudgetSpecBase M A lim false).post xR s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => (rustCliAllocBudgetSpecBase M A lim false).onOom xR s0 sf) := by
  intro effAlign retPC A xR hpc2 hrun2 hsp2 hx0_2 hx1_2 hx2_2 hlr2 hcs2 hv2 hpres02 hvm02
  have hEvs :
      rustAllocEvents sizeBv.toNat alignBv.toNat =
        [.aligned (max alignBv.toNat 8) sizeBv.toNat] := by
    unfold rustAllocEvents; simp [hSlow]
  obtain ⟨hEffNat, hEffGe8, hEffMax, hPowEff, hEffMax16, _hEffSz, hPosixOk, hPosixRet⟩ :=
    effAlign_props (size := sizeBv) hPow2 hAlMax
  change effAlign.toNat = max alignBv.toNat 8 at hEffNat
  change 8 ≤ effAlign.toNat at hEffGe8
  change effAlign.toNat ≤ MaxAlignedAllocAlign at hEffMax
  change IsPow2Align effAlign at hPowEff
  change max effAlign.toNat 16 = max alignBv.toNat 16 at hEffMax16
  change mallocngPosixMemalignOk effAlign sizeBv = _ at hPosixOk
  change mallocngPosixMemalignRet effAlign sizeBv = _ at hPosixRet
  have hEffAlOk : alignedAllocAlignOk effAlign = true := isPow2Align_alignedAllocOk hPowEff
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp_align
  have hspAl32b : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true := spAligned_sub32 hspAl0
  let FrameF := stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 ∗
    ((s0.sp - 32#64) ↦₆₄ w0) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)
  let xP := (s0.sp - 24#64, effAlign, sizeBv, st)
  refine SepWP.call_subroutine_frame (F := FrameF) (x := xP) hPosix (ret_pc := retPC)
    hpc2 hrun2 (by simpa [State.spAligned, hsp2] using hspAl32b) hlr2
    (fun R' hsat => ?_)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun s3 hpc3 hrun3 hsp3 hcs3 => ?_)
    (fun R' sf _ ho => ?_)
  · dsimp only [mallocngBudgetPosixMemalignCSpec, xP, FrameF]
    have hPool2 :
        mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 =
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s2 :=
      (mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim st hvm02).symm
    rw [hPool2] at hsat
    rw [hsp2]
    have hsat' : s2.mem ⊨
        (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s2 ∗
          ((s0.sp - 24#64) ↦₆₄ 0#64) ∗
          stackFrameAt (s0.sp - 32#64) mallocngStackBytes) ∗
        ((stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 ∗
          ((s0.sp - 32#64) ↦₆₄ w0) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗ R') :=
      Satisfies.mono (Entails.of_eq (by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s2 = Ppool
        generalize stackFrameAt (s0.sp - 32#64) mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 = Pstk2
        ac_rfl)) hsat
    refine Satisfies.mono (sepConj_mono_left ?_) hsat'
    refine Entails.pure_right ⟨hx0_2, hx1_2, hx2_2, hEffMax⟩ ?_
    exact sepConj_mono_right (sepConj_mono_left ((IsBlock.pointsTo64 (s0.sp - 24#64) 0#64).entails_memRegion))
  · have hcs3_regs : ∀ r ∈ ([.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
        s3.readReg64 r = s0.readReg64 r := by
      obtain ⟨d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, _, _⟩ := hcs3
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact d19.trans (hcs2 .x19 (by simp))
      · exact d20.trans (hcs2 .x20 (by simp))
      · exact d21.trans (hcs2 .x21 (by simp))
      · exact d22.trans (hcs2 .x22 (by simp))
      · exact d23.trans (hcs2 .x23 (by simp))
      · exact d24.trans (hcs2 .x24 (by simp))
      · exact d25.trans (hcs2 .x25 (by simp))
      · exact d26.trans (hcs2 .x26 (by simp))
      · exact d27.trans (hcs2 .x27 (by simp))
      · exact d28.trans (hcs2 .x28 (by simp))
    have hv3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hcs3.2.2.2.2.2.2.2.2.2.2.2.trans hv2
    have hsp3' : s3.sp = s0.sp - 32#64 := hsp3.trans hsp2
    dsimp only [mallocngBudgetPosixMemalignCSpec, xP]
    rw [hPosixOk, hPosixRet, hEffMax16, hEffNat, hsp2]
    simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hAcc23, hw0_3⟩
    have hpres03 : AllocCallPreserved s0 s3 := allocCallPreserved_trans hpres02 hAcc23
    by_cases hFit : MallocngLayoutFit sizeBv alignBv
    · rw [decide_eq_true hFit]
      simp only [hFit, ↓reduceIte, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc] at hw0_3 ⊢
      apply SepWP.exists_elim; intro q
      let stOk := M.step (.aligned (max alignBv.toNat 8) sizeBv.toNat) st
      have hPullQ :
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 ∗
            stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
            ⌜q ≠ 0#64 ∧ max alignBv.toNat 16 ∣ q.toNat ∧ q.toNat + sizeBv.toNat < 2 ^ 64⌝ ∗
            ((s0.sp - 24#64) ↦₆₄ q) ∗
            I.BlockM γ q sizeBv.toNat (max alignBv.toNat 16) ∗
            memRegion q sizeBv.toNat ∗ FrameF =
          ⌜q ≠ 0#64 ∧ max alignBv.toNat 16 ∣ q.toNat ∧ q.toNat + sizeBv.toNat < 2 ^ 64⌝ ∗
            (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 ∗
              stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
              ((s0.sp - 24#64) ↦₆₄ q) ∗
              I.BlockM γ q sizeBv.toNat (max alignBv.toNat 16) ∗
              memRegion q sizeBv.toNat ∗ FrameF) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 = Ppool
        generalize stackFrameAt (s0.sp - 32#64) mallocngStackBytes = Pstk1
        ac_rfl
      rw [hPullQ]
      apply SepWP.pure_elim; rintro ⟨hqNe, hqDvd, hqFit64⟩
      let RestOk :=
        mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 ∗
          I.BlockM γ q sizeBv.toNat (max alignBv.toNat 16) ∗
          memRegion q sizeBv.toNat
      have hCollapseOk :
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 ∗
            (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
              (((s0.sp - 24#64) ↦₆₄ q) ∗
                (I.BlockM γ q sizeBv.toNat (max alignBv.toNat 16) ∗
                  (memRegion q sizeBv.toNat ∗ FrameF)))) ⊢
          ((((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ q) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
           (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
            stackFrameAt (s0.sp - 32#64 - 1024#64) 3040) ∗ RestOk) := by
        dsimp only [FrameF, RestOk]
        exact Entails.of_eq (by
          generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 = Ppool
          generalize stackFrameAt (s0.sp - 32#64) mallocngStackBytes = Pstk1
          generalize stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 = Pstk2
          ac_rfl)
      refine SepWP.weaken_pre hCollapseOk ?_
      refine rdlAlloc_budget_epilogue hCode s0 s3 w0 q RestOk _ _ hsp_align
        hpc3 hrun3 hsp3' hcs3_regs hv3 fun sf hx0f hspf hcsf hprocf hvm3f => ?_
      refine ⟨fun hsat => ?_, hspf, hcsf⟩
      have hEqTrue : ConditionHolds .EQ (subsPState32 (s3.readReg32 .x0) 0#32) = true := by
        rw [hw0_3]; exact (cond_eq_subs32_iff_eq 0#32 0#32).mpr rfl
      have hx0_q : sf.readReg64 .x0 = q := by rw [hx0f, hEqTrue]; rfl
      have hqNe0 : q ≠ 0 := hqNe
      have hAlDvd : alignBv.toNat ∣ q.toNat := Nat.dvd_trans (pow2_dvd_max16 hPow2) hqDvd
      have h16Dvd : 16 ∣ q.toNat := Nat.dvd_trans (sixteen_dvd_max16_of_layoutOk hLayout) hqDvd
      have hMod : q.toNat % alignBv.toNat = 0 := Nat.mod_eq_zero_of_dvd hAlDvd
      have hPres0f : AllocCallPreserved s0 sf := allocCallPreserved_trans hpres03 hprocf
      have hPoolSf :
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk s3 =
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk sf :=
        (mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim stOk hvm3f).symm
      dsimp only [rustCliAllocBudgetSpecBase, A, mallocngRustCliAllocBudgetAt, xR, RestOk] at hsat ⊢
      rw [hEvs, stackAt_eq_hookFrame s0.sp]
      simp only [hx0_q, hqNe0, ↓reduceIte, AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
      change sf.mem ⊨
        (⌜AllocCallPreserved s0 sf⌝ ∗
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk sf ∗
          Rust.hookFrame s0.sp ∗
          (⌜q.toNat % alignBv.toNat = 0⌝ ∗
            mallocngLiveM M I γ q sizeBv.toNat alignBv.toNat ∗
            memRegion q sizeBv.toNat)) ∗ R
      rw [hPoolSf] at hsat
      refine Satisfies.mono (sepConj_mono_left ?_) hsat
      have hLive := packLiveM (M := M) (I := I) γ hqNe hAlDvd h16Dvd hqFit64 hLayout
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hLive))) ?_
      have hGoalEq :
          ⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk sf ∗
            Rust.hookFrame s0.sp ∗
            (⌜q.toNat % alignBv.toNat = 0⌝ ∗
              mallocngLiveM M I γ q sizeBv.toNat alignBv.toNat ∗
              memRegion q sizeBv.toNat) =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜q.toNat % alignBv.toNat = 0⌝ ∗
              (Rust.hookFrame s0.sp ∗
                (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk sf ∗
                  (mallocngLiveM M I γ q sizeBv.toNat alignBv.toNat ∗
                    memRegion q sizeBv.toNat)))) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk sf = Ppool
        generalize Rust.hookFrame s0.sp = Phook
        generalize mallocngLiveM M I γ q sizeBv.toNat alignBv.toNat = Plive
        ac_rfl
      rw [hGoalEq]
      exact Entails.pure_right hPres0f (Entails.pure_right hMod (Entails.refl _))
    · rw [decide_eq_false hFit]
      simp only [hFit, Bool.false_eq_true, ↓reduceIte] at hw0_3 ⊢
      have hNull : NullAllowed sizeBv.toNat alignBv.toNat := not_layoutFit_imp_gt_2pow62 hFit
      apply SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (memRegion8_entails_pointsTo64 (s0.sp - 24#64)))))
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro q
      let RestFail := mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s3
      have hCollapseFail :
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s3 ∗
            (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
              (((s0.sp - 24#64) ↦₆₄ q) ∗ FrameF)) ⊢
          ((((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ q) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)) ∗
           (stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
            stackFrameAt (s0.sp - 32#64 - 1024#64) 3040) ∗ RestFail) := by
        dsimp only [FrameF, RestFail]
        exact Entails.of_eq (by
          generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s3 = Ppool
          generalize stackFrameAt (s0.sp - 32#64) mallocngStackBytes = Pstk1
          generalize stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 = Pstk2
          ac_rfl)
      refine SepWP.weaken_pre hCollapseFail ?_
      refine rdlAlloc_budget_epilogue hCode s0 s3 w0 q RestFail _ _ hsp_align
        hpc3 hrun3 hsp3' hcs3_regs hv3 fun sf hx0f hspf hcsf hprocf hvm3f => ?_
      refine ⟨fun hsat => ?_, hspf, hcsf⟩
      have hEqFalse : ConditionHolds .EQ (subsPState32 (s3.readReg32 .x0) 0#32) = false := by
        rw [hw0_3]; exact Bool.eq_false_iff.mpr fun h =>
          absurd ((cond_eq_subs32_iff_eq 12#32 0#32).mp h) (by decide)
      have hx0_0 : sf.readReg64 .x0 = 0 := by rw [hx0f, hEqFalse]; rfl
      have hPres0f : AllocCallPreserved s0 sf := allocCallPreserved_trans hpres03 hprocf
      have hPoolSf :
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s3 =
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf :=
        (mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim st hvm3f).symm
      dsimp only [rustCliAllocBudgetSpecBase, A, mallocngRustCliAllocBudgetAt, xR, RestFail] at hsat ⊢
      rw [stackAt_eq_hookFrame s0.sp]
      simp only [hx0_0, ↓reduceIte]
      rw [hPoolSf] at hsat
      refine Satisfies.mono (sepConj_mono_left ?_) hsat
      have hGoalEq :
          ⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf ∗
            Rust.hookFrame s0.sp ∗
            ⌜NullAllowed sizeBv.toNat alignBv.toNat⌝ =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜NullAllowed sizeBv.toNat alignBv.toNat⌝ ∗
              (Rust.hookFrame s0.sp ∗
                mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf)) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf = Ppool
        generalize Rust.hookFrame s0.sp = Phook
        ac_rfl
      rw [hGoalEq]
      exact Entails.pure_right hPres0f (Entails.pure_right hNull (Entails.refl _))
  · dsimp only [mallocngBudgetPosixMemalignCSpec, xP] at ho
    dsimp only [rustCliAllocBudgetSpecBase, A, xR]
    rw [hEvs]
    rw [satisfies_pure_sepConj] at ho ⊢
    obtain ⟨⟨hNotPosix, hOom2f⟩, hFR⟩ := ho
    have hNotEvs : ¬ FitsEvents M lim st [.aligned (max alignBv.toNat 8) sizeBv.toNat] := by
      intro hFitEvs
      refine hNotPosix ⟨hEffGe8, hEffAlOk, ?_⟩
      rw [hEffNat]
      exact hFitEvs.1
    exact ⟨⟨hNotEvs, oomPreserved_of_allocCallPreserved hpres02 hOom2f⟩, Satisfies.drop_left hFR⟩

private theorem rdlAlloc_budget_posix_args {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart : BitVec 64} {cAddrs : MallocngCEntryAddrs}
    {lim : BudgetLimits} (allocAddr : BitVec 64)
    (hCode : hasInstrs P allocAddr
      (rdlAllocInstrs allocAddr cAddrs.malloc cAddrs.posixMemalign))
    (hPosix : subroutine_ok P cAddrs.posixMemalign
      (mallocngBudgetPosixMemalignCSpec M I γ mAddrs tp brkStart lim))
    (sizeBv alignBv w0 w1 : BitVec 64) (st : M.σ) (R : SepProp) (s0 sm : State)
    (hsp_align : s0.spAligned = true)
    (hLayout : RustLayoutOk sizeBv.toNat alignBv.toNat)
    (hPow2 : IsPow2Align alignBv) (hAlMax : alignBv.toNat ≤ MaxAlignedAllocAlign)
    (hSlow : ¬ (alignBv.toNat ≤ 16 ∧ alignBv.toNat ≤ sizeBv.toNat))
    (hpcm : sm.pc = allocAddr + 0x2c#64) (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 32#64)
    (hpstm : sm.pstate = subsPState64 alignBv 8#64)
    (hx1_m : sm.readReg64 .x1 = alignBv) (hx2_m : sm.readReg64 .x2 = sizeBv)
    (hcsm : ∀ r ∈ ([.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg),
      sm.readReg64 r = s0.readReg64 r)
    (hvm : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hpres0m : AllocCallPreserved s0 sm) (hvm0m : VmPreserved s0 sm) :
    let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
    let xR := (sizeBv.toNat, alignBv.toNat, st)
    SepWP P (s0.readReg64 Reg.lr) sm
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
        stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 ∗
        ((s0.sp - 32#64) ↦₆₄ w0) ∗
        ((s0.sp - 24#64) ↦₆₄ w1) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (rustCliAllocBudgetSpecBase M A lim false).post xR s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => (rustCliAllocBudgetSpecBase M A lim false).onOom xR s0 sf) := by
  intro A xR
  have hf11 := fetch_instr_at 11 hCode
  have hf12 := fetch_instr_at 12 hCode
  have hf13 := fetch_instr_at 13 hCode
  have hf14 := fetch_instr_at 14 hCode
  have hf15 := fetch_instr_at 15 hCode
  have ha_sp8 : sm.sp + 8#64 = s0.sp - 24#64 := by rw [hspm]; bv_omega
  wp_step; wp_step; wp_step; wp_str64 hf14 m hm; wp_step
  have hm0 : m.perm = sm.mem.perm := by simpa using hm
  exact rdlAlloc_budget_posix_call hS γ allocAddr hCode hPosix
    sizeBv alignBv w0 st R s0 _
    hsp_align hLayout hPow2 hAlMax hSlow
    (by simp only [arm64_norm]; bv_omega)
    (by simp [arm64_norm, hrunm])
    (by simp [arm64_norm, hspm])
    (by simp only [arm64_norm])
    (by simp [arm64_norm])
    (by simp only [arm64_norm, hx2_m])
    (by simp only [arm64_norm])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa only [arm64_norm] using hcsm _ (by simp))
    (by simpa only [calleeSavedVRegs, arm64_norm] using hvm)
    (allocCallPreserved_trans hpres0m
      (allocCallPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])))
    (vmPreserved_trans hvm0m
      (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm, hm0])))

private theorem rdlAlloc_budget_posix_path {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart : BitVec 64} {cAddrs : MallocngCEntryAddrs}
    {lim : BudgetLimits} (allocAddr : BitVec 64)
    (hCode : hasInstrs P allocAddr
      (rdlAllocInstrs allocAddr cAddrs.malloc cAddrs.posixMemalign))
    (hPosix : subroutine_ok P cAddrs.posixMemalign
      (mallocngBudgetPosixMemalignCSpec M I γ mAddrs tp brkStart lim))
    (sizeBv alignBv : BitVec 64) (st : M.σ) (R : SepProp) (s0 s1 : State)
    (hsp_align : s0.spAligned = true)
    (hLayout : RustLayoutOk sizeBv.toNat alignBv.toNat)
    (hPow2 : IsPow2Align alignBv) (hAlMax : alignBv.toNat ≤ MaxAlignedAllocAlign)
    (hSlow : ¬ (alignBv.toNat ≤ 16 ∧ alignBv.toNat ≤ sizeBv.toNat))
    (hpc1 : s1.pc = allocAddr + 0x1c#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp)
    (hx1_1 : s1.readReg64 .x1 = alignBv) (hx2_1 : s1.readReg64 .x2 = sizeBv)
    (hlr1 : s1.readReg64 Reg.lr = s0.readReg64 Reg.lr)
    (hcs1 : CalleeSavedPreserved s0 s1)
    (hpres01 : AllocCallPreserved s0 s1) (hvm01 : VmPreserved s0 s1) :
    let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
    let xR := (sizeBv.toNat, alignBv.toNat, st)
    SepWP P (s0.readReg64 Reg.lr) s1
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗ Rust.hookFrame s0.sp)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (rustCliAllocBudgetSpecBase M A lim false).post xR s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => (rustCliAllocBudgetSpecBase M A lim false).onOom xR s0 sf) := by
  intro A xR
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp_align
  have hspAl32b : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true := spAligned_sub32 hspAl0
  have hspAl32 : decide ((s0.sp - 32#64) &&& 15#64 = 0#64) = true :=
    decide_eq_true (beq_iff_eq.mp hspAl32b)
  have hUnpack :
      mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗ Rust.hookFrame s0.sp =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
          stackFrameAt (s0.sp - 32#64) mallocngStackBytes ∗
          stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 ∗
          ((s0.sp - 32#64) ↦₆₄ w0) ∗ ((s0.sp - 24#64) ↦₆₄ w1) ∗
          ((s0.sp - 16#64) ↦₆₄ w2) ∗ ((s0.sp - 8#64) ↦₆₄ w3)) := by
    rw [hookFrame_eq_stack32_1024 s0.sp, stackFrameAt32_eq s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine congrArg SepProp.sepExists (funext fun _ =>
      congrArg SepProp.sepExists (funext fun _ =>
      congrArg SepProp.sepExists (funext fun _ =>
      congrArg SepProp.sepExists (funext fun _ => by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 = Ppool
        generalize stackFrameAt (s0.sp - 32#64) mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 32#64 - 1024#64) 3040 = Pstk2
        ac_rfl))))
  rw [hUnpack]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  have hf7 := fetch_instr_at 7 hCode
  have hf8 := fetch_instr_at 8 hCode
  have hf9 := fetch_instr_at 9 hCode
  have hf10 := fetch_instr_at 10 hCode
  have ha_sp : s1.sp + (-32#64) = s0.sp - 32#64 := by rw [hsp1]; bv_omega
  obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv⟩ := hcs1
  have _ : s1.readReg64 (.gpr 29#5) = s0.readReg64 .x29 := c29
  wp_step; wp_stp64 hf8 m hm; wp_step; wp_step
  have hm0 : m.perm = s1.mem.perm := by simpa using hm
  exact rdlAlloc_budget_posix_args hS γ allocAddr hCode hPosix
    sizeBv alignBv w0 w1 st R s0 _
    hsp_align hLayout hPow2 hAlMax hSlow
    (by simp [arm64_norm])
    (by simp [arm64_norm, hrun1])
    (by simp [arm64_norm])
    (by simp [arm64_norm])
    (by simp [arm64_norm, hx1_1])
    (by simp [arm64_norm, hx2_1])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa only [arm64_norm] using c19
      · simpa only [arm64_norm] using c20
      · simpa only [arm64_norm] using c21
      · simpa only [arm64_norm] using c22
      · simpa only [arm64_norm] using c23
      · simpa only [arm64_norm] using c24
      · simpa only [arm64_norm] using c25
      · simpa only [arm64_norm] using c26
      · simpa only [arm64_norm] using c27
      · simpa only [arm64_norm] using c28)
    (by simpa only [calleeSavedVRegs, arm64_norm] using cv)
    (allocCallPreserved_trans hpres01
      (allocCallPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])))
    (vmPreserved_trans hvm01
      (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm, hm0])))

/-- Placed `rustc 1.98.1` `__rustc::__rdl_alloc` (`22` instructions: `rdlAllocInstrs`) satisfies
    `rustCliAllocBudgetSpec` (`zeroed = false`) over `mallocngRustCliAllocBudgetAt`. -/
theorem rdlAlloc_budget_placed_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart : BitVec 64}
    {cAddrs : MallocngCEntryAddrs} {callocAddr : BitVec 64}
    (allocAddr : BitVec 64) (lim : BudgetLimits)
    (hCode : hasInstrs P allocAddr
      (rdlAllocInstrs allocAddr cAddrs.malloc cAddrs.posixMemalign))
    (hC : MallocngProgBudgetCContracts M I γ mAddrs tp brkStart P cAddrs callocAddr) :
    subroutine_ok P allocAddr
      (rustCliAllocBudgetSpecBase M (mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart) lim false) := by
  let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
  apply subroutine_ok_of_sepWP_init
  rintro ⟨size, align, st⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [rustCliAllocBudgetSpecBase, A, mallocngRustCliAllocBudgetAt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hLayout⟩, hpre⟩ := hpre
  let sizeBv := s0.readReg64 .x0
  let alignBv := s0.readReg64 .x1
  have hx0_bv : s0.readReg64 .x0 = sizeBv := rfl
  have hx1_bv : s0.readReg64 .x1 = alignBv := rfl
  change sizeBv.toNat = size at hx0
  change alignBv.toNat = align at hx1
  subst hx0; subst hx1
  have ⟨⟨_hSzPos, ⟨k, hk⟩, _hSum63⟩, hAlMax⟩ := hLayout
  have hPow2 : IsPow2Align alignBv := isPow2Align_of_toNat_pow2 hk
  have hAlMax' : alignBv.toNat ≤ MaxAlignedAllocAlign := hAlMax
  rw [stackAt_eq_hookFrame s0.sp] at hpre
  refine ⟨_, hpre, ?_⟩
  have hf0 := fetch_instr_at0 hCode
  have hf1 := fetch_instr_at 1 hCode
  have hf2 := fetch_instr_at 2 hCode
  have hf3 := fetch_instr_at 3 hCode
  have hf4 := fetch_instr_at 4 hCode
  have hf5 := fetch_instr_at 5 hCode
  have hf6 := fetch_instr_at 6 hCode
  wp_step; wp_step
  by_cases hAl16 : alignBv.toNat ≤ 16
  · have hHi1 : ConditionHolds .HI (subsPState64 alignBv 16#64) = false :=
      Bool.eq_false_iff.mpr fun h => by
        have := (VerifiedLibraries.Mallocng.Proofs.RdlAllocH.cond_hi_subs64_iff_lt alignBv 16#64).mp h
        change 16 < alignBv.toNat at this; omega
    wp_step; wp_step
    by_cases hAlSz : alignBv.toNat ≤ sizeBv.toNat
    · have hHi2 : ConditionHolds .HI (subsPState64 alignBv sizeBv) = false :=
        Bool.eq_false_iff.mpr fun h => by
          have := (VerifiedLibraries.Mallocng.Proofs.RdlAllocH.cond_hi_subs64_iff_lt alignBv sizeBv).mp h
          omega
      wp_step; wp_step; wp_step
      exact rdlAlloc_budget_fast_path hS γ (hC.malloc_ok lim)
        sizeBv alignBv st R s0 _
        hsp_align hLayout hPow2 hAl16 hAlSz
        (by simp only [State.pc_setPC]; bv_omega)
        (by simp [arm64_norm, hrun])
        (by simp [arm64_norm])
        (by simp [arm64_norm])
        (by simp [arm64_norm])
        (by unfold CalleeSavedPreserved; simp [arm64_norm, calleeSavedVRegs])
        (by unfold AllocCallPreserved; simp [arm64_norm])
        (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]))
    · have hHi2 : ConditionHolds .HI (subsPState64 alignBv sizeBv) = true :=
        (VerifiedLibraries.Mallocng.Proofs.RdlAllocH.cond_hi_subs64_iff_lt alignBv sizeBv).mpr (by omega)
      wp_step
      exact rdlAlloc_budget_posix_path hS γ allocAddr hCode (hC.posixMemalign_ok lim)
        sizeBv alignBv st R s0 _
        hsp_align hLayout hPow2 hAlMax' (fun h => hAlSz h.2)
        (by simp only [State.pc_setPC])
        (by simp [arm64_norm, hrun])
        (by simp [arm64_norm])
        (by simp [arm64_norm, hx1_bv])
        (by simp [arm64_norm])
        (by simp [arm64_norm])
        (by unfold CalleeSavedPreserved; simp [arm64_norm, calleeSavedVRegs])
        (by unfold AllocCallPreserved; simp [arm64_norm])
        (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]))
  · have hHi1 : ConditionHolds .HI (subsPState64 alignBv 16#64) = true :=
      (VerifiedLibraries.Mallocng.Proofs.RdlAllocH.cond_hi_subs64_iff_lt alignBv 16#64).mpr
        (by change 16 < alignBv.toNat; omega)
    wp_step
    exact rdlAlloc_budget_posix_path hS γ allocAddr hCode (hC.posixMemalign_ok lim)
      sizeBv alignBv st R s0 _
      hsp_align hLayout hPow2 hAlMax' (fun h => hAl16 h.1)
      (by simp only [State.pc_setPC])
      (by simp [arm64_norm, hrun])
      (by simp [arm64_norm])
      (by simp [arm64_norm, hx1_bv])
      (by simp [arm64_norm])
      (by simp [arm64_norm])
      (by unfold CalleeSavedPreserved; simp [arm64_norm, calleeSavedVRegs])
      (by unfold AllocCallPreserved; simp [arm64_norm])
      (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]))

/-! ## Placed `__rustc::__rdl_realloc` -/

private theorem rdlRealloc_budget_epilogue {P : Program}
    {reallocAddr cReallocAddr posixMemalignAddr memcpyAddr freeAddr : BitVec 64}
    (hCode : hasInstrs P reallocAddr
      (rdlReallocInstrs reallocAddr cReallocAddr posixMemalignAddr memcpyAddr freeAddr))
    (s0 s : State) (w0 w1 : BitVec 64) (Q : SepProp)
    (post : State → SepProp → Prop) (oom : State → SepProp)
    (hsp_align : s0.spAligned = true)
    (hpc : s.pc = reallocAddr + 0x98#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 64#64)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hcs_v : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hpost : ∀ sf : State,
      sf.readReg64 .x0 = s.readReg64 .x0 →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      AllocCallPreserved s sf →
      VmPreserved s sf →
      post sf (Rust.hookFrame s0.sp ∗ Q)) :
    SepWP P (s0.readReg64 Reg.lr) s
      ((((s0.sp - 64#64) ↦₆₄ w0) ∗ ((s0.sp - 56#64) ↦₆₄ w1) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
       (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 64#64 - 1024#64) 3008) ∗ Q)
      post oom := by
  have hsp_s : decide (s.sp &&& 15#64 = 0#64) = true := by
    rw [hsp]; exact spAligned_sub64 hsp_align
  have hf38 := fetch_instr_at 38 (off := 0x98#64) hCode
  have hf39 := fetch_instr_at 39 (off := 0x9c#64) hCode
  have hf40 := fetch_instr_at 40 (off := 0xa0#64) hCode
  have hf41 := fetch_instr_at 41 (off := 0xa4#64) hCode
  have hf42 := fetch_instr_at 42 (off := 0xa8#64) hCode
  wp_step; wp_step; wp_step; wp_step; wp_step
  rw [← sepConj_assoc]
  refine SepWP.weaken_pre (sepConj_mono_left (repack_hookFrame_64 s0.sp w0 w1 _ _ _ _ _ _)) ?_
  refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) ?_
  refine hpost _ (by simp [arm64_norm]) (by simp [arm64_norm]) ?_ ?_ ?_
  · unfold CalleeSavedPreserved
    simp [arm64_norm, hx23, hx24, hx25, hx26, hx27, hx28, hcs_v]
  · unfold AllocCallPreserved
    simp [arm64_norm]
  · exact vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])

private theorem rdlRealloc_budget_pathA {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart : BitVec 64}
    {cAddrs : MallocngCEntryAddrs} {callocAddr : BitVec 64}
    {reallocAddr memcpyAddr : BitVec 64} {lim : BudgetLimits}
    (hCode : hasInstrs P reallocAddr
      (rdlReallocInstrs reallocAddr cAddrs.realloc cAddrs.posixMemalign memcpyAddr cAddrs.free))
    (hC : MallocngProgBudgetCContracts M I γ mAddrs tp brkStart P cAddrs callocAddr)
    (p alignBv newBv : BitVec 64) (old align new : Nat) (bs : List (BitVec 8))
    (st : M.σ) (sv0 sv1 : BitVec 64) (R : SepProp) (s0 s : State)
    (hsp_align : s0.spAligned = true)
    (hAlignNat : alignBv.toNat = align) (hNewNat : newBv.toNat = new)
    (hLayoutNew : RustLayoutOk new align) (hLayoutOld : RustLayoutOk old align)
    (hpAlDvd : align ∣ p.toNat)
    (hPow2 : IsPow2Align alignBv) (hAl16 : align ≤ 16) (hAlNew : align ≤ new)
    (hpNe : p ≠ 0#64) (hp16 : 16 ∣ p.toNat) (hp64 : p.toNat + old < 2 ^ 64)
    (hbsOld : bs.length ≤ old) (hbsNew : bs.length ≤ new)
    (hpc : s.pc = reallocAddr + 0x2c#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 64#64)
    (hx0 : s.readReg64 .x0 = p) (hx19 : s.readReg64 .x19 = newBv)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23) (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hcs_v : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hPres : AllocCallPreserved s0 s) (hVm : VmPreserved s0 s) :
    let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
    let spec := rustCliReallocBudgetSpecBase M A lim
    let x := (p, old, align, new, bs, st)
    SepWP P (s0.readReg64 Reg.lr) s
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
       I.BlockM γ p old (max align 16) ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ sv1) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
        (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
         stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => spec.onOom x s0 sf) := by
  intro A spec x
  have hEvs : rustReallocEvents old new align = [.realloc align old new] := by
    unfold rustReallocEvents
    have hc : (align ≤ 16 ∧ align ≤ new) := ⟨hAl16, hAlNew⟩
    simp [hc]
  have hsp_s : decide (s.sp &&& 15#64 = 0#64) = true := by
    rw [hsp]; exact spAligned_sub64 hsp_align
  have hf11 := fetch_instr_at 11 (off := 0x2c#64) hCode
  have hf12 := fetch_instr_at 12 (off := 0x30#64) hCode
  have hf13 := fetch_instr_at 13 (off := 0x34#64) hCode
  have hf14 := fetch_instr_at 14 (off := 0x38#64) hCode
  have hf15 := fetch_instr_at 15 (off := 0x3c#64) hCode
  have hf16 := fetch_instr_at 16 (off := 0x40#64) hCode
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  have hTake : bs.take new = bs := List.take_of_length_le hbsNew
  have hPreShape :
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
       I.BlockM γ p old (max align 16) ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ sv1) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
        (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
         stackFrameAt (s0.sp - 64#64 - 1024#64) 3008))) ⊢
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
       I.BlockM γ p old (max align 16) ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       stackFrameAt s0.sp mallocngStackBytes) ∗
      stackFrameAt (s0.sp - 1024#64) 3072 := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (repack_stack64_to_1024 s0.sp sv0 sv1 _ _ _ _ _ _))))) ?_
    exact Entails.of_eq (by
      generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 = Ppool
      generalize stackFrameAt s0.sp mallocngStackBytes = Pstk1
      generalize stackFrameAt (s0.sp - 1024#64) 3072 = Pstk2
      ac_rfl)
  refine SepWP.weaken_pre hPreShape ?_
  refine SepWP.call_subroutine_frame (hC.realloc_some_ok lim)
    (x := (p, newBv, old, align, bs, st))
    (F := stackFrameAt (s0.sp - 1024#64) 3072)
    (ret_pc := s0.readReg64 Reg.lr)
    (by simp [arm64_norm]; bv_omega)
    (by simp [arm64_norm, hrun])
    (by
      have hsp_eq : (s.sp + 64#64) = s0.sp := by rw [hsp]; bv_omega
      simpa [State.spAligned, arm64_norm, hsp_eq] using hsp_align)
    (by simp [arm64_norm])
    ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    ?_ ?_
  · intro R' hsat
    dsimp only [mallocngBudgetReallocSomeCSpec]
    conv => pattern (stackFrameAt _ mallocngStackBytes); arg 1; simp only [arm64_norm]
    conv =>
      pattern (mallocngBudgetPoolAt _ _ _ _ _ _ _ _ _)
      simp only [mallocngBudgetPoolAt_setPC, mallocngBudgetPoolAt_writeReg64]
      rw [mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim st hVm]
    rw [sepConj_assoc _ _ R'] at hsat
    refine Satisfies.mono (sepConj_mono_left ?_) hsat
    exact Entails.pure_right
      ⟨by simpa [arm64_norm] using hx0,
       by simp [arm64_norm],
       hpNe, hp16, hp64, hbsOld⟩
      (Entails.of_eq (by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 = Ppool
        generalize stackFrameAt s0.sp mallocngStackBytes = Pstk1
        ac_rfl))
  · intro sf hpc_f hrun_f hsp_f hcs_f
    have hsp_sf : sf.sp = s0.sp := by simpa [arm64_norm] using hsp_f
    have hcs_s0 : CalleeSavedPreserved s0 sf := by
      refine calleeSavedPreserved_trans ?_ hcs_f
      unfold CalleeSavedPreserved
      simp [arm64_norm, hx23, hx24, hx25, hx26, hx27, hx28, hcs_v]
    refine SepWP.done hpc_f hrun_f ⟨fun hsat => ?_, hsp_sf, hcs_s0⟩
    dsimp only [mallocngBudgetReallocSomeCSpec] at hsat
    dsimp only [spec, x, rustCliReallocBudgetSpecBase, A, mallocngRustCliAllocBudgetAt]
    rw [hNewNat] at hsat
    rw [hEvs, stackAt_eq_hookFrame s0.sp]
    conv at hsat => pattern (stackFrameAt _ mallocngStackBytes); arg 1; simp only [arm64_norm]
    by_cases hMax : new ≤ MallocngMaxAllocSize
    · have hOkT : decide (new ≤ MallocngMaxAllocSize) = true := decide_eq_true hMax
      rw [hOkT] at hsat
      simp only [↓reduceIte, hTake, sepConj_assoc] at hsat
      rw [satisfies_pure_sepConj] at hsat
      obtain ⟨hAcc, hsat⟩ := hsat
      have hPresSf : AllocCallPreserved s0 sf :=
        allocCallPreserved_trans hPres (allocCallPreserved_of_fields_eq
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) hAcc)
      let stOk := M.step (.realloc align old new) st
      have hPull :
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk sf ∗
            stackFrameAt s0.sp mallocngStackBytes ∗
            ⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
                (sf.readReg64 .x0).toNat + new < 2 ^ 64 ∧ bs.length ≤ new⌝ ∗
            I.BlockM γ (sf.readReg64 .x0) new (max align 16) ∗
            (sf.readReg64 .x0 ↦ₛ bs) ∗
            memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length) ∗
            stackFrameAt (s0.sp - 1024#64) 3072 ∗ R =
          ⌜sf.readReg64 .x0 ≠ 0#64 ∧ 16 ∣ (sf.readReg64 .x0).toNat ∧
              (sf.readReg64 .x0).toNat + new < 2 ^ 64 ∧ bs.length ≤ new⌝ ∗
            ((mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk sf ∗
              (stackFrameAt s0.sp mallocngStackBytes ∗ stackFrameAt (s0.sp - 1024#64) 3072) ∗
              (I.BlockM γ (sf.readReg64 .x0) new (max align 16) ∗
                (sf.readReg64 .x0 ↦ₛ bs) ∗
                memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))) ∗ R) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk sf = Ppool
        generalize stackFrameAt s0.sp mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 1024#64) 3072 = Pstk2
        ac_rfl
      rw [hPull, satisfies_pure_sepConj] at hsat
      obtain ⟨⟨hretNe, h16Ret, hFitRet, _⟩, hsat⟩ := hsat
      rw [← hookFrame_eq_stack1024 s0.sp] at hsat
      have hretNe0 : sf.readReg64 .x0 ≠ 0 := hretNe
      have hAlBv16 : alignBv.toNat ≤ 16 := by rwa [hAlignNat]
      have hAlDvd : align ∣ (sf.readReg64 .x0).toNat := by
        rw [← hAlignNat]
        exact Nat.dvd_trans (isPow2Align_dvd_16 hPow2 hAlBv16) h16Ret
      have hMod : (sf.readReg64 .x0).toNat % align = 0 := Nat.mod_eq_zero_of_dvd hAlDvd
      simp only [hretNe0, ↓reduceIte, AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
      refine Satisfies.mono (sepConj_mono_left ?_) hsat
      have hLive := packLiveM (M := M) (I := I) γ hretNe hAlDvd h16Ret hFitRet hLayoutNew
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hLive))) ?_
      have hGoalEq :
          ⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk sf ∗
            Rust.hookFrame s0.sp ∗
            (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
              mallocngLiveM M I γ (sf.readReg64 .x0) new align ∗
              (sf.readReg64 .x0 ↦ₛ bs) ∗
              memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length)) =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
              (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk sf ∗
                Rust.hookFrame s0.sp ∗
                (mallocngLiveM M I γ (sf.readReg64 .x0) new align ∗
                  (sf.readReg64 .x0 ↦ₛ bs) ∗
                  memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length)))) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim stOk sf = Ppool
        generalize Rust.hookFrame s0.sp = Phook
        generalize mallocngLiveM M I γ (sf.readReg64 .x0) new align = Plive
        ac_rfl
      rw [hGoalEq]
      exact Entails.pure_right hPresSf (Entails.pure_right hMod (Entails.refl _))
    · have hOkF : decide (new ≤ MallocngMaxAllocSize) = false := decide_eq_false hMax
      rw [hOkF] at hsat
      simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hsat
      rw [satisfies_pure_sepConj] at hsat
      obtain ⟨hAcc, hsat⟩ := hsat
      have hPresSf : AllocCallPreserved s0 sf :=
        allocCallPreserved_trans hPres (allocCallPreserved_of_fields_eq
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) hAcc)
      have hNull : NullAllowed new align := by
        unfold MallocngMaxAllocSize at hMax
        unfold NullAllowed
        omega
      have hPull :
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf ∗
            stackFrameAt s0.sp mallocngStackBytes ∗
            ⌜sf.readReg64 .x0 = 0#64⌝ ∗
            I.BlockM γ p old (max align 16) ∗
            (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
            stackFrameAt (s0.sp - 1024#64) 3072 ∗ R =
          ⌜sf.readReg64 .x0 = 0#64⌝ ∗
            ((mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf ∗
              (stackFrameAt s0.sp mallocngStackBytes ∗ stackFrameAt (s0.sp - 1024#64) 3072) ∗
              (I.BlockM γ p old (max align 16) ∗
                (p ↦ₛ bs) ∗
                memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length))) ∗ R) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf = Ppool
        generalize stackFrameAt s0.sp mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 1024#64) 3072 = Pstk2
        ac_rfl
      rw [hPull, satisfies_pure_sepConj] at hsat
      obtain ⟨hret0, hsat⟩ := hsat
      rw [← hookFrame_eq_stack1024 s0.sp] at hsat
      have hret0' : sf.readReg64 .x0 = 0 := hret0
      simp only [hret0', ↓reduceIte]
      refine Satisfies.mono (sepConj_mono_left ?_) hsat
      have hLiveOld := packLiveM (M := M) (I := I) γ hpNe hpAlDvd hp16 hp64 hLayoutOld
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hLiveOld))) ?_
      have hGoalEq :
          ⌜AllocCallPreserved s0 sf⌝ ∗
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf ∗
            Rust.hookFrame s0.sp ∗
            (⌜NullAllowed new align⌝ ∗
              mallocngLiveM M I γ p old align ∗
              (p ↦ₛ bs) ∗
              memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)) =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜NullAllowed new align⌝ ∗
              (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf ∗
                Rust.hookFrame s0.sp ∗
                (mallocngLiveM M I γ p old align ∗
                  (p ↦ₛ bs) ∗
                  memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)))) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf = Ppool
        generalize Rust.hookFrame s0.sp = Phook
        generalize mallocngLiveM M I γ p old align = Plive
        ac_rfl
      rw [hGoalEq]
      exact Entails.pure_right hPresSf (Entails.pure_right hNull (Entails.refl _))
  · intro R' sf _ hsat
    dsimp only [mallocngBudgetReallocSomeCSpec] at hsat
    dsimp only [spec, x, rustCliReallocBudgetSpecBase]
    rw [hNewNat] at hsat
    rw [hEvs]
    rw [satisfies_pure_sepConj] at hsat
    obtain ⟨⟨hNotEv, hOomPre⟩, hFR⟩ := hsat
    have hR' : sf.mem ⊨ R' := Satisfies.drop_left hFR
    have hOom0 : OomPreserved s0 sf :=
      oomPreserved_of_allocCallPreserved hPres
        (oomPreserved_of_fields_eq (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) hOomPre)
    have hNotEvs : ¬ FitsEvents M lim st [.realloc align old new] := fun hF => hNotEv hF.1
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hNotEvs, hOom0⟩, hR'⟩

private theorem rdlRealloc_budget_pathB_fail {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart : BitVec 64}
    {reallocAddr cReallocAddr posixMemalignAddr memcpyAddr freeAddr : BitVec 64}
    {lim : BudgetLimits}
    (hCode : hasInstrs P reallocAddr
      (rdlReallocInstrs reallocAddr cReallocAddr posixMemalignAddr memcpyAddr freeAddr))
    (p alignBv newBv : BitVec 64) (old align new : Nat) (bs : List (BitVec 8))
    (st : M.σ) (sv0 : BitVec 64) (R : SepProp) (s0 s2 : State)
    (hsp_align : s0.spAligned = true)
    (hAlignNat : alignBv.toNat = align) (hNewNat : newBv.toNat = new)
    (hLayoutOld : RustLayoutOk old align)
    (hpNe : p ≠ 0#64) (hpAlDvd : align ∣ p.toNat) (hp16 : 16 ∣ p.toNat) (hp64 : p.toNat + old < 2 ^ 64)
    (hNotFit : ¬ MallocngLayoutFit newBv alignBv)
    (hpc2 : s2.pc = reallocAddr + 0x64#64) (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 64#64)
    (hRet32 : s2.readReg32 .x0 = 12#32)
    (hx23 : s2.readReg64 .x23 = s0.readReg64 .x23) (hx24 : s2.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s2.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s2.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s2.readReg64 .x27 = s0.readReg64 .x27) (hx28 : s2.readReg64 .x28 = s0.readReg64 .x28)
    (hcs_v : calleeSavedVRegs s2 = calleeSavedVRegs s0) (hPres2 : AllocCallPreserved s0 s2) :
    let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
    let spec := rustCliReallocBudgetSpecBase M A lim
    let x := (p, old, align, new, bs, st)
    SepWP P (s0.readReg64 Reg.lr) s2
      (memRegion (s0.sp - 56#64) 8 ∗
       mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s2 ∗
       I.BlockM γ p old (max align 16) ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       (((s0.sp - 64#64) ↦₆₄ sv0) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
       (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 64#64 - 1024#64) 3008))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => spec.onOom x s0 sf) := by
  intro A spec x
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion8_entails_pointsTo64 (s0.sp - 56#64))) ?_
  conv => arg 4; rw [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro w1
  refine SepWP.weaken_pre (P' :=
      ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ w1) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
       (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
        stackFrameAt (s0.sp - 64#64 - 1024#64) 3008) ∗
       (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s2 ∗
        I.BlockM γ p old (max align 16) ∗ (p ↦ₛ bs) ∗
        memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length))))
    (Entails.of_eq (by
      generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s2 = Ppool
      generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
      generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2
      ac_rfl)) ?_
  have hf25 := fetch_instr_at 25 (off := 0x64#64) hCode
  have hf26 := fetch_instr_at 26 (off := 0x68#64) hCode
  have hf27 := fetch_instr_at 27 (off := 0x6c#64) hCode
  wp_step; wp_step; wp_step
  wp_if hc
  · apply rdlRealloc_budget_epilogue hCode s0 _ sv0 w1 _ _ _ hsp_align
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun2]) (by simp [arm64_norm, hsp2])
      (by simp [arm64_norm, hx23]) (by simp [arm64_norm, hx24]) (by simp [arm64_norm, hx25])
      (by simp [arm64_norm, hx26]) (by simp [arm64_norm, hx27]) (by simp [arm64_norm, hx28])
      (by simp [arm64_norm, hcs_v])
    intro sf hx0f hspf hcsf hPresEp hVmEp
    simp only [arm64_norm] at hx0f
    refine ⟨fun hsat => ?_, hspf, hcsf⟩
    dsimp only [spec, x, rustCliReallocBudgetSpecBase, A, mallocngRustCliAllocBudgetAt]
    rw [stackAt_eq_hookFrame s0.sp]
    have hx0f0 : sf.readReg64 .x0 = 0 := hx0f
    simp only [hx0f0, ↓reduceIte]
    have hPresSf : AllocCallPreserved s0 sf :=
      allocCallPreserved_trans hPres2 (allocCallPreserved_of_fields_eq
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) hPresEp)
    have hVm2f : VmPreserved s2 sf :=
      vmPreserved_of_fields_eq (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) hVmEp
    have hPoolEq :
        mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s2 =
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf :=
      (mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim st hVm2f).symm
    have hNull : NullAllowed new align := by
      have hgt := not_layoutFit_imp_gt_2pow62 hNotFit
      rw [hNewNat, hAlignNat] at hgt
      exact hgt
    have hLiveOld := packLiveM (M := M) (I := I) γ hpNe hpAlDvd hp16 hp64 hLayoutOld
    refine Satisfies.mono (sepConj_mono_left ?_) hsat
    rw [hPoolEq]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hLiveOld))) ?_
    have hGoalEq :
        ⌜AllocCallPreserved s0 sf⌝ ∗
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf ∗
          Rust.hookFrame s0.sp ∗
          (⌜NullAllowed new align⌝ ∗
            mallocngLiveM M I γ p old align ∗
            (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)) =
        ⌜AllocCallPreserved s0 sf⌝ ∗
          (⌜NullAllowed new align⌝ ∗
            (Rust.hookFrame s0.sp ∗
              (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf ∗
                (mallocngLiveM M I γ p old align ∗
                  ((p ↦ₛ bs) ∗
                    memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)))))) := by
      generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st sf = Ppool
      generalize Rust.hookFrame s0.sp = Phook
      generalize mallocngLiveM M I γ p old align = Plive
      ac_rfl
    rw [hGoalEq]
    exact Entails.pure_right hPresSf (Entails.pure_right hNull (Entails.refl _))
  · dsimp only [State.readReg32, Reg.x0] at hRet32
    rw [hRet32] at hc
    exact absurd hc (by decide)

private theorem rdlRealloc_budget_pathB_free {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart : BitVec 64}
    {cAddrs : MallocngCEntryAddrs} {callocAddr : BitVec 64}
    {reallocAddr memcpyAddr : BitVec 64} {lim : BudgetLimits}
    (hCode : hasInstrs P reallocAddr
      (rdlReallocInstrs reallocAddr cAddrs.realloc cAddrs.posixMemalign memcpyAddr cAddrs.free))
    (hC : MallocngProgBudgetCContracts M I γ mAddrs tp brkStart P cAddrs callocAddr)
    (p q : BitVec 64) (old align new : Nat) (bs : List (BitVec 8))
    (st : M.σ) (sv0 : BitVec 64) (R : SepProp) (s0 s3 : State)
    (hsp_align : s0.spAligned = true)
    (hLayoutNew : RustLayoutOk new align)
    (hSlow : ¬ (align ≤ 16 ∧ align ≤ new))
    (hpNe : p ≠ 0#64) (hp16 : 16 ∣ p.toNat) (hp64 : p.toNat + old < 2 ^ 64)
    (hqNe : q ≠ 0#64) (hqAlDvd : align ∣ q.toNat) (hq16 : 16 ∣ q.toNat) (hq64 : q.toNat + new < 2 ^ 64)
    (hpc3 : s3.pc = reallocAddr + 0x8c#64) (hrun3 : s3.status = .Running) (hsp3 : s3.sp = s0.sp - 64#64)
    (hx21_3 : s3.readReg64 .x21 = q) (hx22_3 : s3.readReg64 .x22 = p)
    (hx23_3 : s3.readReg64 .x23 = s0.readReg64 .x23) (hx24_3 : s3.readReg64 .x24 = s0.readReg64 .x24)
    (hx25_3 : s3.readReg64 .x25 = s0.readReg64 .x25) (hx26_3 : s3.readReg64 .x26 = s0.readReg64 .x26)
    (hx27_3 : s3.readReg64 .x27 = s0.readReg64 .x27) (hx28_3 : s3.readReg64 .x28 = s0.readReg64 .x28)
    (hcs_v3 : calleeSavedVRegs s3 = calleeSavedVRegs s0) (hPres3 : AllocCallPreserved s0 s3) :
    let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
    let spec := rustCliReallocBudgetSpecBase M A lim
    let x := (p, old, align, new, bs, st)
    let st1 := M.step (.aligned (max align 8) new) st
    SepWP P (s0.readReg64 Reg.lr) s3
      ((mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s3 ∗
        stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
        I.BlockM γ p old (max align 16) ∗ memRegion p old) ∗
       (I.BlockM γ q new (max align 16) ∗ (q ↦ₛ bs) ∗
        memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗
        stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 ∗
        (((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ q) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => spec.onOom x s0 sf) := by
  intro A spec x st1
  have hEvs : rustReallocEvents old new align = [.aligned (max align 8) new, .free align old] := by
    unfold rustReallocEvents
    simp [hSlow]
  have hsp_s3 : decide (s3.sp &&& 15#64 = 0#64) = true := by
    rw [hsp3]; exact spAligned_sub64 hsp_align
  have hf35 := fetch_instr_at 35 (off := 0x8c#64) hCode
  have hf36 := fetch_instr_at 36 (off := 0x90#64) hCode
  have hf37 := fetch_instr_at 37 (off := 0x94#64) hCode
  wp_step; wp_step
  refine SepWP.call_subroutine_frame (hC.free_ok lim)
    (x := (p, old, align, st1))
    (F := I.BlockM γ q new (max align 16) ∗ (q ↦ₛ bs) ∗
      memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗
      stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 ∗
      (((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ q) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (ret_pc := reallocAddr + 0x94#64)
    (by simp [arm64_norm]; bv_omega)
    (by simp [arm64_norm, hrun3])
    (by simpa [State.spAligned, arm64_norm] using hsp_s3)
    (by simp [arm64_norm])
    ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    ?_
    (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  · intro R' hsat
    dsimp only [mallocngBudgetFreeCSpec]
    simp only [hpNe, ↓reduceIte]
    conv => pattern (stackFrameAt _ mallocngStackBytes); arg 1; simp only [arm64_norm]; rw [hsp3]
    conv =>
      pattern (mallocngBudgetPoolAt _ _ _ _ _ _ _ _ _)
      simp only [mallocngBudgetPoolAt_setPC, mallocngBudgetPoolAt_writeReg64]
    rw [sepConj_assoc _ _ R'] at hsat
    refine Satisfies.mono (sepConj_mono_left ?_) hsat
    exact Entails.pure_right ⟨by simp [arm64_norm], hp16, hp64⟩
      (Entails.of_eq (by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s3 = Ppool
        generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
        ac_rfl))
  · intro s4 hpc4 hrun4 hsp4 hcs4
    simp only [CalleeSavedPreserved, arm64_norm] at hsp4 hcs4
    have hsp4' : s4.sp = s0.sp - 64#64 := hsp4.trans hsp3
    obtain ⟨_, _, hx21_4, _, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, _, hcs_v4⟩ := hcs4
    replace hx21_4 := hx21_4.trans hx21_3
    replace hx23_4 := hx23_4.trans hx23_3
    replace hx24_4 := hx24_4.trans hx24_3
    replace hx25_4 := hx25_4.trans hx25_3
    replace hx26_4 := hx26_4.trans hx26_3
    replace hx27_4 := hx27_4.trans hx27_3
    replace hx28_4 := hx28_4.trans hx28_3
    replace hcs_v4 := hcs_v4.trans hcs_v3
    have hbeqF : (p == 0#64) = false := beq_false_of_ne hpNe
    dsimp only [mallocngBudgetFreeCSpec]
    rw [hbeqF]
    simp only [Bool.false_eq_true, ↓reduceIte]
    conv => pattern (stackFrameAt _ mallocngStackBytes); arg 1; simp only [arm64_norm]; rw [hsp3]
    simp only [sepConj_assoc]
    apply SepWP.pure_elim; intro hAcc34
    have hPres4 : AllocCallPreserved s0 s4 :=
      allocCallPreserved_trans hPres3 (allocCallPreserved_of_fields_eq
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) hAcc34)
    let st2 := M.step (.free align old) st1
    refine SepWP.weaken_pre (P' :=
        ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ q) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
         (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
          stackFrameAt (s0.sp - 64#64 - 1024#64) 3008) ∗
         (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st2 s4 ∗
          I.BlockM γ q new (max align 16) ∗ (q ↦ₛ bs) ∗
          memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length))))
      (Entails.of_eq (by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st2 s4 = Ppool
        generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2
        ac_rfl)) ?_
    wp_step
    apply rdlRealloc_budget_epilogue hCode s0 _ sv0 q _ _ _ hsp_align
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun4]) (by simp [arm64_norm, hsp4'])
      (by simp [arm64_norm, hx23_4]) (by simp [arm64_norm, hx24_4]) (by simp [arm64_norm, hx25_4])
      (by simp [arm64_norm, hx26_4]) (by simp [arm64_norm, hx27_4]) (by simp [arm64_norm, hx28_4])
      (by simp [arm64_norm, hcs_v4])
    intro sf hx0f hspf hcsf hPresEp hVmEp
    simp only [arm64_norm] at hx0f
    try rw [hx21_4] at hx0f
    refine ⟨fun hsat => ?_, hspf, hcsf⟩
    dsimp only [spec, x, rustCliReallocBudgetSpecBase, A, mallocngRustCliAllocBudgetAt]
    rw [hEvs, stackAt_eq_hookFrame s0.sp]
    have hqNe0 : q ≠ 0 := hqNe
    rw [hx0f]
    simp only [hqNe0, ↓reduceIte, AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
    have hPresSf : AllocCallPreserved s0 sf :=
      allocCallPreserved_trans hPres4 (allocCallPreserved_of_fields_eq
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) hPresEp)
    have hVm4f : VmPreserved s4 sf :=
      vmPreserved_of_fields_eq (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) hVmEp
    have hPoolEq :
        mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st2 s4 =
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st2 sf :=
      (mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim st2 hVm4f).symm
    have hqMod : q.toNat % align = 0 := Nat.mod_eq_zero_of_dvd hqAlDvd
    have hLiveNew := packLiveM (M := M) (I := I) γ hqNe hqAlDvd hq16 hq64 hLayoutNew
    refine Satisfies.mono (sepConj_mono_left ?_) hsat
    rw [hPoolEq]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hLiveNew))) ?_
    have hGoalEq :
        ⌜AllocCallPreserved s0 sf⌝ ∗
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st2 sf ∗
          Rust.hookFrame s0.sp ∗
          (⌜q.toNat % align = 0⌝ ∗
            mallocngLiveM M I γ q new align ∗
            (q ↦ₛ bs) ∗
            memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length)) =
        ⌜AllocCallPreserved s0 sf⌝ ∗
          (⌜q.toNat % align = 0⌝ ∗
            (Rust.hookFrame s0.sp ∗
              (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st2 sf ∗
                (mallocngLiveM M I γ q new align ∗
                  ((q ↦ₛ bs) ∗
                    memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length)))))) := by
      generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st2 sf = Ppool
      generalize Rust.hookFrame s0.sp = Phook
      generalize mallocngLiveM M I γ q new align = Plive
      ac_rfl
    rw [hGoalEq]
    exact Entails.pure_right hPresSf (Entails.pure_right hqMod (Entails.refl _))

private theorem rdlRealloc_budget_pathB_copy {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart : BitVec 64}
    {cAddrs : MallocngCEntryAddrs} {callocAddr : BitVec 64}
    {reallocAddr memcpyAddr : BitVec 64} {lim : BudgetLimits}
    (hCode : hasInstrs P reallocAddr
      (rdlReallocInstrs reallocAddr cAddrs.realloc cAddrs.posixMemalign memcpyAddr cAddrs.free))
    (hC : MallocngProgBudgetCContracts M I γ mAddrs tp brkStart P cAddrs callocAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (p q oldBv newBv : BitVec 64) (old align new : Nat) (bs : List (BitVec 8))
    (st : M.σ) (sv0 : BitVec 64) (R : SepProp) (s0 s2 : State)
    (hsp_align : s0.spAligned = true)
    (hOldNat : oldBv.toNat = old) (hNewNat : newBv.toNat = new)
    (hLayoutNew : RustLayoutOk new align)
    (hSlow : ¬ (align ≤ 16 ∧ align ≤ new))
    (hpNe : p ≠ 0#64) (hp16 : 16 ∣ p.toNat) (hp64 : p.toNat + old < 2 ^ 64)
    (hqNe : q ≠ 0#64) (hqAlDvd : align ∣ q.toNat) (hq16 : 16 ∣ q.toNat) (hq64 : q.toNat + new < 2 ^ 64)
    (hbsOld : bs.length ≤ old) (hbsNew : bs.length ≤ new)
    (hpc2 : s2.pc = reallocAddr + 0x64#64) (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 64#64)
    (hRet32 : s2.readReg32 .x0 = 0#32)
    (hx19_2 : s2.readReg64 .x19 = newBv) (hx20_2 : s2.readReg64 .x20 = oldBv) (hx22_2 : s2.readReg64 .x22 = p)
    (hx23_2 : s2.readReg64 .x23 = s0.readReg64 .x23) (hx24_2 : s2.readReg64 .x24 = s0.readReg64 .x24)
    (hx25_2 : s2.readReg64 .x25 = s0.readReg64 .x25) (hx26_2 : s2.readReg64 .x26 = s0.readReg64 .x26)
    (hx27_2 : s2.readReg64 .x27 = s0.readReg64 .x27) (hx28_2 : s2.readReg64 .x28 = s0.readReg64 .x28)
    (hcs_v2 : calleeSavedVRegs s2 = calleeSavedVRegs s0) (hPres2 : AllocCallPreserved s0 s2) :
    let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
    let spec := rustCliReallocBudgetSpecBase M A lim
    let x := (p, old, align, new, bs, st)
    let st1 := M.step (.aligned (max align 8) new) st
    SepWP P (s0.readReg64 Reg.lr) s2
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s2 ∗
       I.BlockM γ q new (max align 16) ∗ memRegion q new ∗
       I.BlockM γ p old (max align 16) ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ q) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
        (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
         stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => spec.onOom x s0 sf) := by
  intro A spec x st1
  have hsp_s2 : decide (s2.sp &&& 15#64 = 0#64) = true := by
    rw [hsp2]; exact spAligned_sub64 hsp_align
  have hSlot2 : s2.sp + 8#64 = s0.sp - 56#64 := by rw [hsp2]; bv_omega
  conv => arg 4; rw [← hSlot2]
  have hf25 := fetch_instr_at 25 (off := 0x64#64) hCode
  have hf26 := fetch_instr_at 26 (off := 0x68#64) hCode
  have hf27 := fetch_instr_at 27 (off := 0x6c#64) hCode
  have hf28 := fetch_instr_at 28 (off := 0x70#64) hCode
  have hf29 := fetch_instr_at 29 (off := 0x74#64) hCode
  have hf30 := fetch_instr_at 30 (off := 0x78#64) hCode
  have hf31 := fetch_instr_at 31 (off := 0x7c#64) hCode
  have hf32 := fetch_instr_at 32 (off := 0x80#64) hCode
  have hf33 := fetch_instr_at 33 (off := 0x84#64) hCode
  have hf34 := fetch_instr_at 34 (off := 0x88#64) hCode
  wp_step; wp_step; wp_step
  wp_if hc
  · dsimp only [State.readReg32, Reg.x0] at hRet32
    rw [hRet32] at hc
    exact absurd hc (by decide)
  · wp_step; wp_step
    wp_if hq0
    · exact absurd hq0 hqNe
    · conv => arg 4; rw [hSlot2]
      wp_step; wp_step; wp_step; wp_step; wp_step
      let copyBv : BitVec 64 := if newBv.ult oldBv = true then newBv else oldBv
      have hOldLt64 : old < 2 ^ 64 := hOldNat ▸ oldBv.isLt
      have hNewLt64 : new < 2 ^ 64 := hNewNat ▸ newBv.isLt
      have hCopyBounds : bs.length ≤ copyBv.toNat ∧ copyBv.toNat ≤ old ∧ copyBv.toNat ≤ new := by
        dsimp only [copyBv]
        by_cases hcc : newBv.ult oldBv = true
        · have hlt : new < old := by
            rw [← hNewNat, ← hOldNat]; simpa [BitVec.ult] using hcc
          simp only [hcc, ↓reduceIte, hNewNat]; omega
        · have hnlt : ¬ (new < old) := by
            rw [← hNewNat, ← hOldNat]; simpa [BitVec.ult] using hcc
          simp only [hcc, Bool.false_eq_true, ↓reduceIte, hOldNat]; omega
      obtain ⟨hCopy1, hCopy2, hCopy3⟩ := hCopyBounds
      let Pstk64 : SepProp :=
        (((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ q) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      have hPrep :
          (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s2 ∗
           I.BlockM γ q new (max align 16) ∗ memRegion q new ∗
           I.BlockM γ p old (max align 16) ∗ (p ↦ₛ bs) ∗
           memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
           (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
            stackFrameAt (s0.sp - 64#64 - 1024#64) 3008))) ⊢
          ∃∗ midBs : List (BitVec 8),
            ⌜(bs ++ midBs).length = copyBv.toNat⌝ ∗
            (memRegion q (bs ++ midBs).length ∗ (p ↦ₛ (bs ++ midBs))) ∗
            (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s2 ∗
             I.BlockM γ q new (max align 16) ∗ I.BlockM γ p old (max align 16) ∗
             memRegion (p + BitVec.ofNat 64 copyBv.toNat) (old - copyBv.toNat) ∗
             memRegion (q + BitVec.ofNat 64 copyBv.toNat) (new - copyBv.toNat) ∗
             (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
              stackFrameAt (s0.sp - 64#64 - 1024#64) 3008))) := by
        have hRe1 :
            (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s2 ∗
             I.BlockM γ q new (max align 16) ∗ memRegion q new ∗
             I.BlockM γ p old (max align 16) ∗ (p ↦ₛ bs) ∗
             memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
             (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
              stackFrameAt (s0.sp - 64#64 - 1024#64) 3008))) =
            (((p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
              memRegion q new) ∗
             (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s2 ∗
              I.BlockM γ q new (max align 16) ∗ I.BlockM γ p old (max align 16) ∗
              (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
               stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)))) := by
          generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s2 = Ppool
          generalize (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
            stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)) = Pstk
          ac_rfl
        rw [hRe1]
        refine Entails.trans (sepConj_mono_left
          (allocMemcpy_prep_entails p q bs old new copyBv.toNat hCopy1 hCopy2 hCopy3
            (Nat.le_of_lt hOldLt64) (Nat.le_of_lt hNewLt64))) ?_
        simp only [sepExists_sepConj_left]
        refine Entails.sepExists_mono fun midBs => Entails.of_eq (by
          generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s2 = Ppool
          generalize (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
            stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)) = Pstk
          ac_rfl)
      refine SepWP.weaken_pre hPrep ?_
      apply SepWP.exists_elim; intro midBs; apply SepWP.pure_elim; intro hsrcLen
      refine SepWP.call_subroutine_frame hMemcpy (x := (q, p, bs ++ midBs))
        (F := mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s2 ∗
          I.BlockM γ q new (max align 16) ∗ I.BlockM γ p old (max align 16) ∗
          memRegion (p + BitVec.ofNat 64 copyBv.toNat) (old - copyBv.toNat) ∗
          memRegion (q + BitVec.ofNat 64 copyBv.toNat) (new - copyBv.toNat) ∗
          (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
           stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)))
        (ret_pc := reallocAddr + 0x8c#64)
        (by simp [arm64_norm]; bv_omega) (by simp [arm64_norm, hrun2])
        (by simpa [State.spAligned, arm64_norm] using hsp_s2) (by simp [arm64_norm]) ?_
        (fun _ _ _ hp => not_satisfies_false_sepConj hp)
        (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
        (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
      · intro R' hsat
        dsimp only [allocMemcpyVmSpec]; rw [sepConj_assoc] at hsat
        refine Satisfies.mono (sepConj_mono_left ?_) hsat
        have hbvEq : BitVec.ofNat 64 (bs ++ midBs).length = copyBv := by rw [hsrcLen]; simp
        exact Entails.pure_right ⟨by simp [arm64_norm], by simp [arm64_norm],
          by rw [hbvEq]; simp [arm64_norm, copyBv],
          by rw [hsrcLen]; exact copyBv.isLt⟩ (Entails.refl _)
      · intro s3 hpc3 hrun3 hsp3 hcs3
        simp only [CalleeSavedPreserved, arm64_norm] at hsp3 hcs3
        have hsp3' : s3.sp = s0.sp - 64#64 := hsp3.trans hsp2
        obtain ⟨_, _, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, _, hcs_v3⟩ := hcs3
        replace hx22_3 := hx22_3.trans hx22_2
        replace hx23_3 := hx23_3.trans hx23_2
        replace hx24_3 := hx24_3.trans hx24_2
        replace hx25_3 := hx25_3.trans hx25_2
        replace hx26_3 := hx26_3.trans hx26_2
        replace hx27_3 := hx27_3.trans hx27_2
        replace hx28_3 := hx28_3.trans hx28_2
        replace hcs_v3 := hcs_v3.trans hcs_v2
        dsimp only [allocMemcpyVmSpec]; rw [sepConj_assoc]
        apply SepWP.pure_elim; rintro ⟨_, hPresMc, hVmMc⟩
        have hPres3 : AllocCallPreserved s0 s3 :=
          allocCallPreserved_trans hPres2 (allocCallPreserved_of_fields_eq
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
            (by simp [arm64_norm]) hPresMc)
        have hVm23 : VmPreserved s2 s3 :=
          vmPreserved_of_fields_eq (by simp [arm64_norm]) (by simp [arm64_norm])
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) hVmMc
        have hPoolEq3 :
            mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s2 =
              mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s3 :=
          (mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim st1 hVm23).symm
        have hFin :
            (((q ↦ₛ (bs ++ midBs)) ∗ (p ↦ₛ (bs ++ midBs))) ∗
             (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s2 ∗
              I.BlockM γ q new (max align 16) ∗ I.BlockM γ p old (max align 16) ∗
              memRegion (p + BitVec.ofNat 64 copyBv.toNat) (old - copyBv.toNat) ∗
              memRegion (q + BitVec.ofNat 64 copyBv.toNat) (new - copyBv.toNat) ∗
              (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
               stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)))) ⊢
            ((mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s3 ∗
              stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
              I.BlockM γ p old (max align 16) ∗ memRegion p old) ∗
             (I.BlockM γ q new (max align 16) ∗ (q ↦ₛ bs) ∗
              memRegion (q + BitVec.ofNat 64 bs.length) (new - bs.length) ∗
              stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 ∗ Pstk64)) := by
          rw [hPoolEq3]
          have hRe2 :
              (((q ↦ₛ (bs ++ midBs)) ∗ (p ↦ₛ (bs ++ midBs))) ∗
               (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s3 ∗
                I.BlockM γ q new (max align 16) ∗ I.BlockM γ p old (max align 16) ∗
                memRegion (p + BitVec.ofNat 64 copyBv.toNat) (old - copyBv.toNat) ∗
                memRegion (q + BitVec.ofNat 64 copyBv.toNat) (new - copyBv.toNat) ∗
                (Pstk64 ∗ (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
                 stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)))) =
              (((q ↦ₛ (bs ++ midBs)) ∗ (p ↦ₛ (bs ++ midBs)) ∗
                memRegion (p + BitVec.ofNat 64 copyBv.toNat) (old - copyBv.toNat) ∗
                memRegion (q + BitVec.ofNat 64 copyBv.toNat) (new - copyBv.toNat)) ∗
               (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s3 ∗
                I.BlockM γ q new (max align 16) ∗ I.BlockM γ p old (max align 16) ∗
                stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
                stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 ∗ Pstk64)) := by
            generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s3 = Ppool
            generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
            generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2
            ac_rfl
          rw [hRe2]
          refine Entails.trans (sepConj_mono_left
            (copyFinish_entails p q bs midBs old new copyBv.toNat hsrcLen hCopy2 hCopy3
              (Nat.le_of_lt hOldLt64) (Nat.le_of_lt hNewLt64))) ?_
          exact Entails.of_eq (by
            generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s3 = Ppool
            generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
            generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2
            ac_rfl)
        refine SepWP.weaken_pre hFin ?_
        exact rdlRealloc_budget_pathB_free hS γ hCode hC p q old align new bs st sv0 R
          s0 s3 hsp_align hLayoutNew hSlow hpNe hp16 hp64 hqNe hqAlDvd hq16 hq64
          hpc3 hrun3 hsp3' hx21_3 hx22_3
          hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hcs_v3 hPres3

private theorem rdlRealloc_budget_pathB_posix {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart : BitVec 64}
    {cAddrs : MallocngCEntryAddrs} {callocAddr : BitVec 64}
    {reallocAddr memcpyAddr : BitVec 64} {lim : BudgetLimits}
    (hCode : hasInstrs P reallocAddr
      (rdlReallocInstrs reallocAddr cAddrs.realloc cAddrs.posixMemalign memcpyAddr cAddrs.free))
    (hC : MallocngProgBudgetCContracts M I γ mAddrs tp brkStart P cAddrs callocAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (p oldBv alignBv newBv : BitVec 64) (old align new : Nat) (bs : List (BitVec 8))
    (st : M.σ) (sv0 sv1 : BitVec 64) (R : SepProp) (s0 s1 : State)
    (hsp_align : s0.spAligned = true)
    (hOldNat : oldBv.toNat = old) (hAlignNat : alignBv.toNat = align) (hNewNat : newBv.toNat = new)
    (hLayoutNew : RustLayoutOk new align) (hLayoutOld : RustLayoutOk old align)
    (hSlow : ¬ (align ≤ 16 ∧ align ≤ new))
    (hpAlDvd : align ∣ p.toNat)
    (hPow2 : IsPow2Align alignBv) (hAlMax : alignBv.toNat ≤ MaxAlignedAllocAlign)
    (hpNe : p ≠ 0#64) (hp16 : 16 ∣ p.toNat) (hp64 : p.toNat + old < 2 ^ 64)
    (hbsOld : bs.length ≤ old) (hbsNew : bs.length ≤ new)
    (hpc1 : s1.pc = reallocAddr + 0x44#64) (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 64#64)
    (hx0_1 : s1.readReg64 .x0 = p) (hx2_1 : s1.readReg64 .x2 = alignBv)
    (hx19_1 : s1.readReg64 .x19 = newBv) (hx20_1 : s1.readReg64 .x20 = oldBv)
    (hx23_1 : s1.readReg64 .x23 = s0.readReg64 .x23) (hx24_1 : s1.readReg64 .x24 = s0.readReg64 .x24)
    (hx25_1 : s1.readReg64 .x25 = s0.readReg64 .x25) (hx26_1 : s1.readReg64 .x26 = s0.readReg64 .x26)
    (hx27_1 : s1.readReg64 .x27 = s0.readReg64 .x27) (hx28_1 : s1.readReg64 .x28 = s0.readReg64 .x28)
    (hcs_v1 : calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hPres1 : AllocCallPreserved s0 s1) (hVm1 : VmPreserved s0 s1) :
    let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
    let spec := rustCliReallocBudgetSpecBase M A lim
    let x := (p, old, align, new, bs, st)
    SepWP P (s0.readReg64 Reg.lr) s1
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
       I.BlockM γ p old (max align 16) ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ sv1) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
        (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
         stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => spec.onOom x s0 sf) := by
  intro A spec x
  have hEvs : rustReallocEvents old new align = [.aligned (max align 8) new, .free align old] := by
    unfold rustReallocEvents
    simp [hSlow]
  have hsp_s1 : decide (s1.sp &&& 15#64 = 0#64) = true := by
    rw [hsp1]; exact spAligned_sub64 hsp_align
  let effAlign : BitVec 64 := if (8#64).ult alignBv = true then alignBv else 8#64
  have hEffDisj : (effAlign = alignBv ∧ 8 < alignBv.toNat) ∨
      (effAlign = 8#64 ∧ alignBv.toNat ≤ 8) := by
    dsimp only [effAlign]
    by_cases hhi : (8#64).ult alignBv = true
    · exact Or.inl ⟨by simp [hhi], by simpa [BitVec.ult] using hhi⟩
    · exact Or.inr ⟨by simp [hhi], by
        have hn : ¬ (8 < alignBv.toNat) := by simpa [BitVec.ult] using hhi
        omega⟩
  obtain ⟨hEffMax, hMax16, _hEffSz, hPosixOk, hPosixRet⟩ :=
    rdlRealloc_effAlign_props (new := newBv) hPow2 hAlMax hEffDisj
  obtain ⟨hEffNatBv, hEffGe8, hEffAlOk⟩ := effAlign_disj_extra hPow2 hEffDisj
  have hEffNat : effAlign.toNat = max align 8 := by rwa [hAlignNat] at hEffNatBv
  have hMax16' : max effAlign.toNat 16 = max align 16 := by rwa [hAlignNat] at hMax16
  have hf17 := fetch_instr_at 17 (off := 0x44#64) hCode
  have hf18 := fetch_instr_at 18 (off := 0x48#64) hCode
  have hf19 := fetch_instr_at 19 (off := 0x4c#64) hCode
  have hf20 := fetch_instr_at 20 (off := 0x50#64) hCode
  have hf21 := fetch_instr_at 21 (off := 0x54#64) hCode
  have hf22 := fetch_instr_at 22 (off := 0x58#64) hCode
  have hf23 := fetch_instr_at 23 (off := 0x5c#64) hCode
  have hf24 := fetch_instr_at 24 (off := 0x60#64) hCode
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  have hSlot1 : s1.sp + 8#64 = s0.sp - 56#64 := by rw [hsp1]; bv_omega
  conv => arg 4; rw [← hSlot1]
  wp_str64 hf23 m hm
  have hm1 : m.perm = s1.mem.perm := by simpa using hm
  conv => arg 4; rw [hSlot1]
  wp_step
  let F_saved : SepProp :=
    ((s0.sp - 64#64) ↦₆₄ sv0) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  have hPreP :
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
       I.BlockM γ p old (max align 16) ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ 0#64) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
        (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
         stackFrameAt (s0.sp - 64#64 - 1024#64) 3008))) ⊢
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
       memRegion (s0.sp - 56#64) 8 ∗
       stackFrameAt (s0.sp - 64#64) mallocngStackBytes) ∗
      (I.BlockM γ p old (max align 16) ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       F_saved ∗ stackFrameAt (s0.sp - 64#64 - 1024#64) 3008) := by
    dsimp only [F_saved]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
        ((IsBlock.pointsTo64 (s0.sp - 56#64) 0#64).entails_memRegion)))))))) ?_
    exact Entails.of_eq (by
      generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 = Ppool
      generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
      generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2
      ac_rfl)
  refine SepWP.weaken_pre hPreP ?_
  refine SepWP.call_subroutine_frame (hC.posixMemalign_ok lim)
    (x := (s0.sp - 56#64, effAlign, newBv, st))
    (F := I.BlockM γ p old (max align 16) ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
      F_saved ∗ stackFrameAt (s0.sp - 64#64 - 1024#64) 3008)
    (ret_pc := reallocAddr + 0x64#64)
    (by simp [arm64_norm]; bv_omega)
    (by simp [arm64_norm, hrun1])
    (by simpa [State.spAligned, arm64_norm] using hsp_s1)
    (by simp [arm64_norm])
    ?_
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    ?_ ?_
  · intro R' hsat
    dsimp only [mallocngBudgetPosixMemalignCSpec]
    conv => pattern (stackFrameAt _ mallocngStackBytes); arg 1; simp only [arm64_norm]; rw [hsp1]
    conv =>
      pattern (mallocngBudgetPoolAt _ _ _ _ _ _ _ _ _)
      rw [mallocngBudgetPoolAt_setMem_of_perm M I γ mAddrs tp brkStart lim st _ (by simp [hm1])]
      simp only [mallocngBudgetPoolAt_setPC, mallocngBudgetPoolAt_writeReg64,
        mallocngBudgetPoolAt_setPState]
      rw [mallocngBudgetPoolAt_transport M I γ mAddrs tp brkStart lim st hVm1]
    rw [sepConj_assoc _ _ R'] at hsat
    refine Satisfies.mono (sepConj_mono_left ?_) hsat
    exact Entails.pure_right
      ⟨by simp only [arm64_norm]; try rw [hsp1]; bv_omega,
       by simp only [arm64_norm, effAlign],
       by simp only [arm64_norm],
       hEffMax⟩
      (Entails.of_eq (by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 = Ppool
        generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
        ac_rfl))
  · intro s2 hpc2 hrun2 hsp2 hcs2
    simp only [CalleeSavedPreserved, arm64_norm] at hsp2 hcs2
    have hsp2' : s2.sp = s0.sp - 64#64 := hsp2.trans hsp1
    obtain ⟨hx19_2, hx20_2, _, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, hcs_v2⟩ := hcs2
    replace hx19_2 := hx19_2.trans hx19_1
    replace hx20_2 := hx20_2.trans hx20_1
    replace hx23_2 := hx23_2.trans hx23_1
    replace hx24_2 := hx24_2.trans hx24_1
    replace hx25_2 := hx25_2.trans hx25_1
    replace hx26_2 := hx26_2.trans hx26_1
    replace hx27_2 := hx27_2.trans hx27_1
    replace hx28_2 := hx28_2.trans hx28_1
    replace hcs_v2 := hcs_v2.trans hcs_v1
    dsimp only [mallocngBudgetPosixMemalignCSpec]
    rw [hPosixOk, hPosixRet, hMax16', hEffNat, hNewNat]
    conv => pattern (stackFrameAt _ mallocngStackBytes); arg 1; simp only [arm64_norm]; rw [hsp1]
    simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hAcc12, hRet32⟩
    have hPres2 : AllocCallPreserved s0 s2 :=
      allocCallPreserved_trans hPres1 (allocCallPreserved_of_fields_eq
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) hAcc12)
    by_cases hFit : MallocngLayoutFit newBv alignBv
    · rw [decide_eq_true hFit]
      simp only [hFit, ↓reduceIte, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc] at hRet32 ⊢
      apply SepWP.exists_elim; intro q
      let st1 := M.step (.aligned (max align 8) new) st
      have hPullQ :
          mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s2 ∗
            stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
            ⌜q ≠ 0#64 ∧ max align 16 ∣ q.toNat ∧ q.toNat + new < 2 ^ 64⌝ ∗
            ((s0.sp - 56#64) ↦₆₄ q) ∗
            I.BlockM γ q new (max align 16) ∗
            memRegion q new ∗
            I.BlockM γ p old (max align 16) ∗
            (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
            F_saved ∗ stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 =
          ⌜q ≠ 0#64 ∧ max align 16 ∣ q.toNat ∧ q.toNat + new < 2 ^ 64⌝ ∗
            (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s2 ∗
              stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
              ((s0.sp - 56#64) ↦₆₄ q) ∗
              I.BlockM γ q new (max align 16) ∗
              memRegion q new ∗
              I.BlockM γ p old (max align 16) ∗
              (p ↦ₛ bs) ∗
              memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
              F_saved ∗ stackFrameAt (s0.sp - 64#64 - 1024#64) 3008) := by
        generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st1 s2 = Ppool
        generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
        generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2
        ac_rfl
      rw [hPullQ]
      apply SepWP.pure_elim; rintro ⟨hqNe, hqAlignEff, hq64⟩
      have hqAlDvd : align ∣ q.toNat := by
        rw [← hAlignNat]
        exact Nat.dvd_trans (pow2_dvd_max16 hPow2) (by rwa [hAlignNat])
      have hq16 : 16 ∣ q.toNat := Nat.dvd_trans (sixteen_dvd_max16_of_layoutOk hLayoutNew) hqAlignEff
      refine SepWP.weaken_pre (Entails.of_eq ?_)
        (rdlRealloc_budget_pathB_copy hS γ hCode hC hMemcpy p q oldBv newBv old align new bs
          st sv0 R s0 s2 hsp_align hOldNat hNewNat hLayoutNew hSlow hpNe hp16 hp64
          hqNe hqAlDvd hq16 hq64 hbsOld hbsNew
          hpc2 hrun2 hsp2' hRet32 hx19_2 hx20_2 hx22_2
          hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hcs_v2 hPres2)
      dsimp only [F_saved, st1]
      generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim (M.step (.aligned (max align 8) new) st) s2 = Ppool
      generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
      generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2
      ac_rfl
    · rw [decide_eq_false hFit]
      simp only [hFit, Bool.false_eq_true, ↓reduceIte] at hRet32 ⊢
      refine SepWP.weaken_pre (Entails.of_eq ?_)
        (rdlRealloc_budget_pathB_fail hS γ hCode p alignBv newBv old align new bs st sv0 R s0 s2
          hsp_align hAlignNat hNewNat hLayoutOld hpNe hpAlDvd hp16 hp64 hFit hpc2 hrun2 hsp2' hRet32
          hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hcs_v2 hPres2)
      dsimp only [F_saved]
      generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s2 = Ppool
      generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
      generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2
      ac_rfl
  · intro R' sf _ hsat
    dsimp only [mallocngBudgetPosixMemalignCSpec] at hsat
    dsimp only [spec, x, rustCliReallocBudgetSpecBase]
    rw [hEffNat, hNewNat] at hsat
    rw [hEvs]
    rw [satisfies_pure_sepConj] at hsat
    obtain ⟨⟨hNotPosix, hOomPre⟩, hFR⟩ := hsat
    have hR' : sf.mem ⊨ R' := Satisfies.drop_left hFR
    have hOom0 : OomPreserved s0 sf :=
      oomPreserved_of_allocCallPreserved hPres1
        (oomPreserved_of_fields_eq (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) hOomPre)
    have hNotEvs : ¬ FitsEvents M lim st [.aligned (max align 8) new, .free align old] := by
      intro hF
      exact hNotPosix ⟨Nat.le_max_right align 8, hEffAlOk, hF.1⟩
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hNotEvs, hOom0⟩, hR'⟩

private theorem realloc_prologue_pre_entails {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    (mAddrs : MallocngAddrs) (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (p : BitVec 64) (old align : Nat) (bs : List (BitVec 8)) (st : M.σ) (s0 : State) :
    let A := mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart
    (A.pool lim st s0 ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
     memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
     stackAt s0.sp allocHookStack) ⊢
    ∃∗ sv0 : BitVec 64, ∃∗ sv1 : BitVec 64, ∃∗ sv2 : BitVec 64, ∃∗ sv3 : BitVec 64,
    ∃∗ sv4 : BitVec 64, ∃∗ sv5 : BitVec 64, ∃∗ sv6 : BitVec 64, ∃∗ sv7 : BitVec 64,
      ⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + old < 2 ^ 64 ∧ RustLayoutOk old align⌝ ∗
      (mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 ∗
       I.BlockM γ p old (max align 16) ∗ (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
       ((((s0.sp - 64#64) ↦₆₄ sv0) ∗ ((s0.sp - 56#64) ↦₆₄ sv1) ∗
         ((s0.sp - 48#64) ↦₆₄ sv2) ∗ ((s0.sp - 40#64) ↦₆₄ sv3) ∗
         ((s0.sp - 32#64) ↦₆₄ sv4) ∗ ((s0.sp - 24#64) ↦₆₄ sv5) ∗
         ((s0.sp - 16#64) ↦₆₄ sv6) ∗ ((s0.sp - 8#64) ↦₆₄ sv7)) ∗
        (stackFrameAt (s0.sp - 64#64) mallocngStackBytes ∗
         stackFrameAt (s0.sp - 64#64 - 1024#64) 3008))) := by
  intro A
  dsimp only [A, mallocngRustCliAllocBudgetAt]
  rw [stackAt_eq_hookFrame s0.sp, hookFrame_eq_stack64_1024 s0.sp]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (unpackLiveM γ p old align))) ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (unpack_stack64 s0.sp)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_mono fun sv0 => Entails.sepExists_mono fun sv1 =>
    Entails.sepExists_mono fun sv2 => Entails.sepExists_mono fun sv3 =>
    Entails.sepExists_mono fun sv4 => Entails.sepExists_mono fun sv5 =>
    Entails.sepExists_mono fun sv6 => Entails.sepExists_mono fun sv7 => ?_
  exact Entails.of_eq (by
    generalize mallocngBudgetPoolAt M I γ mAddrs tp brkStart lim st s0 = Ppool
    generalize stackFrameAt (s0.sp - 64#64) mallocngStackBytes = Pstk1
    generalize stackFrameAt (s0.sp - 64#64 - 1024#64) 3008 = Pstk2
    ac_rfl)

/-- Placed `rustc 1.98.1` `__rustc::__rdl_realloc` (`43` instructions: `rdlReallocInstrs`) satisfies
    `rustCliReallocBudgetSpec` over `mallocngRustCliAllocBudgetAt`. -/
theorem rdlRealloc_budget_placed_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName) {P : Program}
    {mAddrs : MallocngAddrs} {tp brkStart : BitVec 64}
    {cAddrs : MallocngCEntryAddrs} {callocAddr : BitVec 64}
    (reallocAddr memcpyAddr : BitVec 64) (lim : BudgetLimits)
    (hCode : hasInstrs P reallocAddr
      (rdlReallocInstrs reallocAddr cAddrs.realloc cAddrs.posixMemalign memcpyAddr cAddrs.free))
    (hC : MallocngProgBudgetCContracts M I γ mAddrs tp brkStart P cAddrs callocAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    subroutine_ok P reallocAddr
      (rustCliReallocBudgetSpecBase M (mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart) lim) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨p, old, align, new, bs, st⟩ R s0 hpc hrun hpre hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only [rustCliReallocBudgetSpecBase]
  apply SepWP.pure_elim
  let oldBv := s0.readReg64 .x1
  let alignBv := s0.readReg64 .x2
  let newBv := s0.readReg64 .x3
  rintro ⟨hx0, hOldNat, hAlignNat, hNewNat, hLayoutNew, hbsOld, hbsNew⟩
  have hAlignBv : alignBv.toNat = align := hAlignNat
  have ⟨⟨_hNewPos, ⟨k, hk⟩, _hSum63⟩, hAlLe⟩ := hLayoutNew
  have hPow2 : IsPow2Align alignBv := isPow2Align_of_toNat_pow2 (hAlignBv.trans hk)
  have hAlMax : alignBv.toNat ≤ MaxAlignedAllocAlign := by rwa [hAlignBv]
  refine SepWP.weaken_pre
    (realloc_prologue_pre_entails hS γ mAddrs tp brkStart lim p old align bs st s0) ?_
  apply SepWP.exists_elim; intro sv0; apply SepWP.exists_elim; intro sv1
  apply SepWP.exists_elim; intro sv2; apply SepWP.exists_elim; intro sv3
  apply SepWP.exists_elim; intro sv4; apply SepWP.exists_elim; intro sv5
  apply SepWP.exists_elim; intro sv6; apply SepWP.exists_elim; intro sv7
  apply SepWP.pure_elim; rintro ⟨hpNe, hpAlDvd, hp16, hp64, hLayoutOld⟩
  have hsp_sub : decide ((s0.sp - 64#64) &&& 15#64 = 0#64) = true := spAligned_sub64 hsp_align
  have hf0 := fetch_instr_at0 hCode
  have hf1 := fetch_instr_at 1 (off := 0x04#64) hCode
  have hf2 := fetch_instr_at 2 (off := 0x08#64) hCode
  have hf3 := fetch_instr_at 3 (off := 0x0c#64) hCode
  have hf4 := fetch_instr_at 4 (off := 0x10#64) hCode
  have hf5 := fetch_instr_at 5 (off := 0x14#64) hCode
  have hf6 := fetch_instr_at 6 (off := 0x18#64) hCode
  have hf7 := fetch_instr_at 7 (off := 0x1c#64) hCode
  have hf8 := fetch_instr_at 8 (off := 0x20#64) hCode
  have hf9 := fetch_instr_at 9 (off := 0x24#64) hCode
  have hf10 := fetch_instr_at 10 (off := 0x28#64) hCode
  wp_step; wp_stp64 hf1 m1 hm1; wp_stp64 hf2 m2 hm2; wp_stp64 hf3 m3 hm3
  have hm30 : m3.perm = s0.mem.perm := by
    simp at hm1 hm2 hm3
    exact hm3.trans (hm2.trans hm1)
  wp_step; wp_step; wp_step; wp_step; wp_step
  wp_if hgt16
  · have hGt16Nat : 16 < align := by
      rw [← hAlignBv]; simpa [BitVec.ult] using hgt16
    exact rdlRealloc_budget_pathB_posix hS γ hCode hC hMemcpy p oldBv alignBv newBv old align new
      bs st sv0 sv1 R s0 _ hsp_align hOldNat hAlignBv hNewNat hLayoutNew hLayoutOld
      (fun h => by omega) hpAlDvd hPow2 hAlMax hpNe hp16 hp64 hbsOld hbsNew
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm])
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm, alignBv])
      (by simp [arm64_norm, newBv]) (by simp [arm64_norm, oldBv])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by unfold AllocCallPreserved; simp [arm64_norm])
      (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm, hm30]))
  · have hAl16 : align ≤ 16 := by
      have hn : ¬ (16 < alignBv.toNat) := by simpa [BitVec.ult] using hgt16
      omega
    wp_step; wp_step
    wp_if hgtNew
    · have hLtNewNat : new < align := by
        rw [← hNewNat, ← hAlignBv]; simpa [BitVec.ult] using hgtNew
      exact rdlRealloc_budget_pathB_posix hS γ hCode hC hMemcpy p oldBv alignBv newBv old align new
        bs st sv0 sv1 R s0 _ hsp_align hOldNat hAlignBv hNewNat hLayoutNew hLayoutOld
        (fun h => by omega) hpAlDvd hPow2 hAlMax hpNe hp16 hp64 hbsOld hbsNew
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm])
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm, alignBv])
        (by simp [arm64_norm, newBv]) (by simp [arm64_norm, oldBv])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by unfold AllocCallPreserved; simp [arm64_norm])
        (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm, hm30]))
    · have hAlNew : align ≤ new := by
        have hn : ¬ (newBv.toNat < alignBv.toNat) := by simpa [BitVec.ult] using hgtNew
        have hNewBv : newBv.toNat = new := hNewNat
        omega
      exact rdlRealloc_budget_pathA hS γ hCode hC p alignBv newBv old align new bs st
        sv0 sv1 R s0 _ hsp_align hAlignBv hNewNat hLayoutNew hLayoutOld hpAlDvd hPow2 hAl16 hAlNew
        hpNe hp16 hp64 hbsOld hbsNew
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm])
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm, newBv])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by unfold AllocCallPreserved; simp [arm64_norm])
        (vmPreserved_of_eq (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm, hm30]))

/-! ## `B`-Thunk Lifts (`__rustc::__rust_{alloc,dealloc,realloc}`) -/

private theorem readReg64_setPC_eq (s : State) (pc' : BitVec 64) (r : Reg) :
    (s.setPC pc').readReg64 r = s.readReg64 r := by cases s; rfl

private theorem sp_setPC_eq (s : State) (pc' : BitVec 64) :
    (s.setPC pc').sp = s.sp := by cases s; rfl

private theorem allocCallPreserved_setPC_left (s0 sf : State) (pc' : BitVec 64) :
    AllocCallPreserved (s0.setPC pc') sf = AllocCallPreserved s0 sf := by cases s0; rfl

private theorem oomPreserved_setPC_left (s0 sf : State) (pc' : BitVec 64) :
    OomPreserved (s0.setPC pc') sf = OomPreserved s0 sf := by cases s0; rfl

theorem rustCliAllocBudget_of_b_thunk {M : AllocCostModel} {A : RustCliAllocBudget M}
    {P : Program} {thunkAddr targetAddr : BitVec 64} {lim : BudgetLimits} {zeroed : Bool}
    (hThunk : hasInstrs P thunkAddr [ .b (targetAddr - thunkAddr) ])
    (hok : subroutine_ok P targetAddr (rustCliAllocBudgetSpecBase M A lim zeroed)) :
    subroutine_ok P thunkAddr (rustCliAllocBudgetSpecBase M A lim zeroed) :=
  subroutine_ok_of_b_thunk (fetch_instr_at0 hThunk)
    (hpre_pc := by
      rintro ⟨size, align, st⟩ s pc'
      dsimp only [rustCliAllocBudgetSpecBase]
      rw [readReg64_setPC_eq, readReg64_setPC_eq, sp_setPC_eq, A.pool_setPC])
    (hpost_pc := by
      rintro ⟨size, align, st⟩ s0 sf pc'
      dsimp only [rustCliAllocBudgetSpecBase]
      rw [allocCallPreserved_setPC_left, sp_setPC_eq])
    (hoom_pc := by
      rintro ⟨size, align, st⟩ s0 sf pc'
      dsimp only [rustCliAllocBudgetSpecBase]
      rw [oomPreserved_setPC_left])
    (hok := hok)

theorem rustCliDeallocBudget_of_b_thunk {M : AllocCostModel} {A : RustCliAllocBudget M}
    {P : Program} {thunkAddr targetAddr : BitVec 64} {lim : BudgetLimits}
    (hThunk : hasInstrs P thunkAddr [ .b (targetAddr - thunkAddr) ])
    (hok : subroutine_ok P targetAddr (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok P thunkAddr (rustCliDeallocBudgetSpecBase M A lim) :=
  subroutine_ok_of_b_thunk (fetch_instr_at0 hThunk)
    (hpre_pc := by
      rintro ⟨p, size, align, st⟩ s pc'
      dsimp only [rustCliDeallocBudgetSpecBase]
      rw [readReg64_setPC_eq, readReg64_setPC_eq, readReg64_setPC_eq, sp_setPC_eq, A.pool_setPC])
    (hpost_pc := by
      rintro ⟨p, size, align, st⟩ s0 sf pc'
      dsimp only [rustCliDeallocBudgetSpecBase]
      rw [allocCallPreserved_setPC_left, sp_setPC_eq])
    (hoom_pc := by intros; rfl)
    (hok := hok)

theorem rustCliReallocBudget_of_b_thunk {M : AllocCostModel} {A : RustCliAllocBudget M}
    {P : Program} {thunkAddr targetAddr : BitVec 64} {lim : BudgetLimits}
    (hThunk : hasInstrs P thunkAddr [ .b (targetAddr - thunkAddr) ])
    (hok : subroutine_ok P targetAddr (rustCliReallocBudgetSpecBase M A lim)) :
    subroutine_ok P thunkAddr (rustCliReallocBudgetSpecBase M A lim) :=
  subroutine_ok_of_b_thunk (fetch_instr_at0 hThunk)
    (hpre_pc := by
      rintro ⟨p, old, align, new, bs, st⟩ s pc'
      dsimp only [rustCliReallocBudgetSpecBase]
      rw [readReg64_setPC_eq, readReg64_setPC_eq, readReg64_setPC_eq, readReg64_setPC_eq,
          sp_setPC_eq, A.pool_setPC])
    (hpost_pc := by
      rintro ⟨p, old, align, new, bs, st⟩ s0 sf pc'
      dsimp only [rustCliReallocBudgetSpecBase]
      rw [allocCallPreserved_setPC_left, sp_setPC_eq])
    (hoom_pc := by
      rintro ⟨p, old, align, new, bs, st⟩ s0 sf pc'
      dsimp only [rustCliReallocBudgetSpecBase]
      rw [oomPreserved_setPC_left])
    (hok := hok)

theorem RustCliAllocBudgetEntriesBase.of_thunks {M : AllocCostModel} {A : RustCliAllocBudget M}
    {P : Program} {thunkAddrs rdlAddrs : RustAllocAddrs}
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hRdl : RustCliAllocBudgetEntriesBase M A P rdlAddrs) :
    RustCliAllocBudgetEntriesBase M A P thunkAddrs where
  alloc lim := rustCliAllocBudget_of_b_thunk hThunks.alloc_thunk (hRdl.alloc lim)
  dealloc lim := rustCliDeallocBudget_of_b_thunk hThunks.dealloc_thunk (hRdl.dealloc lim)
  realloc lim := rustCliReallocBudget_of_b_thunk hThunks.realloc_thunk (hRdl.realloc lim)

theorem RustCliAllocBudgetEntries.of_thunks [CryptoVerification.LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {P : Program} {thunkAddrs rdlAddrs : RustAllocAddrs}
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hRdl : RustCliAllocBudgetEntriesBase M A P rdlAddrs) :
    RustCliAllocBudgetEntries M A P thunkAddrs :=
  (RustCliAllocBudgetEntriesBase.of_thunks hThunks hRdl).toPlaced

/-! ## Top-Level `RustCliAllocBudgetEntries` and `RustCliAllocNoOomEntries` Bundles -/

/-- Placed `__rustc::__rdl_{alloc,dealloc,realloc}` `RustCliAllocBudgetEntries` bundle over
    `mallocngRustCliAllocBudgetAt` from an arbitrary `MallocngProgBudgetCContracts` witness. -/
theorem mallocngRustCliAllocBudgetAtEntries {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) (γ : GhostName)
    {P : Program} {mAddrs : MallocngAddrs} (tp brkStart : BitVec 64)
    {cAddrs : MallocngCEntryAddrs} {callocAddr : BitVec 64}
    {rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd cAddrs memcpyAddr)
    (hC : MallocngProgBudgetCContracts M I γ mAddrs tp brkStart P cAddrs callocAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocBudgetEntriesBase M
      (mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart)
      P rdlAddrs where
  alloc lim := rdlAlloc_budget_placed_ok hS γ rdlAddrs.alloc lim hShims.alloc_instrs hC
  dealloc lim :=
    rdlDealloc_budget_placed_ok hS γ rdlAddrs.dealloc lim hShims.dealloc_instrs hC
  realloc lim :=
    rdlRealloc_budget_placed_ok hS γ rdlAddrs.realloc memcpyAddr lim
      hShims.realloc_instrs hC hMemcpy

theorem mallocngRustCliAllocBudgetAtEntries_thunks {M : AllocCostModel}
    {I : MallocngCostModelIface M} (hS : MallocngCostModelSound M I) (γ : GhostName)
    {P : Program} {mAddrs : MallocngAddrs} (tp brkStart : BitVec 64)
    {cAddrs : MallocngCEntryAddrs} {callocAddr : BitVec 64}
    {thunkAddrs rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd cAddrs memcpyAddr)
    (hC : MallocngProgBudgetCContracts M I γ mAddrs tp brkStart P cAddrs callocAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocBudgetEntriesBase M
      (mallocngRustCliAllocBudgetAt M I hS γ mAddrs tp brkStart)
      P thunkAddrs :=
  RustCliAllocBudgetEntriesBase.of_thunks hThunks
    (mallocngRustCliAllocBudgetAtEntries hS γ tp brkStart hShims hC hMemcpy)

/-- Placed `__rustc::__rdl_{alloc,dealloc,realloc}` `RustCliAllocBudgetEntries` bundle for any
    program `P` containing `VerifiedLibraries.mallocngLib` at `mpl : Obj.MultiPlacement`
    (`ProgContainsMallocng P mpl`), parameterized over `(M, I)` (`MallocngCostModelSound M I`). -/
theorem mallocngRustCliAllocBudgetEntries {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocBudgetEntriesBase M
      (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart)
      P rdlAddrs :=
  mallocngRustCliAllocBudgetAtEntries hS γ tp brkStart hShims
    (mallocngProgBudgetCContracts_of_placed hS hP γ tp brkStart) hMemcpy

theorem mallocngRustCliAllocBudgetEntries_thunks {M : AllocCostModel}
    {I : MallocngCostModelIface M} (hS : MallocngCostModelSound M I)
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {thunkAddrs rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocBudgetEntriesBase M
      (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart)
      P thunkAddrs :=
  RustCliAllocBudgetEntriesBase.of_thunks hThunks
    (mallocngRustCliAllocBudgetEntries hS hP γ tp brkStart hShims hMemcpy)

theorem mallocngRustCliAllocNoOomEntries {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I)
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64) (lim : BudgetLimits)
    {rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocNoOomEntriesBase M
      (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart)
      lim P rdlAddrs :=
  (mallocngRustCliAllocBudgetEntries hS hP γ tp brkStart hShims hMemcpy).toNoOom lim

theorem mallocngRustCliAllocNoOomEntries_thunks {M : AllocCostModel}
    {I : MallocngCostModelIface M} (hS : MallocngCostModelSound M I)
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64) (lim : BudgetLimits)
    {thunkAddrs rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocNoOomEntriesBase M
      (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart)
      lim P thunkAddrs :=
  (mallocngRustCliAllocBudgetEntries_thunks hS hP γ tp brkStart hThunks hShims hMemcpy).toNoOom lim

end LibsignalBinary.Heap
