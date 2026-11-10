/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.StdoutAdapter
public meta import CaseStudies.Hashbrown.Proofs.StdCli.StdoutAdapter
public meta import ProofLib.SepLogic.Stack

/-!
# `OnceLock<Stdout>::initialize` and Formatted Print Proofs

Total-correctness contracts over `HbCliLayout` for `OnceLock<Stdout>::initialize`,
`<&Stdout as Write>::write_fmt`, and `std::io::stdio::__print`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open CaseStudies.Hashbrown

local macro "iAdrp " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr true $rd (adrpOff $pc $t))
local macro "iAdr " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr false $rd ($t - $pc))
local macro "iAddLo12 " rd:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.addSubImm .W64 .ADD $rd $rn (($t).truncate 12) false)
local macro "iLdr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.ldr .W64 .X64 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iLdrbLo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.ldr .W32 .B8 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.str .X64 $rt (.Offset $rn (pageLo12 $t)))
local macro "iBl " pc:term:arg t:term:arg : term => `(Instr.bl ($t - $pc))
local macro "iB " pc:term:arg t:term:arg : term => `(Instr.b ($t - $pc))


local macro "unpack_stdout_code " chunks:ident h:term : tactic => `(tactic| (
  have _hc := stdoutToStepFacts $h
  simp only [$chunks:ident, stdoutStepFacts, stdoutStepAcc, fetchAtAcc',
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

local macro "norm_jmp" : tactic =>
  `(tactic| conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel'])

local macro "unpack_cells " k:num : tactic => `(tactic| (
  try simp only [Nat.reduceMul]
  cells_unfold
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate $k (apply SepWP.exists_left; intro _)))

local macro "repack_cells" : tactic => `(tactic| (
  try simp only [Nat.reduceMul]
  cells_unfold
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  sep_entail))

attribute [local simp] cpuAux_writeReg64 cpuAux_writeReg32 cpuAux_writeReg
  cpuAux_setPState cpuAux_advancePC cpuAux_setPC cpuAux_setMem

local macro "unpack_cs " h:ident : tactic =>
  `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := $h)
local macro "close_cs" : tactic =>
  `(tactic| simp [CalleeSavedPreserved.iff_regs, Reg.fp, wp_norm, arm64_norm, *])
local macro "wp_a" : term =>
  `(by simp [wp_norm, arm64_norm, bv_lin_norm, bv64_add_sub_cancel', *]; try bv_lin)

private theorem isAligned_w32_of_mod4 {a : BitVec 64} (h : a.toNat % 4 = 0) :
    MemWidth.isAligned .W32 a = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]; change a.toNat &&& 3 = 0
  rw [Nat.and_two_pow_sub_one_eq_mod _ 2]; exact h

private theorem isAligned_x64_of_mod8 {a : BitVec 64} (h : a.toNat % 8 = 0) :
    MemWidth.isAligned .X64 a = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]; change a.toNat &&& 7 = 0
  rw [Nat.and_two_pow_sub_one_eq_mod _ 3]; exact h

theorem hbValid_stdout_align {C : HbCliLayout} (hv : C.Valid) :
    MemWidth.isAligned .X64 C.std.stdoutGlobalAddr = true ∧
    MemWidth.isAligned .W32 (C.std.stdoutGlobalAddr + 0x08#64) = true ∧
    MemWidth.isAligned .W32 (C.std.stdoutGlobalAddr + 0x38#64) = true ∧
    MemWidth.isAligned .X64 C.std.threadIdCounterAddr = true := by
  have hal := hv.stdoutGlobal_align
  have hnw := hv.stdoutGlobal_noWrap
  have h8 : (C.std.stdoutGlobalAddr + 0x08#64).toNat = C.std.stdoutGlobalAddr.toNat + 8 := by
    rw [BitVec.toNat_add, show (0x08#64 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
  have h56 : (C.std.stdoutGlobalAddr + 0x38#64).toNat = C.std.stdoutGlobalAddr.toNat + 56 := by
    rw [BitVec.toNat_add, show (0x38#64 : BitVec 64).toNat = 56 from rfl, Nat.mod_eq_of_lt (by omega)]
  exact ⟨isAligned_x64_of_mod8 hal, isAligned_w32_of_mod4 (by omega),
    isAligned_w32_of_mod4 (by omega), isAligned_x64_of_mod8 hv.threadIdCtr_align⟩

theorem step_ldar32_words {prog : Program} {target_pc : BitVec 64}
    (addr : BitVec 64) (words : List (BitVec 32))
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {w : BitVec 32} {rn rt : Reg} {ea : BitVec 64} {v : BitVec 32}
    (i : Nat) (next_pc : BitVec 64) (halign : MemWidth.isAligned .W32 ea = true)
    (rt' : Reg := .gpr 8#5)
    (hw : prog.hasCode addr words := by with_reducible assumption)
    (hget : words[i]? = some w := by rfl)
    (hdec : decode w = some (.ldarStlr .W32 true rn rt) := by rfl)
    (hrt : rt = rt' := by decide) (hrn : rn ≠ .sp := by decide)
    (hpc_next : addr + BitVec.ofNat 64 (4 * (i + 1)) = next_pc := by simp [bv_lin_norm]; try bv_lin)
    (hpc : s.pc = addr + BitVec.ofNat 64 (4 * i) := by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp [wp_norm, arm64_norm, *])
    (haddr : s.readReg64 rn = ea := by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hload : SepLoad32 ea P v := by wp_sep_access_fast)
    (hnext : SepWP prog target_pc ((s.writeReg64 rt' (v.zeroExtend 64)).setPC next_pc) P post oom) :
    SepWP prog target_pc s P post oom := by
  subst hrt hpc_next
  have hsp : checkRegSPAligned s rn = true := by cases rn <;> simp_all [checkRegSPAligned]
  apply SepWP.weaken_pre_frame (P' := ⌜s.mem.read32 ea = v ∧ s.mem.canRead ea 4 = true⌝ ∗ P)
  · intro R hm; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hload.load hm, hload.readable hm⟩, hm⟩
  · apply SepWP.pure_elim; rintro ⟨hread, hcan⟩
    refine SepWP.step_pure (s' := (s.writeReg64 rt (v.zeroExtend 64)).setPC (addr + BitVec.ofNat 64 (4 * (i + 1))))
      hpc hrun (Program.fetch_of_hasWords_getElem_decode i w hw rfl hget hdec) ?_ rfl hnext
    have hs_eq : s.setPC (addr + BitVec.ofNat 64 (4 * i)) = s := by
      cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm
    have hpc4 : s.pc + 4#64 = addr + BitVec.ofNat 64 (4 * (i + 1)) := by
      rw [hpc, Nat.mul_succ, BitVec.ofNat_add]; bv_lin
    rw [hs_eq]
    simp [Program.evalInst, execInstWithSvc, Memory.readSized, State.writeReg,
      State.advancePC, State.setPC, hsp, haddr, halign, hread, hcan, MemWidth.bytes, hpc4]

private theorem hbStdoutZeroBytes_to_fields (g : BitVec 64) :
    (g ↦ₛ List.replicate 56 0#8) ⊢
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ b6 : BitVec 8,
        (g ↦₆₄ v0) ∗ ((g + 0x08#64) ↦₆₄ v1) ∗ ((g + 0x10#64) ↦₆₄ v2) ∗
        ((g + 0x18#64) ↦₆₄ v3) ∗ ((g + 0x20#64) ↦₆₄ v4) ∗ ((g + 0x28#64) ↦₆₄ v5) ∗
        ((g + 0x30#64) ↦₈ b6) ∗ memRegion (g + 0x31#64) 7 := by
  refine Entails.trans (pointsToBytes_entails_memRegion_of_length (n := 56) (by decide)) ?_
  rw [show (56 : Nat) = 48 + 1 + 7 from rfl, memRegion_split_three g 48 1 7 (by decide),
      show (48 : Nat) = 8 * 6 from rfl, memRegion_cells g 6 (by decide),
      show g + BitVec.ofNat 64 (8 * 6) + BitVec.ofNat 64 1 = g + 0x31#64 by bv_lin,
      show g + BitVec.ofNat 64 (8 * 6) = g + 0x30#64 by bv_lin]
  simp only [cells_succ, cells_zero, sepConj_emp, bv_lin_norm, sepExists_sepConj_left, sepConj_assoc]
  rw [memRegion_one]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

private def hbStdoutInitFields (g bufPtr : BitVec 64) : SepProp :=
  (g ↦₆₄ 0#64) ∗ ((g + 0x08#64) ↦₃₂ 0#32) ∗ ((g + 0x0c#64) ↦₃₂ 0#32) ∗
  ((g + 0x10#64) ↦₆₄ 0#64) ∗ ((g + 0x18#64) ↦₆₄ 1024#64) ∗
  ((g + 0x20#64) ↦₆₄ bufPtr) ∗ ((g + 0x28#64) ↦₆₄ 0#64) ∗
  ((g + 0x30#64) ↦₈ 0#8) ∗ memRegion (g + 0x31#64) 7

private theorem hbStdoutInitFields_to_inv {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P addrs lim) (γ : GhostName) {bufPtr : BitVec 64}
    (hne : bufPtr ≠ 0#64) (hal : 16 ∣ bufPtr.toNat) (_hfit : bufPtr.toNat + 1024 < 2 ^ 64) :
    hbStdoutInitFields C.std.stdoutGlobalAddr bufPtr ∗
      ((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 0#32) ∗
      M.Block γ bufPtr 1024 ∗ memRegion bufPtr 1024 ⊢
      HbStdoutInv C M γ true := by
  have hblk :
      hbStdoutInitFields C.std.stdoutGlobalAddr bufPtr ∗
        ((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 0#32) ∗
        M.Block γ bufPtr 1024 ∗ memRegion bufPtr 1024 ⊢
      M.Block γ bufPtr 1024 ∗
        (hbStdoutInitFields C.std.stdoutGlobalAddr bufPtr ∗
         ((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 0#32) ∗ memRegion bufPtr 1024) := by
    sep_entail
  refine Entails.trans hblk (Entails.trans (sepConj_mono_left (M.block_userVa γ bufPtr 1024)) ?_)
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hva
  dsimp only [HbStdoutInv, hbStdoutInitFields]
  simp only [↓reduceIte]
  refine Entails.sepExists_right bufPtr ?_
  rw [sepConj_assoc, pure_sepConj_of_true ⟨hne, hal, hva⟩]
  sep_entail

theorem sepWP_cpu_seg {P : Program} {mid_pc target_pc : BitVec 64} {s0 : State}
    {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hext : ∀ pc, P.externAt? pc = none)
    (hseg : SepWP (P.withSvc noSyscalls) mid_pc s0 Pre
      (fun sm Pm => CpuAuxPreserved s0 sm ∧
        (FmtPureStatePreserved s0 sm → SepWP P target_pc sm Pm post oom))) :
    SepWP P target_pc s0 Pre post oom :=
  SepWP.seq_noSyscalls hext hseg fun _ _ _ _ hpure hcont => hcont hpure

theorem heap_eq {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) {γ : GhostName} {lc blk : Nat} {s1 s2 : State}
    (hbrk : s2.brk = s1.brk) (hbs : s2.brkStart = s1.brkStart)
    (hpm : s2.physMemAvail = s1.physMemAvail) (hperm : ∀ a, s2.mem.perm a = s1.mem.perm a) :
    M.Heap γ lc blk s1 = M.Heap γ lc blk s2 :=
  Entails.antisymm
    (M.heap_transport hbrk hbs hpm hperm)
    (M.heap_transport hbrk.symm hbs.symm hpm.symm (fun a => (hperm a).symm))

theorem heap_eq_of_std {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) {γ : GhostName} {lc blk : Nat} {s1 s2 : State}
    (h : StdStatePreserved s1 s2) :
    M.Heap γ lc blk s1 = M.Heap γ lc blk s2 :=
  heap_eq M h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2

private theorem heap_eq_of_fmtIo {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) {γ : GhostName} {lc blk : Nat} {s1 s2 : State}
    (h : FmtIoStatePreserved s1 s2) :
    M.Heap γ lc blk s1 = M.Heap γ lc blk s2 :=
  heap_eq M h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1

private theorem hbStdoutOutlinedOnceCall_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc sp1 onceAddr vtableAddr v8 v9 v10 u0 u1 u2 : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C)
    (hext : ∀ pc, P.externAt? pc = none)
    (hpc : s.pc = C.outlinedOnceCallAddr) (hrun : s.status = .Running)
    (hsp : s.sp = sp1) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = onceAddr) (hx3 : s.readReg64 .x3 = vtableAddr)
    (hx8 : s.readReg64 .x8 = v8) (hx9 : s.readReg64 .x9 = v9) (hx10 : s.readReg64 .x10 = v10)
    (hnext : ∀ sf : State, sf.pc = C.std.onceCallAddr → sf.status = .Running →
      sf.sp = sp1 → sf.spAligned = true → sf.readReg64 Reg.lr = ret_pc →
      CalleeSavedPreserved s sf → StdStatePreserved s sf →
      sf.readReg64 .x0 = onceAddr → sf.readReg64 .x1 = 1#64 →
      sf.readReg64 .x2 = sp1 + 16#64 → sf.readReg64 .x3 = vtableAddr →
      SepWP P target_pc sf
        ((sp1 ↦₆₄ v8) ∗ ((sp1 + 8#64) ↦₆₄ v9) ∗ ((sp1 + 16#64) ↦₆₄ v10) ∗ F) post oom) :
    SepWP P target_pc s
      ((sp1 ↦₆₄ u0) ∗ ((sp1 + 8#64) ↦₆₄ u1) ∗ ((sp1 + 16#64) ↦₆₄ u2) ∗ F) post oom := by
  subst hsp
  refine sepWP_cpu_seg (mid_pc := C.std.onceCallAddr) hext ?_
  have hchunk := (hc.withSvc noSyscalls).outlinedOnceCall
  unpack_stdout_code hbStdoutOutlinedOnceCallChunks hchunk
  have hx0' : s.readReg64 (.gpr 0#5) = onceAddr := hx0
  have hx3' : s.readReg64 (.gpr 3#5) = vtableAddr := hx3
  have hx8' : s.readReg64 (.gpr 8#5) = v8 := hx8
  have hx9' : s.readReg64 (.gpr 9#5) = v9 := hx9
  have hx10' : s.readReg64 (.gpr 10#5) = v10 := hx10
  have hlr' : s.readReg64 (.gpr 30#5) = ret_pc := hlr
  wp_steps; wp_steps; norm_jmp
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
    ⟨by simp [CpuAuxPreserved.refl s], fun hpure => ?_⟩
  refine SepWP.weaken_pre (by sep_frame)
    (hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a
      (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align) wp_a
      (by close_cs) hpure.1 wp_a wp_a wp_a wp_a)

private theorem hbStdoutInitClosure_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    {target_pc ret_c sp_c dataPtr pairPtr : BitVec 64} {lc blk : Nat} {e0 : BitVec 32}
    {sc : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C)
    (hext : ∀ pc, P.externAt? pc = none)
    (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64)
    (hreq : 1024 ≤ lim.maxReq)
    (hcost : lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost)
    (hblk : blk + 1 ≤ lim.maxPeakBlocks)
    (hpc : sc.pc = C.stdoutInitClosureAddr) (hrun : sc.status = .Running)
    (hsp : sc.sp = sp_c) (hsp_align : sc.spAligned = true)
    (hlr : sc.readReg64 Reg.lr = ret_c) (hx0 : sc.readReg64 .x0 = dataPtr)
    (hnext : ∀ (sr : State) (bufPtr : BitVec 64) (e1 : BitVec 32),
      sr.pc = ret_c → sr.status = .Running → sr.sp = sp_c →
      CalleeSavedPreserved sc sr →
      sr.fs = sc.fs → sr.trace = sc.trace → sr.sigActions = sc.sigActions → sr.tpidrEl0 = sc.tpidrEl0 →
      bufPtr ≠ 0#64 → 16 ∣ bufPtr.toNat → bufPtr.toNat + 1024 < 2 ^ 64 →
      SepWP P target_pc sr
        ((dataPtr ↦₆₄ pairPtr) ∗ (pairPtr ↦₆₄ 0#64) ∗
         hbStdoutInitFields C.std.stdoutGlobalAddr bufPtr ∗
         M.Heap γ (lc + mallocngBlockCost 1024) (blk + 1) sr ∗
         M.Block γ bufPtr 1024 ∗ memRegion bufPtr 1024 ∗
         (muslErrnoAddr sr ↦₃₂ e1) ∗ stackAt sp_c (MallocngStackBytes + 32) ∗ F) post oom) :
    SepWP P target_pc sc
      ((dataPtr ↦₆₄ pairPtr) ∗ (pairPtr ↦₆₄ C.std.stdoutGlobalAddr) ∗
       (C.std.stdoutGlobalAddr ↦ₛ List.replicate 56 0#8) ∗
       M.Heap γ lc blk sc ∗ (muslErrnoAddr sc ↦₃₂ e0) ∗
       stackAt sp_c (MallocngStackBytes + 32) ∗ F) post oom := by
  subst hsp
  let g := C.std.stdoutGlobalAddr
  have hgnz : (g == 0#64) = false := beq_false_of_ne hg_nz
  have hx0' : sc.readReg64 (.gpr 0#5) = dataPtr := hx0
  have hlr' : sc.readReg64 (.gpr 30#5) = ret_c := hlr
  rw [show MallocngStackBytes + 32 = MallocngStackBytes + 8 * 4 from rfl,
      stackAt_split_cells sc.sp MallocngStackBytes 4 (by decide)]
  simp only [Nat.reduceMul]; cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro c3; apply SepWP.exists_left; intro c2
  apply SepWP.exists_left; intro c1; apply SepWP.exists_left; intro c0
  refine sepWP_cpu_seg (mid_pc := C.mallocng.mallocAddr) hext ?_
  have hchunk := (hc.withSvc noSyscalls).stdoutInitClosure
  unpack_stdout_code hbStdoutInitClosureChunks hchunk
  wp_steps; norm_jmp; wp_steps; wp_steps; norm_jmp; wp_steps; norm_jmp; wp_steps; norm_jmp
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
    ⟨by simp [CpuAuxPreserved.refl sc], fun hpure0 => ?_⟩
  refine SepWP.call_subroutine_frame (M.malloc_ok γ) (x := (lc, blk, 1024, e0))
    (ret_pc := C.stdoutInitClosureAddr + 0x2c#64)
    (F := (dataPtr ↦₆₄ pairPtr) ∗ (pairPtr ↦₆₄ 0#64) ∗ (g ↦ₛ List.replicate 56 0#8) ∗
          ((sc.sp - 32#64) ↦₆₄ sc.readReg64 (.gpr 29#5)) ∗ ((sc.sp - 24#64) ↦₆₄ ret_c) ∗
          ((sc.sp - 16#64) ↦₆₄ sc.readReg64 (.gpr 19#5)) ∗ ((sc.sp - 8#64) ↦₆₄ c0) ∗ F)
    wp_a (by simp [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm]
        simpa [BitVec.sub_eq_add_neg] using sc.spAligned_sub 32#64 hsp_align)
    wp_a ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_
    (by wp_close_oom_default)
  · intro R hm
    rw [heap_eq_of_std M hpure0.1] at hm
    dsimp only [muslErrnoAddr] at hm ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm], hreq, hcost, hblk⟩, ?_⟩
    simp only [wp_norm, arm64_norm] at hm ⊢
    exact (by sep_entail : _ → _) hm
  · intro s1 hpc1 hrun1 hsp1 hcs1
    dsimp only
    rw [sepConj_assoc]
    apply SepWP.pure_elim
    rintro ⟨hmal, hret_ne, hret_al, hret_fit⟩
    let bufPtr := s1.readReg64 (.gpr 0#5)
    have hret_nz : (bufPtr == 0#64) = false := beq_false_of_ne hret_ne
    have hx19_1 : s1.readReg64 (.gpr 19#5) = g := by
      rw [hcs1.1]; simp [wp_norm, arm64_norm]; rfl
    have hsp1_eq : s1.sp = sc.sp - 32#64 := by rw [hsp1]; exact wp_a
    have hsp1_al : s1.spAligned = true := by
      simp only [State.spAligned, hsp1_eq]; exact sc.spAligned_sub 32#64 hsp_align
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro e1
    refine SepWP.weaken_pre (P' := (g ↦ₛ List.replicate 56 0#8) ∗ ?Rest) (by sep_frame) ?_
    refine SepWP.weaken_pre (sepConj_mono_left (hbStdoutZeroBytes_to_fields g)) ?_
    simp only [sepExists_sepConj_left]
    iterate 7 (apply SepWP.exists_elim; intro _)
    refine sepWP_cpu_seg (mid_pc := ret_c) hext ?_
    have hchunk2 := (hc.withSvc noSyscalls).stdoutInitClosure
    unpack_stdout_code hbStdoutInitClosureChunks hchunk2
    wp_steps
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun1])
      ⟨by simp [CpuAuxPreserved.refl s1], fun hpure2 => ?_⟩
    refine SepWP.weaken_pre_frame
      (fun R hm => by
        rw [heap_eq_of_std M hpure2.1] at hm
        have hsp_split : ((g + 0x08#64) ↦₆₄ 0#64) =
            ((g + 0x08#64) ↦₃₂ 0#32) ∗ ((g + 0x0c#64) ↦₃₂ 0#32) := by
          simpa [show (g + 0x08#64) + 4#64 = g + 0x0c#64 by bv_lin] using
            pointsTo64_split32' (g + 0x08#64) 0#64
        rw [hsp_split] at hm
        have htp_eq : s1.tpidrEl0 = sc.tpidrEl0 := hmal.2.2.2.1
        dsimp only [hbStdoutInitFields, muslErrnoAddr] at hm ⊢
        rw [show MallocngStackBytes + 32 = MallocngStackBytes + 8 * 4 from rfl,
            stackAt_split_cells sc.sp MallocngStackBytes 4 (by decide)]
        simp only [wp_norm, arm64_norm, htp_eq] at hm ⊢
        exact (by repack_cells : _ → _) hm)
      (hnext _ bufPtr e1 wp_a (by simp [wp_norm, arm64_norm, hrun1]) wp_a
        (by unpack_cs hcs1; close_cs)
        (hpure2.1.1.trans (hmal.1.trans hpure0.1.1))
        (hpure2.1.2.1.trans (hmal.2.1.trans hpure0.1.2.1))
        (hpure2.1.2.2.2.1.trans (hmal.2.2.1.trans hpure0.1.2.2.2.1))
        (hpure2.1.2.2.1.trans (hmal.2.2.2.1.trans hpure0.1.2.2.1))
        hret_ne hret_al hret_fit)

private theorem pointsTo8_combine32_sub (sp o0 o1 o2 o3 : BitVec 64) (b0 b1 b2 b3 : BitVec 8) (R : SepProp)
    (h1 : o0 - 1#64 = o1 := by rfl) (h2 : o0 - 2#64 = o2 := by rfl) (h3 : o0 - 3#64 = o3 := by rfl) :
    ((sp - o0) ↦₈ b0) ∗ ((sp - o1) ↦₈ b1) ∗ ((sp - o2) ↦₈ b2) ∗ ((sp - o3) ↦₈ b3) ∗ R =
      ((sp - o0) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ R := by
  subst h1 h2 h3
  simpa only [sepConj_assoc, show sp - o0 + 1#64 = sp - (o0 - 1#64) by bv_lin,
    show sp - o0 + 2#64 = sp - (o0 - 2#64) by bv_lin, show sp - o0 + 3#64 = sp - (o0 - 3#64) by bv_lin]
    using congrArg (· ∗ R) (pointsTo8_quad (sp - o0) b0 b1 b2 b3)

private theorem pointsTo32_split8_sub (sp o0 o1 o2 o3 : BitVec 64) (v : BitVec 32) (R : SepProp)
    (h1 : o0 - 1#64 = o1 := by rfl) (h2 : o0 - 2#64 = o2 := by rfl) (h3 : o0 - 3#64 = o3 := by rfl) :
    ((sp - o0) ↦₃₂ v) ∗ R =
      ((sp - o0) ↦₈ v.extractLsb' 0 8) ∗ ((sp - o1) ↦₈ v.extractLsb' 8 8) ∗
      ((sp - o2) ↦₈ v.extractLsb' 16 8) ∗ ((sp - o3) ↦₈ v.extractLsb' 24 8) ∗ R := by
  rw [pointsTo8_combine32_sub sp o0 o1 o2 o3 _ _ _ _ R h1 h2 h3,
      show v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v by bv_bits]

private theorem combine_cell_byte4_sat (sp o8 o4 o3 o2 o1 : BitVec 64) {lo : BitVec 32} {b0 b1 b2 b3 : BitVec 8}
    {m : Memory} {P R : SepProp} (hm : m ⊨ P)
    (hf : P ⊢ (((sp - o8) ↦₃₂ lo) ∗ ((sp - o4) ↦₈ b0) ∗ ((sp - o3) ↦₈ b1) ∗
               ((sp - o2) ↦₈ b2) ∗ ((sp - o1) ↦₈ b3)) ∗ R := by sep_frame)
    (h4 : o8 - 4#64 = o4 := by rfl) (h1 : o4 - 1#64 = o3 := by rfl)
    (h2 : o4 - 2#64 = o2 := by rfl) (h3 : o4 - 3#64 = o1 := by rfl) :
    m ⊨ (((sp - o8) ↦₆₄ ((b3 ++ b2 ++ b1 ++ b0) ++ lo)) ∗ R) := by
  have hm' := Satisfies.mono hf hm
  rwa [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
       pointsTo8_combine32_sub sp o4 o3 o2 o1 b0 b1 b2 b3 R h1 h2 h3,
       pointsTo32_combine64_sub sp o8 o4 lo _ R h4] at hm'

private theorem hbOnceCallMalloc_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    {target_pc ret_pc sp1 : BitVec 64} {lc blk : Nat} {e0 : BitVec 32} {haveLse : BitVec 8}
    {s_oc : State} {G : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C) (honce : HbOnceCallCode P C)
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hext : ∀ pc, P.externAt? pc = none)
    (hal_g38 : MemWidth.isAligned .W32 (C.std.stdoutGlobalAddr + 0x38#64) = true)
    (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64)
    (hreq : 1024 ≤ lim.maxReq)
    (hcost : lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost)
    (hblk : blk + 1 ≤ lim.maxPeakBlocks)
    (hpc : s_oc.pc = C.std.onceCallAddr) (hrun : s_oc.status = .Running)
    (hsp : s_oc.sp = sp1) (hsp_al : s_oc.spAligned = true) (hlr : s_oc.readReg64 Reg.lr = ret_pc)
    (hx0 : s_oc.readReg64 .x0 = C.std.stdoutGlobalAddr + 0x38#64)
    (hx1 : s_oc.readReg64 .x1 = 1#64)
    (hx2 : s_oc.readReg64 .x2 = sp1 + 16#64)
    (hx3 : s_oc.readReg64 .x3 = C.stdoutInitVtableAddr)
    (hnext : ∀ (sf : State) (bufPtr : BitVec 64) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp1 → CalleeSavedPreserved s_oc sf →
      sf.fs = s_oc.fs → sf.trace = s_oc.trace → sf.sigActions = s_oc.sigActions → sf.tpidrEl0 = s_oc.tpidrEl0 →
      bufPtr ≠ 0#64 → 16 ∣ bufPtr.toNat → bufPtr.toNat + 1024 < 2 ^ 64 →
      SepWP P target_pc sf
        (((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 0#32) ∗
         (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
         StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
         memRegion (sp1 - 96#64) 96 ∗
         ((sp1 + 16#64) ↦₆₄ sp1) ∗ (sp1 ↦₆₄ 0#64) ∗
         hbStdoutInitFields C.std.stdoutGlobalAddr bufPtr ∗
         M.Heap γ (lc + mallocngBlockCost 1024) (blk + 1) sf ∗
         M.Block γ bufPtr 1024 ∗ memRegion bufPtr 1024 ∗
         (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt (sp1 - 96#64) (MallocngStackBytes + 32) ∗ G) post oom) :
    SepWP P target_pc s_oc
      (((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 3#32) ∗
       (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
       StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
       memRegion (sp1 - 96#64) 96 ∗
       ((sp1 + 16#64) ↦₆₄ sp1) ∗ (sp1 ↦₆₄ C.std.stdoutGlobalAddr) ∗
       (C.std.stdoutGlobalAddr ↦ₛ List.replicate 56 0#8) ∗
       M.Heap γ lc blk s_oc ∗ (muslErrnoAddr s_oc ↦₃₂ e0) ∗
       stackAt (sp1 - 96#64) (MallocngStackBytes + 32) ∗ G) post oom := by
  subst hsp
  let g := C.std.stdoutGlobalAddr
  have h96 : memRegion (s_oc.sp - 96#64) 96 = cells (s_oc.sp - 96#64) 12 :=
    stackAt_eq_cells s_oc.sp 12
  unfold StdVtableRo
  rw [h96]; unpack_cells 12
  rw [pointsTo64_split32_sub s_oc.sp 88#64 84#64, pointsTo32_split8_sub s_oc.sp 84#64 83#64 82#64 81#64]
  have hx0' : s_oc.readReg64 (.gpr 0#5) = g + 0x38#64 := hx0
  have hx1' : s_oc.readReg64 (.gpr 1#5) = 1#64 := hx1
  have hx2' : s_oc.readReg64 (.gpr 2#5) = s_oc.sp + 16#64 := hx2
  have hx3' : s_oc.readReg64 (.gpr 3#5) = C.stdoutInitVtableAddr := hx3
  have hlr' : s_oc.readReg64 (.gpr 30#5) = ret_pc := hlr
  refine sepWP_cpu_seg (mid_pc := C.std.cas4AcqAddr) hext ?_
  have honceNo := codeChunks_withSvc noSyscalls honce
  unpack_stdout_code hbOnceCallPostChunks honceNo
  wp_steps
  refine step_ldar32_words C.std.onceCallAddr _ 7 (C.std.onceCallAddr + 0x20#64)
    hal_g38 (rt' := .gpr 22#5) (hnext := ?_)
  wp_steps; wp_steps; norm_jmp
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
    ⟨by simp [CpuAuxPreserved.refl s_oc], fun hpure0 => ?_⟩
  refine call_stdCas4 hcas4 (haveLse := haveLse) (ptr := g + 0x38#64) (v0 := 3#32) (exp := 3#32) (new := 1#32)
    (ret_pc := C.std.onceCallAddr + 0x64#64) (F := ?_) (by sep_frame)
    (fun s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hstd1 => ?_) (halign := hal_g38)
  simp only [beq_self_eq_true, ↓reduceIte]
  have hx19_1 : s1.readReg64 (.gpr 19#5) = g + 0x38#64 := by rw [hcs1.1]; simp [g, wp_norm, arm64_norm]
  have hx20_1 : s1.readReg64 (.gpr 20#5) = s_oc.sp + 16#64 := by rw [hcs1.2.1]; simp [wp_norm, arm64_norm]
  have hx21_1 : s1.readReg64 (.gpr 21#5) = C.stdoutInitVtableAddr := by rw [hcs1.2.2.1]; simp [wp_norm, arm64_norm]
  have hx22_1 : BitVec.truncate 32 (s1.readReg64 (.gpr 22#5)) = 3#32 := by
    have := hcs1.readReg32_x22; simp [wp_norm, arm64_norm] at this; exact this
  have hx23_1 : BitVec.truncate 32 (s1.readReg64 (.gpr 23#5)) = 3#32 := by
    have := hcs1.readReg32_x23; simp [wp_norm, arm64_norm] at this; exact this
  have hsp1_eq : s1.sp = s_oc.sp - 0x60#64 := by rw [hsp1]; exact wp_a
  have hsp1_al : s1.spAligned = true := by
    simp only [State.spAligned, hsp1_eq]; exact s_oc.spAligned_sub 0x60#64 hsp_al
  refine sepWP_cpu_seg (mid_pc := C.stdoutInitClosureAddr) hext ?_
  have honceNo1 := codeChunks_withSvc noSyscalls honce
  unpack_stdout_code hbOnceCallPostChunks honceNo1
  wp_steps; wp_steps
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun1])
    ⟨by simp [CpuAuxPreserved.refl s1], fun hpure1 => ?_⟩
  have hstd_to_clos : StdStatePreserved s_oc _ :=
    StdStatePreserved.trans hpure0.1 (StdStatePreserved.trans hstd1 hpure1.1)
  refine SepWP.weaken_pre
    (P' := ((s_oc.sp + 16#64) ↦₆₄ s_oc.sp) ∗ (s_oc.sp ↦₆₄ g) ∗
           (g ↦ₛ List.replicate 56 0#8) ∗ M.Heap γ lc blk _ ∗ (muslErrnoAddr _ ↦₃₂ e0) ∗
           stackAt (s_oc.sp - 96#64) (MallocngStackBytes + 32) ∗ ?F_clos)
    (by
      rw [heap_eq_of_std M hstd_to_clos]
      dsimp only [muslErrnoAddr]
      rw [← hstd_to_clos.2.2.1]
      sep_frame)
    (hbStdoutInitClosure_wp (ret_c := C.std.onceCallAddr + 0x11c#64)
      (sp_c := s_oc.sp - 96#64) (dataPtr := s_oc.sp + 16#64) (pairPtr := s_oc.sp)
      M γ hc hext hg_nz hreq hcost hblk wp_a
      (by simp [wp_norm, arm64_norm, hrun1])
      (by simp [wp_norm, arm64_norm, hsp1_eq])
      (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp1_al)
      wp_a wp_a fun s2 bufPtr e1 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 hsig2 htp2 hbuf_ne hbuf_al hbuf_fit => ?_)
  have hx19_2 : s2.readReg64 (.gpr 19#5) = g + 0x38#64 := by
    rw [hcs2.1]; simp [wp_norm, arm64_norm, hx19_1]
  have hsp2_eq : s2.sp = s_oc.sp - 0x60#64 := hsp2
  have hsp2_al : s2.spAligned = true := by
    simp only [State.spAligned, hsp2_eq]; exact s_oc.spAligned_sub 0x60#64 hsp_al
  refine sepWP_cpu_seg (mid_pc := C.std.swp4RelAddr) hext ?_
  have honceNo2 := codeChunks_withSvc noSyscalls honce
  unpack_stdout_code hbOnceCallPostChunks honceNo2
  wp_steps; norm_jmp
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun2])
    ⟨by simp [CpuAuxPreserved.refl s2], fun hpure2 => ?_⟩
  refine call_stdSwp4 hswp4 (haveLse := haveLse) (ptr := g + 0x38#64) (v0 := 1#32) (new := 0#32)
    (ret_pc := C.std.onceCallAddr + 0x128#64) (F := ?_) (by sep_frame)
    (fun s3 hpc3 hrun3 hsp3 hcs3 hx0_3 hstd3 => ?_) (halign := hal_g38)
  have hx0_3' : s3.readReg64 (.gpr 0#5) = 1#64 := hx0_3
  have hsp3_eq : s3.sp = s_oc.sp - 0x60#64 := by rw [hsp3]; simp [wp_norm, arm64_norm, hsp2_eq]
  have hsp3_al : s3.spAligned = true := by
    simp only [State.spAligned, hsp3_eq]; exact s_oc.spAligned_sub 0x60#64 hsp_al
  refine sepWP_cpu_seg (mid_pc := ret_pc) hext ?_
  have honceNo3 := codeChunks_withSvc noSyscalls honce
  unpack_stdout_code hbOnceCallPostChunks honceNo3
  wp_steps; wp_steps
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun3])
    ⟨by simp [CpuAuxPreserved.refl s3], fun hpure3 => ?_⟩
  have hstd_after : StdStatePreserved s2 _ :=
    StdStatePreserved.trans hpure2.1 (StdStatePreserved.trans hstd3 hpure3.1)
  have hcont := hnext _ bufPtr e1 wp_a (by simp [wp_norm, arm64_norm, hrun3]) wp_a
    (by unpack_cs hcs1; unpack_cs hcs2; unpack_cs hcs3; close_cs)
    (hstd_after.1.trans (hfs2.trans hstd_to_clos.1))
    (hstd_after.2.1.trans (htr2.trans hstd_to_clos.2.1))
    (hstd_after.2.2.2.1.trans (hsig2.trans hstd_to_clos.2.2.2.1))
    (hstd_after.2.2.1.trans (htp2.trans hstd_to_clos.2.2.1))
    hbuf_ne hbuf_al hbuf_fit
  refine SepWP.weaken_pre_frame (fun R hm => ?_) hcont
  replace hm := combine_cell_byte4_sat s_oc.sp 88#64 84#64 83#64 82#64 81#64 hm
  rw [heap_eq_of_std M hstd_after] at hm
  dsimp only [muslErrnoAddr] at hm ⊢
  rw [← hstd_after.2.2.1] at hm
  unfold StdVtableRo
  rw [h96]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  sep_entail

theorem hbStdoutInit_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) (init : Bool)
    {target_pc ret_pc sp0 : BitVec 64} {lc blk : Nat} {e0 : BitVec 32} {haveLse : BitVec 8}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C) (honce : HbOnceCallCode P C)
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hv : C.Valid) (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    (hbudget : init = false → 1024 ≤ lim.maxReq ∧
      lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost ∧ blk + 1 ≤ lim.maxPeakBlocks)
    (hpc : s.pc = C.stdoutInitAddr) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 → CalleeSavedPreserved s sf →
      sf.fs = s.fs → sf.trace = s.trace → sf.sigActions = s.sigActions → sf.tpidrEl0 = s.tpidrEl0 →
      SepWP P target_pc sf
        ((HbStdoutInv C M γ true ∗
          (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
          StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
          M.Heap γ (if init then lc else lc + mallocngBlockCost 1024) (if init then blk else blk + 1) sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗
          stackAt sp0 4288) ∗ F) post oom) :
    SepWP P target_pc s
      ((HbStdoutInv C M γ init ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
        M.Heap γ lc blk s ∗
        (muslErrnoAddr s ↦₃₂ e0) ∗
        stackAt sp0 4288) ∗ F) post oom := by
  subst hsp
  let g := C.std.stdoutGlobalAddr
  obtain ⟨_, _, hal_g38, _⟩ := hbValid_stdout_align hv
  have hlr' : s.readReg64 (.gpr 30#5) = ret_pc := hlr
  cases init with
  | true =>
    simp only [HbStdoutInv, ↓reduceIte, sepExists_sepConj_left]
    apply SepWP.exists_elim; intro bufPtr
    simp only [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hbuf_ne, hbuf_al, hbuf_fit⟩
    refine sepWP_cpu_seg (mid_pc := ret_pc) hext ?_
    have hchunk := (hc.withSvc noSyscalls).stdoutInit
    unpack_stdout_code hbStdoutInitChunks hchunk
    wp_steps
    refine step_ldar32_words (C.stdoutInitAddr + 0x08#64) _ 0 (C.stdoutInitAddr + 0x0c#64) hal_g38 (hnext := ?_)
    wp_steps
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
      ⟨by simp [CpuAuxPreserved.refl s], fun hpure => ?_⟩
    refine SepWP.weaken_pre_frame
      (fun R hm => by
        rw [heap_eq_of_std M hpure.1] at hm
        dsimp only [HbStdoutInv, muslErrnoAddr] at hm ⊢
        rw [← hpure.1.2.2.1] at hm
        simp only [↓reduceIte, sepExists_sepConj_left]
        refine Satisfies.mono (Entails.sepExists_right bufPtr ?_) hm
        rw [sepConj_assoc, pure_sepConj_of_true ⟨hbuf_ne, hbuf_al, hbuf_fit⟩]
        sep_entail)
      (hnext _ e0 wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a (by close_cs)
        hpure.1.1 hpure.1.2.1 hpure.1.2.2.2.1 hpure.1.2.2.1)
  | false =>
    obtain ⟨hreq, hcost, hblk⟩ := hbudget rfl
    simp only [HbStdoutInv, Bool.false_eq_true, ↓reduceIte]
    rw [show (4288 : Nat) = 4240 + 8 * 6 from rfl, stackAt_split_cells s.sp 4240 6 (by decide),
        show (4240 : Nat) = ((MallocngStackBytes + 32) + 96) + 16 from rfl,
        stackAt_split_bottom (s.sp - 48#64) ((MallocngStackBytes + 32) + 96) 16 (by decide),
        stackAt_region (s.sp - 48#64) (MallocngStackBytes + 32) 96 (by decide)]
    unpack_cells 6
    refine sepWP_cpu_seg (mid_pc := C.outlinedOnceCallAddr) hext ?_
    have hchunk := (hc.withSvc noSyscalls).stdoutInit
    unpack_stdout_code hbStdoutInitChunks hchunk
    have hfn72 := (hc.withSvc noSyscalls).outlinedFn72
    unpack_stdout_code hbOutlinedFn72Chunks hfn72
    wp_steps
    refine step_ldar32_words (C.stdoutInitAddr + 0x08#64) _ 0 (C.stdoutInitAddr + 0x0c#64) hal_g38 (hnext := ?_)
    wp_steps; wp_steps; wp_steps; wp_steps; norm_jmp; wp_steps; wp_steps; wp_steps; wp_steps; wp_steps; norm_jmp
    conv => repeat rw [bv64_add_sub_cancel']
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
      ⟨by simp [CpuAuxPreserved.refl s], fun hpure0 => ?_⟩
    have hp8 : s.sp - 40#64 = (s.sp - 48#64) + 8#64 := by bv_lin
    have hp16 : s.sp - 32#64 = (s.sp - 48#64) + 16#64 := by bv_lin
    rw [hp8, hp16]
    refine SepWP.weaken_pre
      (P' := ((s.sp - 48#64) ↦₆₄ _) ∗ (((s.sp - 48#64) + 8#64) ↦₆₄ _) ∗
             (((s.sp - 48#64) + 16#64) ↦₆₄ _) ∗ ?F_out)
      (by sep_frame)
      (hbStdoutOutlinedOnceCall_wp (ret_pc := C.stdoutInitAddr + 0x44#64)
        (sp1 := s.sp - 48#64) (onceAddr := g + 0x38#64) (vtableAddr := C.stdoutInitVtableAddr)
        (v8 := g) (v9 := s.sp - 17#64) (v10 := s.sp - 48#64)
        hc hext wp_a (by simp [wp_norm, arm64_norm, hrun]) wp_a
        (by simp only [State.spAligned, wp_norm, arm64_norm]
            simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 48#64 hsp_align)
        wp_a wp_a wp_a wp_a wp_a wp_a
        fun s_oc hpc_oc hrun_oc hsp_oc hsp_oc_al hlr_oc hcs_oc hstd_oc hx0_oc hx1_oc hx2_oc hx3_oc => ?_)
    have hstd_oc' : StdStatePreserved s s_oc := StdStatePreserved.trans hpure0.1 hstd_oc
    refine SepWP.weaken_pre
      (P' := ((g + 0x38#64) ↦₃₂ 3#32) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
             StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
             memRegion ((s.sp - 48#64) - 96#64) 96 ∗
             (((s.sp - 48#64) + 16#64) ↦₆₄ (s.sp - 48#64)) ∗ ((s.sp - 48#64) ↦₆₄ g) ∗
             (g ↦ₛ List.replicate 56 0#8) ∗ M.Heap γ lc blk s_oc ∗ (muslErrnoAddr s_oc ↦₃₂ e0) ∗
             stackAt ((s.sp - 48#64) - 96#64) (MallocngStackBytes + 32) ∗ ?G_oc)
      (by
        rw [heap_eq_of_std M hstd_oc']
        dsimp only [muslErrnoAddr]
        rw [← hstd_oc'.2.2.1]
        sep_frame)
      (hbOnceCallMalloc_wp M γ hc honce hcas4 hswp4 hext hal_g38 hg_nz hreq hcost hblk
        hpc_oc hrun_oc hsp_oc hsp_oc_al hlr_oc hx0_oc hx1_oc hx2_oc hx3_oc
        fun s_ret bufPtr e1 hpc_r hrun_r hsp_r hcs_r hfs_r htr_r hsig_r htp_r hbuf_ne hbuf_al hbuf_fit => ?_)
    have hsp_r_al : s_ret.spAligned = true := by
      simp only [State.spAligned, hsp_r]; exact s.spAligned_sub 48#64 hsp_align
    rw [← hp8, ← hp16]
    refine sepWP_cpu_seg (mid_pc := ret_pc) hext ?_
    have hchunk2 := (hc.withSvc noSyscalls).stdoutInit
    unpack_stdout_code hbStdoutInitChunks hchunk2
    wp_steps
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun_r])
      ⟨by simp [CpuAuxPreserved.refl s_ret], fun hpure_end => ?_⟩
    have hcont := hnext _ e1 wp_a (by simp [wp_norm, arm64_norm, hrun_r])
      (by simp [wp_norm, arm64_norm])
      (by unpack_cs hcs_oc; unpack_cs hcs_r; close_cs)
      (hpure_end.1.1.trans (hfs_r.trans hstd_oc'.1))
      (hpure_end.1.2.1.trans (htr_r.trans hstd_oc'.2.1))
      (hpure_end.1.2.2.2.1.trans (hsig_r.trans hstd_oc'.2.2.2.1))
      (hpure_end.1.2.2.1.trans (htp_r.trans hstd_oc'.2.2.1))
    refine SepWP.weaken_pre_frame (fun R hm => ?_) hcont
    rw [heap_eq_of_std M hpure_end.1] at hm
    dsimp only [muslErrnoAddr] at hm ⊢
    rw [← hpure_end.1.2.2.1] at hm
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hm1 : _ ⊨ (hbStdoutInitFields g bufPtr ∗ ((g + 0x38#64) ↦₃₂ 0#32) ∗
        M.Block γ bufPtr 1024 ∗ memRegion bufPtr 1024) ∗ _ := (by sep_frame : _ → _) hm
    clear hm
    replace hm1 := Satisfies.mono
      (sepConj_mono_left (hbStdoutInitFields_to_inv C M γ hbuf_ne hbuf_al hbuf_fit)) hm1
    rw [show (4288 : Nat) = 4240 + 8 * 6 from rfl, stackAt_split_cells s.sp 4240 6 (by decide),
        show (4240 : Nat) = ((MallocngStackBytes + 32) + 96) + 16 from rfl,
        stackAt_split_bottom (s.sp - 48#64) ((MallocngStackBytes + 32) + 96) 16 (by decide),
        stackAt_region (s.sp - 48#64) (MallocngStackBytes + 32) 96 (by decide)]
    repack_cells

/-- Total-correctness `Spec` for `OnceLock<Stdout>::initialize` (`C.stdoutInitAddr`). -/
def hbStdoutInitSpec {P : Program} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) :
    Spec (Bool × Nat × Nat × BitVec 32 × BitVec 8) where
  pre := fun (init, lc, blk, e0, haveLse) s0 =>
    ⌜init = false → 1024 ≤ lim.maxReq ∧
      lc + mallocngBlockCost 1024 ≤ lim.maxPeakCost ∧ blk + 1 ≤ lim.maxPeakBlocks⌝ ∗
    HbStdoutInv C M γ init ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt s0.sp 4288
  post := fun (init, lc, blk, _, haveLse) s0 sf =>
    ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗
    HbStdoutInv C M γ true ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    M.Heap γ (if init then lc else lc + mallocngBlockCost 1024) (if init then blk else blk + 1) sf ∗
    (∃∗ e1 : BitVec 32, muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt s0.sp 4288

theorem hbStdoutInit_ok {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    (hc : HbStdoutCode P C) (honce : HbOnceCallCode P C)
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hv : C.Valid) (hg_nz : C.std.stdoutGlobalAddr ≠ 0#64)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.stdoutInitAddr (hbStdoutInitSpec C M γ) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨init, lc, blk, e0, haveLse⟩ R s0 hpc hrun hpre hsp
  dsimp only [hbStdoutInitSpec] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hbudget, hmem⟩
  refine ⟨(HbStdoutInv C M γ init ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
    StdVtableRo C.stdoutInitVtableAddr C.stdoutInitShimAddr C.stdoutInitClosureAddr ∗
    M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt s0.sp 4288) ∗ emp,
    by simpa [sepConj_emp, sepConj_assoc] using hmem, ?_⟩
  refine hbStdoutInit_wp M γ init hc honce hcas4 hswp4 hv hg_nz hext hbudget hpc hrun rfl hsp rfl
    fun sf e1 hpcf hrunf hspf hcsf hfsf htrf hsigf htpf => ?_
  refine SepWP.done hpcf hrunf ⟨fun hm => ?_, hspf, hcsf⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hfsf, htrf, hsigf, htpf⟩, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_emp, sepConj_assoc] at hm ⊢
  exact Satisfies.mono (Entails.sepExists_right e1 (by sep_entail)) hm

theorem hbStdoutCost_step (lc0 : Nat) (init : Bool) :
    (if init then lc0 + hbStdoutCost init else (lc0 + hbStdoutCost init) + mallocngBlockCost 1024) =
      lc0 + hbStdoutCost true := by
  cases init <;> simp [hbStdoutCost]

theorem hbStdoutBlocks_step (blk0 : Nat) (init : Bool) :
    (if init then blk0 + hbStdoutBlocks init else (blk0 + hbStdoutBlocks init) + 1) =
      blk0 + hbStdoutBlocks true := by
  cases init <;> simp [hbStdoutBlocks]

theorem hbStdoutInv_true_unpack {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P addrs lim) (γ : GhostName) :
    HbStdoutInv C M γ true ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ⊢
      ∃∗ bufPtr : BitVec 64,
        ⌜bufPtr ≠ 0#64 ∧ 16 ∣ bufPtr.toNat ∧ bufPtr.toNat + 1024 ≤ Arm64.USER_VA_LIMIT⌝ ∗
        (C.std.stdoutGlobalAddr ↦₆₄ 0#64) ∗ ((C.std.stdoutGlobalAddr + 0x08#64) ↦₃₂ 0#32) ∗
        ((C.std.stdoutGlobalAddr + 0x0c#64) ↦₃₂ 0#32) ∗
        hbStdoutRefCell C C.std.stdoutGlobalAddr bufPtr [] ∗
        memRegion (C.std.stdoutGlobalAddr + 0x31#64) 7 ∗
        ((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 0#32) ∗ M.Block γ bufPtr 1024 := by
  dsimp only [HbStdoutInv, hbStdoutRefCell, hbBufWriterState]
  simp only [↓reduceIte, List.length_nil, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
    pointsToBytes_nil, bv_lin_norm, sepExists_sepConj_left]
  apply Entails.sepExists_mono; intro bufPtr; sep_entail

theorem hbStdoutRefCell_to_inv {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P addrs lim) (γ : GhostName) {bufPtr : BitVec 64}
    (hne : bufPtr ≠ 0#64) (hal : 16 ∣ bufPtr.toNat) (hfit : bufPtr.toNat + 1024 ≤ Arm64.USER_VA_LIMIT) :
    (C.std.stdoutGlobalAddr ↦₆₄ 0#64) ∗ ((C.std.stdoutGlobalAddr + 0x08#64) ↦₃₂ 0#32) ∗
      ((C.std.stdoutGlobalAddr + 0x0c#64) ↦₃₂ 0#32) ∗
      hbStdoutRefCell C C.std.stdoutGlobalAddr bufPtr [] ∗
      memRegion (C.std.stdoutGlobalAddr + 0x31#64) 7 ∗
      ((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 0#32) ∗ M.Block γ bufPtr 1024 ⊢
      HbStdoutInv C M γ true ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) := by
  dsimp only [HbStdoutInv, hbStdoutRefCell, hbBufWriterState]
  simp only [↓reduceIte, List.length_nil, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
    pointsToBytes_nil, bv_lin_norm, sepExists_sepConj_left]
  refine Entails.sepExists_right bufPtr ?_
  rw [sepConj_assoc, pure_sepConj_of_true ⟨hne, hal, hfit⟩]; sep_entail

def HbStdoutWfHiSaved (s0 s : State) : Prop :=
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem HbStdoutWfHiSaved.refl (s0 : State) : HbStdoutWfHiSaved s0 s0 :=
  ⟨rfl, rfl, rfl⟩

theorem HbStdoutWfHiSaved.trans_cs {s0 s1 s2 : State}
    (h1 : HbStdoutWfHiSaved s0 s1) (hcs : CalleeSavedPreserved s1 s2) :
    HbStdoutWfHiSaved s0 s2 := by
  rcases h1 with ⟨h27, h28, hv⟩; unpack_cs hcs
  exact ⟨by simp_all, by simp_all, by simp_all⟩

theorem HbStdoutWfHiSaved.of_pure {s0 s sm : State} (_ : FmtPureStatePreserved s sm)
    (hhi : HbStdoutWfHiSaved s0 s)
    (h27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by simp [wp_norm, arm64_norm])
    (h28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by simp [wp_norm, arm64_norm])
    (hv : calleeSavedVRegs sm = calleeSavedVRegs s := by simp [wp_norm, arm64_norm]) :
    HbStdoutWfHiSaved s0 sm :=
  ⟨h27.trans hhi.1, h28.trans hhi.2.1, hv.trans hhi.2.2⟩

theorem hbPrintToBufferCapture_wp {P : Program} {C : HbCliLayout}
    {target_pc ret_pc sp0 : BitVec 64}
    {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C) (hext : ∀ pc, P.externAt? pc = none)
    (hpc : s0.pc = C.printToBufferCaptureAddr) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_al : s0.spAligned = true) (hlr : s0.readReg64 Reg.lr = ret_pc)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp0 →
      CalleeSavedPreserved s0 sf → FmtPureStatePreserved s0 sf →
      sf.readReg64 .x0 = 0#64 →
      SepWP P target_pc sf
        (((C.captureUsedAddr ↦₈ᵣ 0#8) ∗ stackAt sp0 96) ∗ F) post oom) :
    SepWP P target_pc s0
      (((C.captureUsedAddr ↦₈ᵣ 0#8) ∗ stackAt sp0 96) ∗ F) post oom := by
  subst hsp
  have hlr' : s0.readReg64 (.gpr 30#5) = ret_pc := hlr
  rw [show (96 : Nat) = 0 + 8 * 12 from rfl, stackAt_split_cells s0.sp 0 12 (by decide)]
  unpack_cells 12
  refine sepWP_cpu_seg (mid_pc := ret_pc) hext ?_
  have hchunk := (hc.withSvc noSyscalls).printToBufferCapture
  unpack_stdout_code hbPrintToBufferCaptureChunks hchunk
  wp_steps 6; wp_steps 2; wp_steps 1; wp_steps 7
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
    ⟨by simp [CpuAuxPreserved.refl s0], fun hpure => ?_⟩
  have hcont := hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun])
    wp_a (by close_cs) hpure wp_a
  refine SepWP.weaken_pre_frame (fun R hm => ?_) hcont
  rw [show (96 : Nat) = 0 + 8 * 12 from rfl, stackAt_split_cells s0.sp 0 12 (by decide)]
  repack_cells

def hbStdoutWriteFmtSavedRegs (s0 : State) (sp_pr ret_pc : BitVec 64) : SepProp :=
  ((sp_pr - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((sp_pr - 72#64) ↦₆₄ ret_pc) ∗
  ((sp_pr - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗ ((sp_pr - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
  ((sp_pr - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗ ((sp_pr - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
  ((sp_pr - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗ ((sp_pr - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((sp_pr - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((sp_pr - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

theorem hbStdoutWriteFmt_epilogue_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    {target_pc ret_pc sp_pr tid bufPtr w0 w2 w4 w5 : BitVec 64} {haveLse : BitVec 8}
    {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C)
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hal_g8 : MemWidth.isAligned .W32 (C.std.stdoutGlobalAddr + 0x08#64) = true)
    (hext : ∀ pc, P.externAt? pc = none)
    (hbuf_ne : bufPtr ≠ 0#64) (hbuf_al : 16 ∣ bufPtr.toNat) (hbuf_fit : bufPtr.toNat + 1024 ≤ Arm64.USER_VA_LIMIT)
    (hpc : s.pc = C.stdoutWriteFmtAddr + 0x100#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_pr - 128#64) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 (.gpr 0#5) = 0#64)
    (hhi : HbStdoutWfHiSaved s0 s)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_pr → CalleeSavedPreserved s0 sf →
      StdStatePreserved s sf → sf.readReg64 .x0 = 0#64 →
      SepWP P target_pc sf
        ((HbStdoutInv C M γ true ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
          (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ stackAt sp_pr 4288) ∗ F) post oom) :
    SepWP P target_pc s
      (((C.std.stdoutGlobalAddr ↦₆₄ tid) ∗ ((C.std.stdoutGlobalAddr + 0x08#64) ↦₃₂ 1#32) ∗
        ((C.std.stdoutGlobalAddr + 0x0c#64) ↦₃₂ 1#32) ∗
        hbStdoutRefCell C C.std.stdoutGlobalAddr bufPtr [] ∗
        memRegion (C.std.stdoutGlobalAddr + 0x31#64) 7 ∗
        ((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 0#32) ∗ M.Block γ bufPtr 1024 ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        ((sp_pr - 128#64) ↦₆₄ w0) ∗ ((sp_pr - 120#64) ↦₆₄ C.std.stdoutGlobalAddr) ∗
        ((sp_pr - 112#64) ↦₆₄ w2) ∗ ((sp_pr - 104#64) ↦₆₄ 0#64) ∗
        ((sp_pr - 96#64) ↦₆₄ w4) ∗ ((sp_pr - 88#64) ↦₆₄ w5) ∗
        hbStdoutWriteFmtSavedRegs s0 sp_pr ret_pc ∗ stackAt (sp_pr - 128#64) 4160) ∗ F) post oom := by
  let g := C.std.stdoutGlobalAddr
  refine sepWP_cpu_seg (mid_pc := C.std.swp4RelAddr) hext ?_
  have hchunk := (hc.withSvc noSyscalls).stdoutWriteFmt
  unpack_stdout_code hbStdoutWriteFmtChunks hchunk
  wp_steps 2; wp_steps 1; wp_steps 8; wp_steps 1; norm_jmp
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
    ⟨by simp [CpuAuxPreserved.refl s], fun hpure1 => ?_⟩
  have hhi1 := HbStdoutWfHiSaved.of_pure hpure1 hhi
  refine call_stdSwp4 hswp4 (haveLse := haveLse) (ptr := g + 0x08#64) (v0 := 1#32) (new := 0#32)
    (ret_pc := C.stdoutWriteFmtAddr + 0x184#64) (F := ?_) (by sep_frame)
    (fun s2 hpc2 hrun2 hsp2 hcs2 hx0_2 hstd2 => ?_)
    (hsp_align := by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_al)
    (halign := hal_g8)
  have hx0_2' : s2.readReg64 (.gpr 0#5) = 1#64 := hx0_2
  have hx19_2 : s2.readReg64 (.gpr 19#5) = 0#64 := by
    rw [← Reg.x19, hcs2.readReg64_x19]; simp [wp_norm, arm64_norm]
  have hsp2_eq : s2.sp = sp_pr - 128#64 := by rw [hsp2]; simp [wp_norm, arm64_norm, hsp]
  have hsp2_al : s2.spAligned = true := by rw [State.spAligned, hsp2_eq, ← hsp]; exact hsp_al
  have hhi2 : HbStdoutWfHiSaved s0 s2 := hhi1.trans_cs hcs2
  dsimp only [hbStdoutWriteFmtSavedRegs]
  refine sepWP_cpu_seg (mid_pc := ret_pc) hext ?_
  have hchunk2 := (hc.withSvc noSyscalls).stdoutWriteFmt
  unpack_stdout_code hbStdoutWriteFmtChunks hchunk2
  wp_steps 10
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun2])
    ⟨by simp [CpuAuxPreserved.refl s2], fun hpure3 => ?_⟩
  have hstd_all : StdStatePreserved s _ :=
    StdStatePreserved.trans hpure1.1 (StdStatePreserved.trans hstd2 hpure3.1)
  have hcont := hnext _ wp_a (by simp [wp_norm, arm64_norm, hrun2])
    (by simp [wp_norm, arm64_norm])
    (by rcases hhi2 with ⟨_, _, _⟩; close_cs)
    hstd_all wp_a
  refine SepWP.weaken_pre_frame (fun R hm => ?_) hcont
  have hm1 : _ ⊨ ((g ↦₆₄ 0#64) ∗ ((g + 0x08#64) ↦₃₂ 0#32) ∗ ((g + 0x0c#64) ↦₃₂ 0#32) ∗
      hbStdoutRefCell C g bufPtr [] ∗ memRegion (g + 0x31#64) 7 ∗ ((g + 0x38#64) ↦₃₂ 0#32) ∗
      M.Block γ bufPtr 1024) ∗ _ := (by sep_frame : _ → _) hm
  clear hm
  replace hm1 := Satisfies.mono
    (sepConj_mono_left (hbStdoutRefCell_to_inv C M γ hbuf_ne hbuf_al hbuf_fit)) hm1
  rw [show (4288 : Nat) = 4160 + 8 * 16 from rfl, stackAt_split_cells sp_pr 4160 16 (by decide)]
  repack_cells

theorem hbAdapterWriterInv_init (C : HbCliLayout) {s sm : State}
    (writerPtr lockPtrPtr startSlot g bufPtr : BitVec 64)
    (hpure : FmtPureStatePreserved s sm) (hslot8 : writerPtr + 8#64 = startSlot) :
    (writerPtr ↦₆₄ lockPtrPtr) ∗ (startSlot ↦₆₄ 0#64) ∗
      (lockPtrPtr ↦₆₄ g) ∗ hbStdoutRefCell C g bufPtr [] ⊢
      hbAdapterWriterInv C writerPtr lockPtrPtr g bufPtr s.trace [] sm := by
  dsimp only [hbAdapterWriterInv]
  refine Entails.sepExists_right [] (Entails.sepExists_right [] ?_)
  rw [pure_sepConj_of_true
    ⟨rfl, by decide, by simp, by simpa [TraceEvent.ofBytes] using hpure.1.2.1⟩, hslot8]
  sep_entail

/-- Formatting payload kind for `std::io::stdio::__print` (`C.stdioPrintAddr`) and
    `<&Stdout as Write>::write_fmt` (`C.stdoutWriteFmtAddr`). -/
inductive HbPrintKind where
  | constNl (bs : List (BitVec 8))
  | u64Nl   (v : BitVec 64)

def HbPrintKind.outBytes : HbPrintKind → List (BitVec 8)
  | .constNl bs => bs
  | .u64Nl v    => formatGetResult (some v)

def HbPrintKind.isU64 : HbPrintKind → Bool
  | .constNl _ => false
  | .u64Nl _   => true

def HbPrintKind.inputRes (C : HbCliLayout) (k : HbPrintKind)
    (arg0 arg1 valPtr : BitVec 64) : SepProp :=
  match k with
  | .constNl bs =>
    ⌜1 ≤ bs.length ∧ bs.length ≤ 15 ∧ bs.getD (bs.length - 1) 0#8 = 0x0a#8 ∧
      arg0.toNat + bs.length ≤ Arm64.USER_VA_LIMIT ∧
      arg1 &&& 1#64 = 1#64 ∧ arg1 >>> 1 = BitVec.ofNat 64 bs.length⌝ ∗
    HbAdapterWriteVtableRo C ∗ (arg0 ↦ᵣ bs)
  | .u64Nl v =>
    ⌜arg0 ≠ 0#64 ∧ arg0.toNat + 12 ≤ Arm64.USER_VA_LIMIT ∧ arg1 &&& 1#64 = 0#64⌝ ∗
    hbCoreFmtWriteU64NlRes C arg0 arg1 valPtr v

/-- Input formatting resources for `std::io::stdio::__print` (`C.stdioPrintAddr`) at `hashbrown`
    `print_get_result` call sites. -/
def hbStdioPrintInputRes (C : HbCliLayout) (optVal : Option (BitVec 64))
    (arg0 arg1 valPtr : BitVec 64) : SepProp :=
  match optVal with
  | none =>
    ⌜arg0 = C.noneNlAddr ∧ arg1 = 0x0b#64⌝ ∗ HbAdapterWriteVtableRo C ∗ (C.noneNlAddr ↦ᵣ noneNlBytes)
  | some v =>
    ⌜arg0 ≠ 0#64 ∧ arg0.toNat + 12 ≤ Arm64.USER_VA_LIMIT ∧ arg1 &&& 1#64 = 0#64⌝ ∗
    hbCoreFmtWriteU64NlRes C arg0 arg1 valPtr v

theorem list_eq_take_append_nl {bs : List (BitVec 8)}
    (hlen : 1 ≤ bs.length) (hlast : bs.getD (bs.length - 1) 0#8 = 0x0a#8) :
    bs = bs.take (bs.length - 1) ++ [0x0a#8] := by
  have hlt : bs.length - 1 < bs.length := by omega
  have hget : bs[bs.length - 1]'hlt = 0x0a#8 := by simpa [List.getD, hlt] using hlast
  conv => lhs; rw [← List.take_append_drop (bs.length - 1) bs,
    List.drop_eq_getElem_cons hlt, hget, List.drop_eq_nil_of_le (by omega)]

theorem hbAdapterWriterInv_nl_finish_bs {flushed buffered bs : List (BitVec 8)}
    (hlen : 1 ≤ bs.length) (hlast : bs.getD (bs.length - 1) 0#8 = 0x0a#8)
    (heq : bs = flushed ++ buffered) (hnoNl : 0x0a#8 ∉ buffered) :
    buffered = [] ∧ flushed = bs := by
  have hbs := list_eq_take_append_nl hlen hlast
  obtain ⟨hb, hf⟩ := hbAdapterWriterInv_nl_finish (hbs ▸ heq) hnoNl
  exact ⟨hb, hf.trans hbs.symm⟩

def HbPrintIoPreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.sigActions = s0.sigActions ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧
  sf.brk = s0.brk ∧ sf.brkStart = s0.brkStart ∧ sf.physMemAvail = s0.physMemAvail ∧
  (∀ a, sf.mem.perm a = s0.mem.perm a)

theorem HbPrintIoPreserved.refl (s : State) : HbPrintIoPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem HbPrintIoPreserved.trans {s1 s2 s3 : State}
    (h12 : HbPrintIoPreserved s1 s2) (h23 : HbPrintIoPreserved s2 s3) :
    HbPrintIoPreserved s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1,
   h23.2.2.2.1.trans h12.2.2.2.1, h23.2.2.2.2.1.trans h12.2.2.2.2.1,
   h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1,
   fun a => (h23.2.2.2.2.2.2 a).trans (h12.2.2.2.2.2.2 a)⟩

theorem HbPrintIoPreserved.of_std {s1 s2 : State} (h : StdStatePreserved s1 s2) :
    HbPrintIoPreserved s1 s2 :=
  ⟨h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem HbPrintIoPreserved.of_fmtIo {s1 s2 : State} (h : FmtIoStatePreserved s1 s2) :
    HbPrintIoPreserved s1 s2 :=
  ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem heap_eq_of_printIo {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) {γ : GhostName} {lc blk : Nat} {s1 s2 : State}
    (h : HbPrintIoPreserved s1 s2) :
    M.Heap γ lc blk s1 = M.Heap γ lc blk s2 :=
  heap_eq M h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2

theorem hbStdoutWriteFmt_acquire_and_fmt_wp {P : Program} {C : HbCliLayout} (k : HbPrintKind)
    {target_pc sp_pr arg0 arg1 valPtr tid bufPtr w1 w2 w3 : BitVec 64} {haveLse : BitVec 8}
    {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C)
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hal_g8 : MemWidth.isAligned .W32 (C.std.stdoutGlobalAddr + 0x08#64) = true)
    (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (hbuf_fit : bufPtr.toNat + 1024 ≤ Arm64.USER_VA_LIMIT)
    (hsp_lo : k.isU64 = true → 0x280 ≤ sp_pr.toNat)
    (hpc : s.pc = C.stdoutWriteFmtAddr + 0xb8#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_pr - 128#64) (hsp_al : s.spAligned = true)
    (hx19 : s.readReg64 (.gpr 19#5) = arg1) (hx20 : s.readReg64 (.gpr 20#5) = arg0)
    (hx24 : s.readReg64 (.gpr 24#5) = C.std.stdoutGlobalAddr) (hx25 : s.readReg64 (.gpr 25#5) = tid)
    (hhi : HbStdoutWfHiSaved s0 s)
    (hnext : ∀ (s' : State) (w2' : BitVec 64),
      s'.pc = C.stdoutWriteFmtAddr + 0x100#64 → s'.status = .Running → s'.sp = sp_pr - 128#64 →
      s'.spAligned = true → s'.readReg64 (.gpr 0#5) = 0#64 →
      HbStdoutWfHiSaved s0 s' → HbPrintIoPreserved s s' →
      s'.trace = s.trace ++ TraceEvent.ofBytes .stdout k.outBytes →
      SepWP P target_pc s'
        (((C.std.stdoutGlobalAddr ↦₆₄ tid) ∗ ((C.std.stdoutGlobalAddr + 0x08#64) ↦₃₂ 1#32) ∗
          ((C.std.stdoutGlobalAddr + 0x0c#64) ↦₃₂ 1#32) ∗
          hbStdoutRefCell C C.std.stdoutGlobalAddr bufPtr [] ∗
          (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ k.inputRes C arg0 arg1 valPtr ∗
          ((sp_pr - 120#64) ↦₆₄ C.std.stdoutGlobalAddr) ∗ ((sp_pr - 112#64) ↦₆₄ w2') ∗
          ((sp_pr - 104#64) ↦₆₄ 0#64) ∗ stackAt (sp_pr - 128#64) 4160) ∗ F) post oom) :
    SepWP P target_pc s
      (((C.std.stdoutGlobalAddr ↦₆₄ 0#64) ∗ ((C.std.stdoutGlobalAddr + 0x08#64) ↦₃₂ 0#32) ∗
        ((C.std.stdoutGlobalAddr + 0x0c#64) ↦₃₂ 0#32) ∗
        hbStdoutRefCell C C.std.stdoutGlobalAddr bufPtr [] ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ k.inputRes C arg0 arg1 valPtr ∗
        ((sp_pr - 120#64) ↦₆₄ w1) ∗ ((sp_pr - 112#64) ↦₆₄ w2) ∗
        ((sp_pr - 104#64) ↦₆₄ w3) ∗ stackAt (sp_pr - 128#64) 4160) ∗ F) post oom := by
  let g := C.std.stdoutGlobalAddr
  refine sepWP_cpu_seg (mid_pc := C.std.cas4AcqAddr) hext ?_
  have hchunk := (hc.withSvc noSyscalls).stdoutWriteFmt
  unpack_stdout_code hbStdoutWriteFmtChunks hchunk
  wp_steps 4; wp_steps 1; norm_jmp
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
    ⟨by simp [CpuAuxPreserved.refl s], fun hpure1 => ?_⟩
  have hhi1 := HbStdoutWfHiSaved.of_pure hpure1 hhi
  refine call_stdCas4 hcas4 (haveLse := haveLse) (ptr := g + 0x08#64) (v0 := 0#32) (exp := 0#32) (new := 1#32)
    (ret_pc := C.stdoutWriteFmtAddr + 0xcc#64) (F := ?_) (by sep_frame)
    (fun s2 hpc2 hrun2 hsp2 hcs2 hx0_2 hstd2 => ?_)
    (hsp_align := by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp_al)
    (halign := hal_g8)
  simp only [beq_self_eq_true, ↓reduceIte]
  have hx0_2' : s2.readReg64 (.gpr 0#5) = 0#64 := hx0_2
  have hx19_2 : s2.readReg64 (.gpr 19#5) = arg1 := by rw [← Reg.x19, hcs2.readReg64_x19]; simp [wp_norm, arm64_norm, hx19]
  have hx20_2 : s2.readReg64 (.gpr 20#5) = arg0 := by rw [← Reg.x20, hcs2.readReg64_x20]; simp [wp_norm, arm64_norm, hx20]
  have hx21_2 : s2.readReg64 (.gpr 21#5) = 1#64 := by rw [← Reg.x21, hcs2.readReg64_x21]; simp [wp_norm, arm64_norm]
  have hx24_2 : s2.readReg64 (.gpr 24#5) = g := by rw [← Reg.x24, hcs2.readReg64_x24]; simp [wp_norm, arm64_norm, hx24, g]
  have hx25_2 : s2.readReg64 (.gpr 25#5) = tid := by rw [← Reg.x25, hcs2.readReg64_x25]; simp [wp_norm, arm64_norm, hx25]
  have hsp2_eq : s2.sp = sp_pr - 128#64 := by rw [hsp2]; simp [wp_norm, arm64_norm, hsp]
  have hsp2_al : s2.spAligned = true := by rw [State.spAligned, hsp2_eq, ← hsp]; exact hsp_al
  have hhi2 : HbStdoutWfHiSaved s0 s2 := hhi1.trans_cs hcs2
  refine sepWP_cpu_seg (mid_pc := C.coreFmtWriteAddr) hext ?_
  have hchunk2 := (hc.withSvc noSyscalls).stdoutWriteFmt
  unpack_stdout_code hbStdoutWriteFmtChunks hchunk2
  wp_steps 8; wp_steps 1; wp_steps 3; wp_steps 1; norm_jmp
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun2])
    ⟨by simp [CpuAuxPreserved.refl s2], fun hpure3 => ?_⟩
  have hhi3 := HbStdoutWfHiSaved.of_pure hpure3 hhi2
  have hstd03 : StdStatePreserved s _ :=
    StdStatePreserved.trans hpure1.1 (StdStatePreserved.trans hstd2 hpure3.1)
  have hinv_init := hbAdapterWriterInv_init C (sp_pr - 112#64) (sp_pr - 120#64) (sp_pr - 104#64) g bufPtr
    hpure3 (by bv_lin)
  refine SepWP.weaken_pre (P' := k.inputRes C arg0 arg1 valPtr ∗ _) (by sep_frame) ?_
  cases k with
  | constNl bs =>
    dsimp only [HbPrintKind.inputRes, HbPrintKind.outBytes]
    simp only [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hlen_lo, hlen_hi, hlast, harg0_va, harg1_odd, harg1_len⟩
    have hwrite := hbAdapterWriteStr_nlEnd_ro_ok (sp_pr - 112#64) (sp_pr - 120#64) g bufPtr arg0 s2.trace [] bs
      hc hcSys hMem hMemmove hlen_lo hlen_hi hlast hbuf_fit harg0_va hsvc hext
    rw [show (4160 : Nat) = 304 + 3856 from rfl, stackAt_split 304 3856,
        stackAt_eq_stackFrameAt (sp_pr - 128#64) 304]
    refine SepWP.weaken_pre
      (P' := (HbAdapterWriteVtableRo C ∗ (arg0 ↦ᵣ bs) ∗
              hbAdapterWriterInv C (sp_pr - 112#64) (sp_pr - 120#64) g bufPtr s2.trace [] _ ∗
              stackFrameAt (sp_pr - 128#64) (max 0x70 304)) ∗
             (((g ↦₆₄ tid) ∗ ((g + 8#64) ↦₃₂ 1#32) ∗ ((g + 12#64) ↦₃₂ 1#32) ∗
               (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ stackAt ((sp_pr - 128#64) - 304#64) 3856) ∗ F))
      (by
        refine Entails.trans ?_
          (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hinv_init))))
        change _ ⊢ (_ ∗ (_ ∗ (_ ∗ stackFrameAt (sp_pr - 128#64) 304))) ∗ _; sep_entail)
      (hbCoreFmtWrite_const_wp (ret_pc := C.stdoutWriteFmtAddr + 0x100#64)
        hfmt.coreWrite_words (by decide)
        (fun hp => by dsimp only [hbAdapterWriterInv]; rw [hp.1.2.1]; exact Entails.refl _)
        hwrite hext wp_a (by simp [wp_norm, arm64_norm, hrun2])
        (by simp [wp_norm, arm64_norm, hsp2_eq])
        (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp2_al)
        wp_a wp_a wp_a wp_a wp_a harg1_odd harg1_len
        fun s4 hpc4 hrun4 hsp4 hcs4 hx0_4 hio4 => ?_)
    have hx0_4' : s4.readReg64 (.gpr 0#5) = 0#64 := hx0_4
    have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4, ← hsp2_eq] using hsp2_al
    have hhi4 : HbStdoutWfHiSaved s0 s4 := hhi3.trans_cs hcs4
    dsimp only [hbAdapterWriterInv, List.nil_append]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro flushed; apply SepWP.exists_elim; intro buffered
    simp only [sepConj_assoc]
    rw [sepConj_left_comm (arg0 ↦ᵣ bs), sepConj_left_comm (HbAdapterWriteVtableRo C)]
    apply SepWP.pure_elim; rintro ⟨hemit, _, hnoNl, htr4⟩
    obtain ⟨hbuf_nil, hfl_eq⟩ := hbAdapterWriterInv_nl_finish_bs hlen_lo hlast hemit hnoNl
    subst hbuf_nil
    rw [show (sp_pr - 112#64) + 8#64 = sp_pr - 104#64 by bv_lin]
    have hcont := hnext s4 (sp_pr - 120#64) hpc4 hrun4 hsp4 hsp4_al hx0_4' hhi4
      ((HbPrintIoPreserved.of_std hstd03).trans (HbPrintIoPreserved.of_fmtIo hio4))
      (by dsimp only [HbPrintKind.outBytes]; rw [htr4, hfl_eq, hstd2.2.1, hpure1.1.2.1])
    refine SepWP.weaken_pre_frame (fun R hm => ?_) hcont
    dsimp only [HbPrintKind.inputRes]; change _ at hm
    rw [pure_sepConj_of_true ⟨hlen_lo, hlen_hi, hlast, harg0_va, harg1_odd, harg1_len⟩,
        show (4160 : Nat) = 304 + 3856 from rfl, stackAt_split 304 3856,
        stackAt_eq_stackFrameAt (sp_pr - 128#64) 304]
    change _ ⊨ ((_ ∗ (_ ∗ (_ ∗ (_ ∗ (_ ∗ (_ ∗ (_ ∗ (_ ∗ (_ ∗ (stackFrameAt (sp_pr - 128#64) 304 ∗ _)))))))))) ∗ F) ∗ R
    sep_entail
  | u64Nl v =>
    have hsp_wf_lo : 0x200 ≤ (sp_pr - 128#64).toNat := by
      have := sp_pr.isLt; have := hsp_lo rfl
      rw [BitVec.toNat_sub_of_le (show (128#64 : BitVec 64) ≤ sp_pr by
        rw [BitVec.le_def]; change 128 ≤ sp_pr.toNat; omega)]
      change 512 ≤ sp_pr.toNat - 128; omega
    dsimp only [HbPrintKind.inputRes, HbPrintKind.outBytes]
    simp only [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨htpl_ne, htpl_fit, hx1_even⟩
    have hw := hbAdapterFmtWriter (sp_pr - 112#64) (sp_pr - 120#64) g bufPtr s2.trace
      hc hcSys hMem hMemmove hbuf_fit hsvc hext
    rw [show (4160 : Nat) = 544 + 3616 from rfl, stackAt_split 544 3616,
        stackAt_eq_stackFrameAt (sp_pr - 128#64) 544]
    refine SepWP.weaken_pre
      (P' := (hbCoreFmtWriteU64NlRes C arg0 arg1 valPtr v ∗
              hbAdapterWriterInv C (sp_pr - 112#64) (sp_pr - 120#64) g bufPtr s2.trace [] _ ∗
              stackFrameAt (sp_pr - 128#64) (0xf0 + max 0x30 304)) ∗
             (((g ↦₆₄ tid) ∗ ((g + 8#64) ↦₃₂ 1#32) ∗ ((g + 12#64) ↦₃₂ 1#32) ∗
               (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ stackAt ((sp_pr - 128#64) - 544#64) 3616) ∗ F))
      (by
        refine Entails.trans ?_
          (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hinv_init)))
        change _ ⊢ (_ ∗ (_ ∗ stackFrameAt (sp_pr - 128#64) 544)) ∗ _; sep_entail)
      (hbCoreFmtWrite_u64Nl_wp (ret_pc := C.stdoutWriteFmtAddr + 0x100#64) hfmt hw hext htpl_ne htpl_fit
        wp_a (by simp [wp_norm, arm64_norm, hrun2])
        (by simp [wp_norm, arm64_norm, hsp2_eq])
        (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp2_al)
        hsp_wf_lo wp_a wp_a wp_a wp_a wp_a hx1_even
        fun s4 hpc4 hrun4 hsp4 hcs4 hx0_4 hio4 => ?_)
    have hx0_4' : s4.readReg64 (.gpr 0#5) = 0#64 := hx0_4
    have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4, ← hsp2_eq] using hsp2_al
    have hhi4 : HbStdoutWfHiSaved s0 s4 := hhi3.trans_cs hcs4
    dsimp only [hbAdapterWriterInv, List.nil_append]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro flushed; apply SepWP.exists_elim; intro buffered
    simp only [sepConj_assoc]
    rw [sepConj_left_comm (hbCoreFmtWriteU64NlRes C arg0 arg1 valPtr v)]
    apply SepWP.pure_elim; rintro ⟨hemit, _, hnoNl, htr4⟩
    obtain ⟨hbuf_nil, hfl_eq⟩ := hbAdapterWriterInv_nl_finish hemit hnoNl
    subst hbuf_nil
    rw [show (sp_pr - 112#64) + 8#64 = sp_pr - 104#64 by bv_lin]
    have hfmt_eq : formatDecimalNat v.toNat ++ [0x0a#8] = formatGetResult (some v) := by
      simpa using emitted_append_u64Nl_eq_formatGetResult [] v
    have hcont := hnext s4 (sp_pr - 120#64) hpc4 hrun4 hsp4 hsp4_al hx0_4' hhi4
      ((HbPrintIoPreserved.of_std hstd03).trans (HbPrintIoPreserved.of_fmtIo hio4))
      (by dsimp only [HbPrintKind.outBytes]; rw [htr4, hfl_eq, hfmt_eq, hstd2.2.1, hpure1.1.2.1])
    refine SepWP.weaken_pre_frame (fun R hm => ?_) hcont
    dsimp only [HbPrintKind.inputRes]; change _ at hm
    rw [pure_sepConj_of_true ⟨htpl_ne, htpl_fit, hx1_even⟩,
        show (4160 : Nat) = 544 + 3616 from rfl, stackAt_split 544 3616,
        stackAt_eq_stackFrameAt (sp_pr - 128#64) 544]
    change _ ⊨ ((_ ∗ (_ ∗ (_ ∗ (_ ∗ (_ ∗ (_ ∗ (_ ∗ (_ ∗ (_ ∗ (stackFrameAt (sp_pr - 128#64) 544 ∗ _)))))))))) ∗ F) ∗ R
    sep_entail

theorem hbStdoutWriteFmt_from0xb8_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName) (k : HbPrintKind)
    {target_pc ret_wf sp_pr arg0 arg1 valPtr tid bufPtr w0 w1 w2 w3 w4 w5 : BitVec 64} {haveLse : BitVec 8}
    {s_wf s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : HbStdoutCode P C) (hcSys : HbSyscallsAndStderrCode P C) (hfmt : HbFmtCode P C)
    (hcas4 : subroutine_ok P C.std.cas4AcqAddr (stdCas4Spec C.std.haveLseAtomicsAddr))
    (hswp4 : subroutine_ok P C.std.swp4RelAddr (stdSwp4Spec C.std.haveLseAtomicsAddr))
    (hMem : StdMemOps (P.withSvc hbStdioSvc) C.std.memcpyAddr C.std.memsetAddr)
    (hMemmove : subroutine_ok (P.withSvc hbStdioSvc) C.memmoveAddr stdMemcpySpec)
    (hv : C.Valid) (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (hbuf_ne : bufPtr ≠ 0#64) (hbuf_al : 16 ∣ bufPtr.toNat) (hbuf_fit : bufPtr.toNat + 1024 ≤ Arm64.USER_VA_LIMIT)
    (hsp_lo : k.isU64 = true → 0x280 ≤ sp_pr.toNat)
    (hpc : s.pc = C.stdoutWriteFmtAddr + 0xb8#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_pr - 128#64) (hsp_al : s.spAligned = true)
    (hx19 : s.readReg64 (.gpr 19#5) = arg1) (hx20 : s.readReg64 (.gpr 20#5) = arg0)
    (hx24 : s.readReg64 (.gpr 24#5) = C.std.stdoutGlobalAddr) (hx25 : s.readReg64 (.gpr 25#5) = tid)
    (hhi : HbStdoutWfHiSaved s_wf s)
    (hnext : ∀ sf : State,
      sf.pc = ret_wf → sf.status = .Running → sf.sp = sp_pr →
      CalleeSavedPreserved s_wf sf → HbPrintIoPreserved s sf → sf.readReg64 .x0 = 0#64 →
      sf.trace = s.trace ++ TraceEvent.ofBytes .stdout k.outBytes →
      SepWP P target_pc sf
        ((HbStdoutInv C M γ true ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
          (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ k.inputRes C arg0 arg1 valPtr ∗
          stackAt sp_pr 4288) ∗ F) post oom) :
    SepWP P target_pc s
      (((C.std.stdoutGlobalAddr ↦₆₄ 0#64) ∗ ((C.std.stdoutGlobalAddr + 0x08#64) ↦₃₂ 0#32) ∗
        ((C.std.stdoutGlobalAddr + 0x0c#64) ↦₃₂ 0#32) ∗
        hbStdoutRefCell C C.std.stdoutGlobalAddr bufPtr [] ∗
        memRegion (C.std.stdoutGlobalAddr + 0x31#64) 7 ∗
        ((C.std.stdoutGlobalAddr + 0x38#64) ↦₃₂ 0#32) ∗ M.Block γ bufPtr 1024 ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ k.inputRes C arg0 arg1 valPtr ∗
        ((sp_pr - 128#64) ↦₆₄ w0) ∗ ((sp_pr - 120#64) ↦₆₄ w1) ∗
        ((sp_pr - 112#64) ↦₆₄ w2) ∗ ((sp_pr - 104#64) ↦₆₄ w3) ∗
        ((sp_pr - 96#64) ↦₆₄ w4) ∗ ((sp_pr - 88#64) ↦₆₄ w5) ∗
        hbStdoutWriteFmtSavedRegs s_wf sp_pr ret_wf ∗ stackAt (sp_pr - 128#64) 4160) ∗ F) post oom := by
  obtain ⟨_, hal_g8, _, _⟩ := hbValid_stdout_align hv
  refine SepWP.weaken_pre (by sep_frame)
    (hbStdoutWriteFmt_acquire_and_fmt_wp k (valPtr := valPtr) (tid := tid) (bufPtr := bufPtr)
      (w1 := w1) (w2 := w2) (w3 := w3)
      hc hcSys hfmt hcas4 hMem hMemmove hal_g8 hsvc hext hbuf_fit hsp_lo
      hpc hrun hsp hsp_al hx19 hx20 hx24 hx25 hhi
      fun s1 w2' hpc1 hrun1 hsp1 hsp1_al hx0_1 hhi1 hio1 htr1 => ?_)
  refine SepWP.weaken_pre (by sep_frame)
    (hbStdoutWriteFmt_epilogue_wp M γ (ret_pc := ret_wf) (tid := tid) (bufPtr := bufPtr)
      (w0 := w0) (w2 := w2') (w4 := w4) (w5 := w5)
      hc hswp4 hal_g8 hext hbuf_ne hbuf_al hbuf_fit
      hpc1 hrun1 hsp1 hsp1_al hx0_1 hhi1
      fun sf hpcf hrunf hspf hcsf hstd2 hx0f => ?_)
  have hio_all : HbPrintIoPreserved s sf := hio1.trans (HbPrintIoPreserved.of_std hstd2)
  have htr_all : sf.trace = s.trace ++ TraceEvent.ofBytes .stdout k.outBytes := by rw [hstd2.2.1, htr1]
  refine SepWP.weaken_pre_frame (fun R hm => by sep_entail)
    (hnext sf hpcf hrunf hspf hcsf hio_all hx0f htr_all)

end CaseStudies.Hashbrown.Proofs.StdCli
