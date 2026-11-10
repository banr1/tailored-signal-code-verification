/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.MainRead
public meta import ProofLib.LiteralFetchLint
import ProofLib.BV

/-!
# Layout-Generic `hashbrown_cli::main` Stdin Read and Line-Length Scan

Placement-generic `SepWP` verification of `bufReaderReadToEnd_wp`, `stdinReadToEnd_wp`,
`hbMain_readToEnd_wp`, and `hbMain_scanLines_wp` on the 224-byte (`0xe0`) `main` stack frame.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open CaseStudies.Hashbrown CaseStudies.Hashbrown.Proofs

local macro "unpack_hb_subchunks " chunks:ident h:term:arg idxs:term:arg : tactic => `(tactic| (
  have _hc := chunksToStepFacts (codeChunks_select $h $idxs)
  simp only [$chunks:ident, List.filterMap_cons, List.filterMap_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.some.injEq, chunksStepFacts, chunkStepAcc, fetchAtAcc,
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

local macro "norm_jmp" : tactic => `(tactic| (
  (try (conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel]))
  (try (conv in State.setPC _ _ => arg 2; rw [BitVec.add_assoc]; simp only [BitVec.reduceAdd]))))

local macro "unpack_cells " k:num : tactic => `(tactic| (
  conv => arg 4; simp -failIfUnchanged (config := { zetaDelta := false }) only [Nat.reduceMul,
    cells_succ, cells_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right]
  iterate $k (apply SepWP.exists_left; intro _)))

local macro "repack_cells" : tactic => `(tactic| (
  simp -failIfUnchanged (config := { zetaDelta := false }) only [Nat.reduceMul,
    cells_succ, cells_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
    BitVec.ofNat_eq_ofNat, sepExists_sepConj_left, sepExists_sepConj_right]; sep_entail))

local macro "wp_a" : term => `(by simp [wp_norm, arm64_norm, bv_lin_norm, *] <;> try bv_lin)

/-! ## `<BufReader<StdinRaw> as Read>::read_to_end` and `<Stdin as Read>::read_to_end` -/

private theorem stackAt96_split_slot20 (sp_m : BitVec 64) :
    stackAt (sp_m + 0x80#64) 96 = cells (sp_m + 0x20#64) 1 ∗ stackAt (sp_m + 0x80#64) 88 := by
  rw [stackAt_split_main (sp_m + 0x80#64) 88 8 (n := 96)]
  have ha : stackAt (sp_m + 0x80#64 - BitVec.ofNat 64 88) 8 = cells (sp_m + 0x20#64) 1 := by
    have heq := stackAt_eq_cells (sp_m + 0x28#64) 1
    have h1 : sp_m + 0x80#64 - BitVec.ofNat 64 88 = sp_m + 0x28#64 := by bv_lin
    have h2 : sp_m + 0x28#64 - BitVec.ofNat 64 (8 * 1) = sp_m + 0x20#64 := by bv_lin
    rw [h1, heq, h2]
  rw [ha]

private theorem stackAt96_repack_slot20 (sp_m v : BitVec 64) :
    ((sp_m + 0x20#64) ↦₆₄ v) ∗ stackAt (sp_m + 0x80#64) 88 ⊢ stackAt (sp_m + 0x80#64) 96 := by
  rw [stackAt96_split_slot20 sp_m, cells_succ, cells_zero]
  exact sepConj_mono_left (Entails.sepExists_right v (by sep_entail))

private theorem seq_nonVm_kf {prog : Program} {mid target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} (hext : ∀ pc, prog.externAt? pc = none) (hsvc : prog.svc = Syscall.standard)
    (h : SepWP (prog.withSvc nonVmSvc) mid s P
      (fun sm Pm => VmFieldsPreserved s sm → s.mem.KeepsFrozen sm.mem → SepWP prog target sm Pm post)) :
    SepWP prog target s P post :=
  SepWP.seq_nonVm hext hsvc (SepWP.with_keepsFrozen (SepWP.mono h fun _ _ _ _ hp hkf hvm => hp hvm hkf))

private theorem HbStdinInv_true_unpack {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P addrs lim) (γ : GhostName) :
    HbStdinInv C M γ true ⊢ ∃∗ bufPtr : BitVec 64,
      ⌜bufPtr ≠ 0#64 ∧ 16 ∣ bufPtr.toNat ∧ bufPtr.toNat + 8192 < 2 ^ 64⌝ ∗
      (C.stdinGlobalAddr ↦₃₂ 0#32) ∗ HbStdinLockedRest C M γ bufPtr := by
  dsimp only [HbStdinInv, HbStdinLockedRest, ↓reduceIte]
  exact Entails.sepExists_mono fun bufPtr => by sep_entail

/-- Placement-generic `SepWP` specification for `<BufReader<StdinRaw> as Read>::read_to_end`
    (`C.bufReaderReadToEndAddr`, `hbBufReaderReadToEndChunks C`) when `pos = 0, filled = 0`. -/
theorem bufReaderReadToEnd_wp {P : Program} {C : HbCliLayout} {L : Nat} {target_pc ret_pc sp_call : BitVec 64}
    (hc : HbUserMainCode P C) (hc_stdin : HbStdinAndVecCode P C) (hc_sys : HbSyscallsAndStderrCode P C)
    (hMem : StdMemOps P C.std.memcpyAddr C.std.memsetAddr)
    (M : HbMallocngIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    {bufPtr vecSlotPtr ptr0 : BitVec 64} {lc blk : Nat} {stdinBytes : List (BitVec 8)} {e0 : BitVec 32}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hsvc : P.svc = Syscall.standard := by rfl) (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    (hL_eq : stdinBytes.length = L := by rfl) (hL : L ≤ HashbrownCliMaxStdin)
    (hlc_le : lc ≤ mallocngBlockCost 1024 + mallocngBlockCost 8192 := by omega)
    (hblk_le : blk ≤ 2 := by omega) (hpc : s.pc = C.bufReaderReadToEndAddr) (hrun : s.status = .Running)
    (hsp_call : s.sp = sp_call) (hsp_align : s.spAligned = true)
    (hsp_lo : 416 ≤ sp_call.toNat) (hsp_va : sp_call.toNat ≤ Arm64.USER_VA_LIMIT)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = C.stdinGlobalAddr + 0x08#64) (hx1 : s.readReg64 .x1 = vecSlotPtr)
    (hopen : HbStdinOpen stdinBytes s.fs)
    (hpre : Pre ⊢ HbStdinLockedRest C M.toMallocngCoreIface γ bufPtr ∗
      HbByteVec M.toMallocngCoreIface γ vecSlotPtr 0 ptr0 [] ∗ M.Heap γ lc blk s ∗
      (muslErrnoAddr s ↦₃₂ e0) ∗ stackAt sp_call hbBufReaderReadStackBytes ∗ F)
    (hnext : ∀ (sf : State) (cap : Nat) (vecPtr : BitVec 64) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.spAligned = true →
      sf.readReg64 .x0 = 0#64 → sf.readReg64 .x1 = BitVec.ofNat 64 stdinBytes.length →
      CalleeSavedPreserved s sf → cap ≤ 2 * stdinBytes.length + 32 → HbStdinOpen [] sf.fs →
      sf.trace = s.trace → sf.tpidrEl0 = s.tpidrEl0 → sf.sigActions = s.sigActions →
      s.mem.KeepsFrozen sf.mem →
      SepWP P target_pc sf
        (HbStdinLockedRest C M.toMallocngCoreIface γ bufPtr ∗
          HbByteVec M.toMallocngCoreIface γ vecSlotPtr cap vecPtr stdinBytes ∗
          M.Heap γ (lc + hbByteVecCost cap) (blk + hbByteVecBlocks cap) sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt sp_call hbBufReaderReadStackBytes ∗ F) post) :
    SepWP P target_pc s Pre post := by
  cases hsp_call; cases hlr; subst hL_eq
  obtain ⟨sp_b, hsp_b_def⟩ : ∃ sp_b, s.sp - 128#64 = sp_b := ⟨_, rfl⟩
  have hsp_b_al : ((sp_b &&& 15#64) == 0#64) = true := hsp_b_def ▸ s.spAligned_sub 128#64 hsp_align
  have hx0' : s.readReg64 (.gpr 0#5) = C.stdinGlobalAddr + 0x08#64 := hx0
  have hx1' : s.readReg64 (.gpr 1#5) = vecSlotPtr := hx1
  apply SepWP.weaken_pre hpre
  conv => arg 4; rw [show hbBufReaderReadStackBytes = hbDefaultReadStackBytes + 8 * 16 from rfl,
    stackAt_split_cells s.sp hbDefaultReadStackBytes 16 (by decide),
    show s.sp - BitVec.ofNat 64 (8 * 16) = sp_b from hsp_b_def]; dsimp only [HbStdinLockedRest, HbByteVec]
  unpack_cells 16
  refine seq_nonVm_kf (mid := C.defaultReadToEndAddr) hext hsvc ?_
  have hc_nv1 := (hc.withSvc nonVmSvc).bufReaderRead
  unpack_hb_subchunks hbBufReaderReadToEndChunks hc_nv1 [0, 1, 2, 3]
  iterate 4 (wp_steps; (try norm_jmp))
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) (fun hvm1 hkf0 => ?_)
  apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm1)
  have hvec0 : (vecSlotPtr ↦₆₄ BitVec.ofNat 64 0) ∗ ((vecSlotPtr + 0x08#64) ↦₆₄ ptr0) ∗
      ((vecSlotPtr + 0x10#64) ↦₆₄ 0#64) ∗ HbByteVecBuf M.toMallocngCoreIface γ 0 ptr0 [] ⊢
      HbByteVec M.toMallocngCoreIface γ vecSlotPtr 0 ptr0 [] := by dsimp only [HbByteVec]; sep_entail
  apply sepWP_mono_atom hvec0
  have hsp_b_lo : 288 ≤ sp_b.toNat := by
    rw [← hsp_b_def]; bv_omega
  have hsp_b_va : sp_b.toNat ≤ Arm64.USER_VA_LIMIT := by
    rw [← hsp_b_def]; unfold Arm64.USER_VA_LIMIT at hsp_va ⊢; bv_omega
  refine defaultReadToEnd_wp hc hc_stdin hc_sys hMem M γ
    (vecSlotPtr := vecSlotPtr) (ptr0 := ptr0) (lc := lc) (blk := blk)
    (stdinBytes := stdinBytes) (e0 := e0) (sp_call := sp_b) (ret_pc := C.bufReaderReadToEndAddr + 0xec#64)
    hsvc hext rfl hL hlc_le hblk_le
    wp_a (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_b_al)
    hsp_b_lo hsp_b_va
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simpa [wp_norm, arm64_norm] using hopen)
    (by simp [muslErrnoAddr, wp_norm, arm64_norm]; sep_frame)
    (fun s1 cap vecPtr e1 hpc1 hrun1 hsp1 _hal1 hx0_1 hx1_1 hcs1 hcap_le hopen1 htr1 htp1 hsig1 hkf1 => ?_)
  subst hsp1
  have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1
  have hx1_1' : s1.readReg64 (.gpr 1#5) = BitVec.ofNat 64 stdinBytes.length := hx1_1
  have hx19_1 : s1.readReg64 (.gpr 19#5) = 0#64 := by
    rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm]
  refine seq_nonVm_kf (mid := s.readReg64 Reg.lr) hext hsvc ?_
  have hc_nv2 := (hc.withSvc nonVmSvc).bufReaderRead
  unpack_hb_subchunks hbBufReaderReadToEndChunks hc_nv2 [4, 5, 6]
  iterate 3 (wp_steps; (try norm_jmp))
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1]) (fun hvm2 hkf2 => ?_)
  apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm2)
  have hsp_ret : s1.sp + 128#64 = s.sp := by rw [← hsp_b_def]; bv_lin
  refine SepWP.weaken_pre_frame (fun R hm => ?_)
    (hnext _ cap vecPtr e1 (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      (by simp [wp_norm, arm64_norm, hsp_ret]) (by simpa [wp_norm, arm64_norm, hsp_ret] using hsp_align)
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by have hx28_1 := hcs1.readReg64_x28; have hv_1 := hcs1.vregs
          simp only [wp_norm, arm64_norm] at hx28_1 hv_1
          simp [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm, hx28_1, hv_1])
      hcap_le (by simpa [wp_norm, arm64_norm] using hopen1)
      (by simp [wp_norm, arm64_norm]; rw [htr1]; simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]; rw [htp1]; simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]; rw [hsig1]; simp [wp_norm, arm64_norm])
      ((hkf0.trans hkf1).trans hkf2))
  simp only [muslErrnoAddr, wp_norm, arm64_norm] at hm ⊢; dsimp only [HbStdinLockedRest]
  rw [show hbBufReaderReadStackBytes = hbDefaultReadStackBytes + 8 * 16 from rfl,
      stackAt_split_cells s.sp hbDefaultReadStackBytes 16 (by decide),
      show s.sp - BitVec.ofNat 64 (8 * 16) = s1.sp from hsp_b_def]
  repack_cells

private theorem stdHeapTransport {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) {γ : GhostName} {lc blk : Nat} {s0 sf : State}
    (h : StdStatePreserved s0 sf) : M.Heap γ lc blk s0 ⊢ M.Heap γ lc blk sf :=
  M.heap_transport h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2

/-- Placement-generic `SepWP` specification for `<Stdin as Read>::read_to_end`
    (`C.stdinReadToEndAddr`, `hbStdinReadToEndChunks C`). -/
theorem stdinReadToEnd_wp {P : Program} {C : HbCliLayout} {L : Nat}
    {target_pc ret_pc sp_call : BitVec 64}
    (hV : C.Valid) (hc : HbUserMainCode P C) (hc_stdin : HbStdinAndVecCode P C)
    (hc_sys : HbSyscallsAndStderrCode P C) (hMem : StdMemOps P C.std.memcpyAddr C.std.memsetAddr)
    (hatom : StdOutlineAtomics P C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
      C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr)
    (M : HbMallocngIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    {selfPtr vecSlotPtr ptr0 : BitVec 64} {lc blk : Nat}
    {stdinBytes : List (BitVec 8)} {haveLse : BitVec 8} {e0 : BitVec 32}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    (hL_eq : stdinBytes.length = L := by rfl) (hL : L ≤ HashbrownCliMaxStdin)
    (hlc_le : lc ≤ mallocngBlockCost 1024 + mallocngBlockCost 8192 := by omega)
    (hblk_le : blk ≤ 2 := by omega)
    (hpc : s.pc = C.stdinReadToEndAddr) (hrun : s.status = .Running)
    (hsp_call : s.sp = sp_call) (hsp_align : s.spAligned = true)
    (hsp_lo : 480 ≤ sp_call.toNat) (hsp_va : sp_call.toNat ≤ Arm64.USER_VA_LIMIT)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = selfPtr) (hx1 : s.readReg64 .x1 = vecSlotPtr)
    (hopen : HbStdinOpen stdinBytes s.fs)
    (hpre : Pre ⊢ (selfPtr ↦₆₄ C.stdinGlobalAddr) ∗ HbStdinInv C M.toMallocngCoreIface γ true ∗
      HbByteVec M.toMallocngCoreIface γ vecSlotPtr 0 ptr0 [] ∗ M.Heap γ lc blk s ∗
      (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      (muslErrnoAddr s ↦₃₂ e0) ∗ stackAt sp_call hbStdinReadStackBytes ∗ F)
    (hnext : ∀ (sf : State) (cap : Nat) (vecPtr : BitVec 64) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.spAligned = true →
      sf.readReg64 .x0 = 0#64 → sf.readReg64 .x1 = BitVec.ofNat 64 stdinBytes.length →
      CalleeSavedPreserved s sf → cap ≤ 2 * stdinBytes.length + 32 → HbStdinOpen [] sf.fs →
      sf.trace = s.trace → sf.tpidrEl0 = s.tpidrEl0 → sf.sigActions = s.sigActions →
      s.mem.KeepsFrozen sf.mem →
      SepWP P target_pc sf
        ((selfPtr ↦₆₄ C.stdinGlobalAddr) ∗ HbStdinInv C M.toMallocngCoreIface γ true ∗
          HbByteVec M.toMallocngCoreIface γ vecSlotPtr cap vecPtr stdinBytes ∗
          M.Heap γ (lc + hbByteVecCost cap) (blk + hbByteVecBlocks cap) sf ∗
          (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt sp_call hbStdinReadStackBytes ∗ F) post) :
    SepWP P target_pc s Pre post := by
  cases hsp_call; cases hlr; subst hL_eq
  obtain ⟨sp_s, hsp_s_def⟩ : ∃ sp_s, s.sp - 64#64 = sp_s := ⟨_, rfl⟩
  have hsp_s_al : ((sp_s &&& 15#64) == 0#64) = true := hsp_s_def ▸ s.spAligned_sub 64#64 hsp_align
  have hx0' : s.readReg64 (.gpr 0#5) = selfPtr := hx0
  have hx1' : s.readReg64 (.gpr 1#5) = vecSlotPtr := hx1
  refine SepWP.seq (mid := s.readReg64 Reg.lr)
    (Mid := fun sf Pf => ∃ cap vecPtr e1, s.mem.KeepsFrozen sf.mem ∧
      cap ≤ 2 * stdinBytes.length + 32 ∧ HbStdinOpen [] sf.fs ∧
      sf.sp = s.sp ∧ sf.spAligned = true ∧
      sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = BitVec.ofNat 64 stdinBytes.length ∧
      CalleeSavedPreserved s sf ∧ sf.trace = s.trace ∧ sf.tpidrEl0 = s.tpidrEl0 ∧
      sf.sigActions = s.sigActions ∧
      (∀ (R : SepProp) {m : Memory}, (m ⊨ Pf ∗ R) →
        (m ⊨ ((selfPtr ↦₆₄ C.stdinGlobalAddr) ∗ HbStdinInv C M.toMallocngCoreIface γ true ∗
          HbByteVec M.toMallocngCoreIface γ vecSlotPtr cap vecPtr stdinBytes ∗
          M.Heap γ (lc + hbByteVecCost cap) (blk + hbByteVecBlocks cap) sf ∗
          (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt s.sp hbStdinReadStackBytes ∗ F) ∗ R)))
    (SepWP.with_keepsFrozen ?_) ?_
  · apply SepWP.weaken_pre hpre
    apply sepWP_mono_atom (HbStdinInv_true_unpack C M.toMallocngCoreIface γ)
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_left fun bufPtr => ?_
    conv => arg 4; simp only [sepConj_assoc, sepConj_pull_pure]
    refine SepWP.pure_elim fun hbuf => ?_
    conv => arg 4; rw [show hbStdinReadStackBytes = hbBufReaderReadStackBytes + 8 * 8 from rfl,
      stackAt_split_cells s.sp hbBufReaderReadStackBytes 8 (by decide),
      show s.sp - BitVec.ofNat 64 (8 * 8) = sp_s from hsp_s_def]
    unpack_cells 8
    refine SepWP.seq_nonVm (mid := C.std.cas4AcqAddr) hext hsvc ?_
    have hc_nv1 := (hc.withSvc nonVmSvc).stdinReadToEnd
    unpack_hb_subchunks hbStdinReadToEndChunks hc_nv1 [0, 1]
    wp_steps
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) (fun hvm1 => ?_)
    apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm1)
    have hsp0_eq : s.sp + (-64#64 : BitVec 64) = sp_s := by rw [← hsp_s_def]; bv_lin
    refine call_stdCas4 hatom.cas4Acq_ok
      (haveLse := haveLse) (ptr := C.stdinGlobalAddr) (v0 := 0#32) (exp := 0#32) (new := 1#32)
      (ret_pc := C.stdinReadToEndAddr + 0x2c#64) (by simp only [wp_norm, arm64_norm]; sep_frame)
      (fun s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hst1 => ?_)
      (hpc := wp_a) (hrun := by simp [wp_norm, arm64_norm, hrun])
      (hsp_align := by simpa [State.spAligned, wp_norm, arm64_norm, hsp0_eq, hsp_s_def] using hsp_s_al)
      (hlr := by simp [wp_norm, arm64_norm]) (hx0 := by simp [wp_norm, arm64_norm])
      (hx1 := by simp [wp_norm, arm64_norm]) (hx2 := by simp [wp_norm, arm64_norm])
      (halign := stdinGlobal_isAligned32 hV)
    apply sepWP_mono_atom (stdHeapTransport M.toMallocngCoreIface hst1)
    conv => arg 4; simp only [beq_self_eq_true, ↓reduceIte, HbStdinLockedRest]
    have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1
    have hx19_1 : s1.readReg64 (.gpr 19#5) = C.stdinGlobalAddr := by
      rw [hcs1.readReg64_x19]; simp [wp_norm, arm64_norm]
    have hx20_1 : s1.readReg64 (.gpr 20#5) = vecSlotPtr := by
      rw [hcs1.readReg64_x20]; simp [wp_norm, arm64_norm]
    refine SepWP.memRegion4_cell (C.stdinGlobalAddr + 0x04#64) (fun w_pad => ?_)
    conv => arg 4; rw [pointsTo32_split8 (C.stdinGlobalAddr + 0x04#64) w_pad]
    refine SepWP.seq_nonVm (mid := C.bufReaderReadToEndAddr) hext hsvc ?_
    have hc_nv2 := (hc.withSvc nonVmSvc).stdinReadToEnd
    unpack_hb_subchunks hbStdinReadToEndChunks hc_nv2 [2, 3, 4, 5]
    iterate 4 (wp_steps; (try norm_jmp))
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun1]) (fun hvm2 => ?_)
    have hpad : ((C.stdinGlobalAddr + 0x04#64) ↦₈ w_pad.extractLsb' 0 8) ∗
        ((C.stdinGlobalAddr + 0x04#64 + 1#64) ↦₈ w_pad.extractLsb' 8 8) ∗
        ((C.stdinGlobalAddr + 0x04#64 + 2#64) ↦₈ w_pad.extractLsb' 16 8) ∗
        ((C.stdinGlobalAddr + 0x04#64 + 3#64) ↦₈ w_pad.extractLsb' 24 8) ⊢
        memRegion (C.stdinGlobalAddr + 0x04#64) 4 := by
      rw [← pointsTo32_split8]; exact pointsTo32_entails_memRegion _ _
    apply sepWP_mono_atom hpad
    apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm2)
    have hsp1_eq : s1.sp = sp_s := by rw [hsp1, ← hsp_s_def]; simp only [wp_norm, arm64_norm]
    have hopen1 : HbStdinOpen stdinBytes s1.fs := by rw [hst1.1]; simpa [wp_norm, arm64_norm] using hopen
    have htp01 : s.tpidrEl0 = s1.tpidrEl0 := by
      have h := hst1.2.2.1; simp only [wp_norm, arm64_norm] at h; exact h.symm
    have hsp_s_lo : 416 ≤ sp_s.toNat := by
      rw [← hsp_s_def]; bv_omega
    have hsp_s_va : sp_s.toNat ≤ Arm64.USER_VA_LIMIT := by
      rw [← hsp_s_def]; unfold Arm64.USER_VA_LIMIT at hsp_va ⊢; bv_omega
    refine bufReaderReadToEnd_wp hc hc_stdin hc_sys hMem M γ
      (bufPtr := bufPtr) (vecSlotPtr := vecSlotPtr) (ptr0 := ptr0) (lc := lc) (blk := blk)
      (stdinBytes := stdinBytes) (e0 := e0) (sp_call := sp_s) (ret_pc := C.stdinReadToEndAddr + 0x5c#64)
      hsvc hext rfl hL hlc_le hblk_le wp_a (by simp [wp_norm, arm64_norm, hrun1])
      (by simpa [wp_norm, arm64_norm] using hsp1_eq)
      (by simpa [State.spAligned, wp_norm, arm64_norm, hsp1_eq] using hsp_s_al)
      hsp_s_lo hsp_s_va
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simpa [wp_norm, arm64_norm] using hopen1)
      (by dsimp only [HbStdinLockedRest]; simp only [muslErrnoAddr, htp01, wp_norm, arm64_norm]; sep_frame)
      (fun s2 cap vecPtr e1 hpc2 hrun2 hsp2 hal2 hx0_2 hx1_2 hcs2 hcap_le hopen2 htr2 htp2 hsig2 _ => ?_)
    have hx0_2' : s2.readReg64 (.gpr 0#5) = 0#64 := hx0_2
    have hx1_2' : s2.readReg64 (.gpr 1#5) = BitVec.ofNat 64 stdinBytes.length := hx1_2
    have hx19_2 : s2.readReg64 (.gpr 19#5) = C.stdinGlobalAddr := by
      rw [hcs2.readReg64_x19]; simp [wp_norm, arm64_norm, hx19_1]
    have hx22_2 : s2.readReg64 (.gpr 22#5) = 0#64 := by rw [hcs2.readReg64_x22]; simp [wp_norm, arm64_norm]
    have hx23_2 : s2.readReg64 (.gpr 23#5) = C.globalPanicCountAddr := by rw [hcs2.readReg64_x23]; exact wp_a
    refine SepWP.seq_nonVm (mid := C.std.swp4RelAddr) hext hsvc ?_
    have hc_nv3 := (hc.withSvc nonVmSvc).stdinReadToEnd
    unpack_hb_subchunks hbStdinReadToEndChunks hc_nv3 [6, 7]
    iterate 2 (wp_steps; (try norm_jmp))
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun2]) (fun hvm3 => ?_)
    apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm3)
    refine call_stdSwp4 hatom.swp4Rel_ok
      (haveLse := haveLse) (ptr := C.stdinGlobalAddr) (v0 := 1#32) (new := 0#32)
      (ret_pc := C.stdinReadToEndAddr + 0x80#64) (by simp only [wp_norm, arm64_norm]; sep_frame)
      (fun s3 hpc3 hrun3 hsp3 hcs3 hx0_3 hst3 => ?_)
      (hpc := wp_a) (hrun := by simp [wp_norm, arm64_norm, hrun2])
      (hsp_align := by simpa [State.spAligned, wp_norm, arm64_norm] using hal2)
      (hlr := by simp [wp_norm, arm64_norm]) (hx0 := by simp [wp_norm, arm64_norm])
      (hx1 := by simp [wp_norm, arm64_norm]) (halign := stdinGlobal_isAligned32 hV)
    apply sepWP_mono_atom (stdHeapTransport M.toMallocngCoreIface hst3)
    have hsp3_eq : s3.sp = sp_s := by rw [hsp3]; simpa [wp_norm, arm64_norm] using hsp2
    clear hsp0_eq hsp1 hsp1_eq hsp2 hsp3; subst hsp3_eq
    have hx0_3' : s3.readReg64 (.gpr 0#5) = 1#64 := hx0_3
    have hx20_3 : s3.readReg64 (.gpr 20#5) = 0#64 := by rw [hcs3.readReg64_x20]; simp [wp_norm, arm64_norm]
    have hx21_3 : s3.readReg64 (.gpr 21#5) = BitVec.ofNat 64 stdinBytes.length := by
      rw [hcs3.readReg64_x21]; simp [wp_norm, arm64_norm]
    refine SepWP.seq_nonVm (mid := s.readReg64 Reg.lr) hext hsvc ?_
    have hc_nv4 := (hc.withSvc nonVmSvc).stdinReadToEnd
    unpack_hb_subchunks hbStdinReadToEndChunks hc_nv4 [8]
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun3]) (fun hvm4 => ?_)
    apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm4)
    apply sepWP_mono_atom (HbStdinLockedRest_repack C M.toMallocngCoreIface γ hbuf)
    have hsp_ret : s3.sp + 64#64 = s.sp := by rw [← hsp_s_def]; bv_lin
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun3]) (fun hkf => ?_)
    refine ⟨cap, vecPtr, e1, hkf, hcap_le,
      by simp only [wp_norm, arm64_norm]; rw [hst3.1]; simpa [wp_norm, arm64_norm] using hopen2,
      by simp [wp_norm, arm64_norm, hsp_ret],
      by simpa [wp_norm, arm64_norm, hsp_ret] using hsp_align,
      by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], ?_, ?_, ?_, ?_, ?_⟩
    · have h24_1 := hcs1.readReg64_x24; have h25_1 := hcs1.readReg64_x25
      have h26_1 := hcs1.readReg64_x26; have h27_1 := hcs1.readReg64_x27
      have h28_1 := hcs1.readReg64_x28; have hv_1 := hcs1.vregs
      have h24_2 := hcs2.readReg64_x24; have h25_2 := hcs2.readReg64_x25
      have h26_2 := hcs2.readReg64_x26; have h27_2 := hcs2.readReg64_x27
      have h28_2 := hcs2.readReg64_x28; have hv_2 := hcs2.vregs
      have h24_3 := hcs3.readReg64_x24; have h25_3 := hcs3.readReg64_x25
      have h26_3 := hcs3.readReg64_x26; have h27_3 := hcs3.readReg64_x27
      have h28_3 := hcs3.readReg64_x28; have hv_3 := hcs3.vregs
      simp only [wp_norm, arm64_norm] at h24_1 h25_1 h26_1 h27_1 h28_1 hv_1
      simp only [wp_norm, arm64_norm] at h24_2 h25_2 h26_2 h27_2 h28_2 hv_2
      simp only [wp_norm, arm64_norm] at h24_3 h25_3 h26_3 h27_3 h28_3 hv_3
      simp [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm,
        h24_1, h25_1, h26_1, h27_1, h28_1, hv_1,
        h24_2, h25_2, h26_2, h27_2, h28_2, hv_2,
        h24_3, h25_3, h26_3, h27_3, h28_3, hv_3]
    · simp only [wp_norm, arm64_norm]; rw [hst3.2.1]; simp only [wp_norm, arm64_norm]
      rw [htr2]; simp only [wp_norm, arm64_norm]; rw [hst1.2.1]; simp [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm]; rw [hst3.2.2.1]; simp only [wp_norm, arm64_norm]
      rw [htp2]; simp only [wp_norm, arm64_norm]; rw [hst1.2.2.1]; simp [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm]; rw [hst3.2.2.2.1]; simp only [wp_norm, arm64_norm]
      rw [hsig2]; simp only [wp_norm, arm64_norm]; rw [hst1.2.2.2.1]; simp [wp_norm, arm64_norm]
    · intro R m hm
      have htp23 : s2.tpidrEl0 = s3.tpidrEl0 := by
        have h := hst3.2.2.1; simp only [wp_norm, arm64_norm] at h; exact h.symm
      simp only [muslErrnoAddr, htp23, wp_norm, arm64_norm] at hm ⊢
      rw [show hbStdinReadStackBytes = hbBufReaderReadStackBytes + 8 * 8 from rfl,
          stackAt_split_cells s.sp hbBufReaderReadStackBytes 8 (by decide),
          show s.sp - BitVec.ofNat 64 (8 * 8) = s3.sp from hsp_s_def]
      repack_cells
  · rintro sf Pf hpc_f hrun_f ⟨cap, vecPtr, e1, hkf, hcap_le, hopen_f, hsp_f, hal_f,
      hx0_f, hx1_f, hcs_f, htr_f, htp_f, hsig_f, hPf⟩
    exact SepWP.weaken_pre_frame (fun R hm => hPf R hm)
      (hnext sf cap vecPtr e1 hpc_f hrun_f hsp_f hal_f hx0_f hx1_f hcs_f hcap_le hopen_f
        htr_f htp_f hsig_f hkf)

/-! ## `hashbrown_cli::main` prologue and `stdin().read_to_end` -/

private theorem hbByteVec_init_one {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) (γ : GhostName) (sp_m : BitVec 64) :
    ((sp_m + 0x08#64) ↦₆₄ 0#64) ∗ ((sp_m + 0x10#64) ↦₆₄ 1#64) ∗ ((sp_m + 0x18#64) ↦₆₄ 0#64) ⊢
      HbByteVec M γ (sp_m + 0x08#64) 0 1#64 [] := by
  dsimp only [HbByteVec, HbByteVecBuf]
  simp only [↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd]
  rw [sepConj_comm _ ⌜_⌝]; (repeat rw [sepConj_pull_pure])
  exact Entails.pure_right ⟨trivial, by decide⟩ (by sep_entail)

private theorem hbMainSavedRegs_intro (sp_m : BitVec 64) (s_main : State) :
    ((sp_m + 0x80#64) ↦₆₄ s_main.readReg64 (.gpr 29#5)) ∗ ((sp_m + 0x88#64) ↦₆₄ s_main.readReg64 (.gpr 30#5)) ∗
    ((sp_m + 0x90#64) ↦₆₄ s_main.readReg64 (.gpr 27#5)) ∗ ((sp_m + 0xa0#64) ↦₆₄ s_main.readReg64 (.gpr 26#5)) ∗
    ((sp_m + 0xa8#64) ↦₆₄ s_main.readReg64 (.gpr 25#5)) ∗ ((sp_m + 0xb0#64) ↦₆₄ s_main.readReg64 (.gpr 24#5)) ∗
    ((sp_m + 0xb8#64) ↦₆₄ s_main.readReg64 (.gpr 23#5)) ∗ ((sp_m + 0xc0#64) ↦₆₄ s_main.readReg64 (.gpr 22#5)) ∗
    ((sp_m + 0xc8#64) ↦₆₄ s_main.readReg64 (.gpr 21#5)) ∗ ((sp_m + 0xd0#64) ↦₆₄ s_main.readReg64 (.gpr 20#5)) ∗
    ((sp_m + 0xd8#64) ↦₆₄ s_main.readReg64 (.gpr 19#5)) ⊢ HbMainSavedRegs sp_m s_main := by
  dsimp only [HbMainSavedRegs, Reg.x29, Reg.lr, Reg.x27, Reg.x26, Reg.x25, Reg.x24,
    Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; sep_entail

/-- Placement-generic `SepWP` specification for `hashbrown_cli::main` from entry
    (`C.std.userMainAddr`) through `io::stdin().read_to_end(&mut input)` (`u + 0xb4#64`)
    on the consolidated `0xe0` (`224`-byte) stack frame. -/
theorem hbMain_readToEnd_wp {P : Program} {C : HbCliLayout} {L : Nat} {target_pc : BitVec 64}
    (hV : C.Valid) (hc : HbUserMainCode P C) (hc_stdin : HbStdinAndVecCode P C)
    (hc_sys : HbSyscallsAndStderrCode P C) (honce : HbOnceCallCode P C)
    (hatom : StdOutlineAtomics P C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
      C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr)
    (hMem : StdMemOps P C.std.memcpyAddr C.std.memsetAddr)
    (M : HbMallocngIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    {lc0 blk0 : Nat} {stdinBytes : List (BitVec 8)} {haveLse : BitVec 8} {e0 : BitVec 32}
    {s_main : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    (_hstdin_nz : C.stdinGlobalAddr ≠ 0#64 := hV.stdinGlobal_nz)
    (hL_eq : stdinBytes.length = L := by rfl) (hL : L ≤ HashbrownCliMaxStdin)
    (hlc0 : lc0 ≤ mallocngBlockCost 1024 := by omega) (hblk0 : blk0 ≤ 1 := by omega)
    (hpc : s_main.pc = C.std.userMainAddr) (hrun : s_main.status = .Running)
    (hsp_al : s_main.spAligned = true)
    (hsp_lo : 1024 ≤ s_main.sp.toNat) (hsp_va : s_main.sp.toNat ≤ Arm64.USER_VA_LIMIT)
    (hopen : HbStdinOpen stdinBytes s_main.fs)
    (hpre : Pre ⊢ HbStdinUninit C ∗
      StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
      (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
      (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ M.Heap γ lc0 blk0 s_main ∗
      (muslErrnoAddr s_main ↦₃₂ e0) ∗ stackAt s_main.sp 261984 ∗ F)
    (hnext : ∀ (s1 : State) (cap : Nat) (vecPtr : BitVec 64) (e1 : BitVec 32) (sp_m : BitVec 64),
      sp_m = s_main.sp - 0xe0#64 → s1.pc = C.std.userMainAddr + 0xb4#64 → s1.status = .Running →
      s1.sp = sp_m → s1.spAligned = true → cap ≤ 2 * stdinBytes.length + 32 → HbStdinOpen [] s1.fs →
      s1.readReg64 .x28 = s_main.readReg64 .x28 → s1.readReg64 .x29 = sp_m + 0x80#64 →
      calleeSavedVRegs s1 = calleeSavedVRegs s_main → s1.trace = s_main.trace →
      s1.tpidrEl0 = s_main.tpidrEl0 → s1.sigActions = s_main.sigActions →
      s_main.mem.KeepsFrozen s1.mem →
      SepWP P target_pc s1
        (HbByteVec M.toMallocngCoreIface γ (sp_m + 0x08#64) cap vecPtr stdinBytes ∗
          memRegion sp_m 8 ∗ HbMainSavedRegs sp_m s_main ∗ memRegion (sp_m + 0x98#64) 8 ∗
          stackAt (sp_m + 0x80#64) 96 ∗ stackAt sp_m (261984 - 224) ∗
          M.Heap γ (lc0 + mallocngBlockCost 8192 + hbByteVecCost cap)
            (blk0 + 1 + hbByteVecBlocks cap) s1 ∗
          HbStdinInv C M.toMallocngCoreIface γ true ∗ ((C.stdinGlobalAddr + 0x34#64) ↦₃₂ 0#32) ∗
          StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
          (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ (C.globalPanicCountAddr ↦₆₄ᵣ 0#64) ∗
          (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (muslErrnoAddr s1 ↦₃₂ e1) ∗ F) post) :
    SepWP P target_pc s_main Pre post := by
  subst hL_eq
  obtain ⟨sp_m, hsp_m⟩ : ∃ sp_m, s_main.sp - 0xe0#64 = sp_m := ⟨_, rfl⟩
  have hsp_m_al : ((sp_m &&& 15#64) == 0#64) = true := hsp_m ▸ s_main.spAligned_sub 0xe0#64 hsp_al
  apply SepWP.weaken_pre hpre
  conv => arg 4; dsimp only [HbStdinUninit]; rw [hbMainStack_split s_main.sp hsp_m.symm]
  apply sepWP_mono_atom (HbStdinInv_init C M.toMallocngCoreIface γ)
  unpack_cells 14
  refine seq_nonVm_kf (mid := C.stdioStdinAddr) hext hsvc ?_
  have hc_nv1 := (hc.withSvc nonVmSvc).rustMain
  unpack_hb_subchunks hbRustMainReadScanChunks hc_nv1 [0, 1]
  iterate 2 (wp_steps; (try norm_jmp))
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) (fun hvm1 hkf1 => ?_)
  apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm1)
  apply sepWP_mono_atom (hbByteVec_init_one M.toMallocngCoreIface γ sp_m)
  apply sepWP_mono_atom (hbMainSavedRegs_intro sp_m s_main)
  have hsp0_eq : s_main.sp - 224#64 = sp_m := hsp_m
  conv => arg 4; rw [stackAt_split_main sp_m hbStdioStdinStackBytes (261984 - 224 - hbStdioStdinStackBytes)]
  refine stdioStdin_wp hV hc hc_stdin honce hatom M.toMallocngCoreIface γ
    (init := false) (lc := lc0) (blk := blk0) (haveLse := haveLse) (e0 := e0)
    (ret_pc := C.std.userMainAddr + 0x30#64) hsvc hext
    (fun _ => by
      have : stdinBytes.length ≤ 10737418240 := hL
      dsimp only [hbStdLimits, mallocngBlockCost, MallocngMinBlockCost] at hlc0 ⊢; omega)
    wp_a (by simp [wp_norm, arm64_norm, hrun])
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp0_eq] using hsp_m_al)
    (by simp [wp_norm, arm64_norm]) (by simp [muslErrnoAddr, wp_norm, arm64_norm]; sep_frame)
    (fun s_in e_in hpc_in hrun_in hsp_in hx0_in hcs_in hmsp_in => ?_)
  have hsp_in' : s_in.sp = sp_m := by rw [hsp_in]; simp [wp_norm, arm64_norm]
  have hstk_in : stackAt s_in.sp hbStdioStdinStackBytes ∗
      stackAt (sp_m - BitVec.ofNat 64 hbStdioStdinStackBytes) (261984 - 224 - hbStdioStdinStackBytes) ⊢
      stackAt sp_m (261984 - 224) := by
    rw [hsp_in', stackAt_split_main sp_m hbStdioStdinStackBytes
      (261984 - 224 - hbStdioStdinStackBytes) (n := 261984 - 224)]; sep_entail
  have hx0_in' : s_in.readReg64 (.gpr 0#5) = C.stdinGlobalAddr := hx0_in
  have hx28_in : s_in.readReg64 (.gpr 28#5) = s_main.readReg64 (.gpr 28#5) := by
    rw [hcs_in.readReg64_x28]; simp [wp_norm, arm64_norm]
  have hx29_in : s_in.readReg64 (.gpr 29#5) = sp_m + 0x80#64 := by
    rw [hcs_in.readReg64_x29]; simp [wp_norm, arm64_norm]
  have hv_in : calleeSavedVRegs s_in = calleeSavedVRegs s_main := by
    rw [hcs_in.vregs]; simp [wp_norm, arm64_norm]
  apply sepWP_mono_atom hstk_in
  conv => arg 4; rw [stackAt96_split_slot20 sp_m]
  unpack_cells 1
  refine seq_nonVm_kf (mid := C.stdinReadToEndAddr) hext hsvc ?_
  have hc_nv2 := (hc.withSvc nonVmSvc).rustMain
  unpack_hb_subchunks hbRustMainReadScanChunks hc_nv2 [2, 3]
  iterate 2 (wp_steps; (try norm_jmp))
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun_in]) (fun hvm2 hkf2 => ?_)
  apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm2)
  conv => arg 4; rw [stackAt_split_main sp_m hbStdinReadStackBytes (261984 - 224 - hbStdinReadStackBytes)]
  have hopen_in : HbStdinOpen stdinBytes s_in.fs := by
    rw [hmsp_in.1]; simpa [wp_norm, arm64_norm] using hopen
  have hsp_m_lo : 480 ≤ sp_m.toNat := by
    rw [← hsp_m]; bv_omega
  have hsp_m_va : sp_m.toNat ≤ Arm64.USER_VA_LIMIT := by
    rw [← hsp_m]; unfold Arm64.USER_VA_LIMIT at hsp_va ⊢; bv_omega
  refine stdinReadToEnd_wp hV hc hc_stdin hc_sys hMem hatom M γ
    (selfPtr := sp_m + 0x20#64) (vecSlotPtr := sp_m + 0x08#64) (ptr0 := 1#64)
    (lc := lc0 + mallocngBlockCost 8192) (blk := blk0 + 1)
    (stdinBytes := stdinBytes) (haveLse := haveLse) (e0 := e_in) (sp_call := sp_m)
    (ret_pc := C.std.userMainAddr + 0x40#64) hsvc hext rfl hL (by omega) (by omega)
    wp_a (by simp [wp_norm, arm64_norm, hrun_in]) (by simpa [wp_norm, arm64_norm] using hsp_in')
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp_in'] using hsp_m_al)
    hsp_m_lo hsp_m_va
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simpa [wp_norm, arm64_norm] using hopen_in)
    (by simp [muslErrnoAddr, wp_norm, arm64_norm]; sep_frame)
    (fun s_rd cap vecPtr e1 hpc_rd hrun_rd hsp_rd hal_rd hx0_rd _hx1_rd hcs_rd
         hcap_le hopen_rd htr_rd htp_rd hsig_rd hkf_rd => ?_)
  have hstk_rd : stackAt sp_m hbStdinReadStackBytes ∗
      stackAt (sp_m - BitVec.ofNat 64 hbStdinReadStackBytes) (261984 - 224 - hbStdinReadStackBytes) ⊢
      stackAt sp_m (261984 - 224) := by
    rw [stackAt_split_main sp_m hbStdinReadStackBytes
      (261984 - 224 - hbStdinReadStackBytes) (n := 261984 - 224)]; sep_entail
  apply sepWP_mono_atom hstk_rd
  apply sepWP_mono_atom (stackAt96_repack_slot20 sp_m C.stdinGlobalAddr)
  have hx0_rd' : s_rd.readReg64 (.gpr 0#5) = 0#64 := hx0_rd
  have hx28_rd : s_rd.readReg64 (.gpr 28#5) = s_main.readReg64 (.gpr 28#5) := by
    rw [hcs_rd.readReg64_x28]; simpa [wp_norm, arm64_norm] using hx28_in
  have hx29_rd : s_rd.readReg64 (.gpr 29#5) = sp_m + 0x80#64 := by
    rw [hcs_rd.readReg64_x29]; simpa [wp_norm, arm64_norm] using hx29_in
  have hv_rd : calleeSavedVRegs s_rd = calleeSavedVRegs s_main := by
    rw [hcs_rd.vregs]; simpa [wp_norm, arm64_norm] using hv_in
  refine seq_nonVm_kf (mid := C.std.userMainAddr + 0xb4#64) hext hsvc ?_
  have hc_nv3 := (hc.withSvc nonVmSvc).rustMain
  unpack_hb_subchunks hbRustMainReadScanChunks hc_nv3 [4]
  wp_steps; (try norm_jmp)
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun_rd]) (fun hvm3 hkf3 => ?_)
  apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm3)
  have hkf_all : s_main.mem.KeepsFrozen (s_rd.setPC (C.std.userMainAddr + 0xb4#64)).mem :=
    (((hkf1.trans hmsp_in.2.2.2.2).trans hkf2).trans hkf_rd).trans hkf3
  refine SepWP.weaken_pre (by simp [muslErrnoAddr, wp_norm, arm64_norm]; sep_entail)
    (hnext _ cap vecPtr e1 sp_m hsp_m.symm (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun_rd]) (by simpa [wp_norm, arm64_norm] using hsp_rd)
      (by simpa [State.spAligned, wp_norm, arm64_norm] using hal_rd) hcap_le
      (by simpa [wp_norm, arm64_norm] using hopen_rd)
      (by simpa [Reg.x28, wp_norm, arm64_norm] using hx28_rd)
      (by simpa [Reg.x29, wp_norm, arm64_norm] using hx29_rd)
      (by simpa [wp_norm, arm64_norm] using hv_rd)
      (by simp only [wp_norm, arm64_norm]; rw [htr_rd]; simp only [wp_norm, arm64_norm]
          rw [hmsp_in.2.1]; simp [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]; rw [htp_rd]; simp only [wp_norm, arm64_norm]
          rw [hmsp_in.2.2.2.1]; simp [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]; rw [hsig_rd]; simp only [wp_norm, arm64_norm]
          rw [hmsp_in.2.2.1]; simp [wp_norm, arm64_norm]) hkf_all)

/-! ## `MaxLineLen` scan and early-exit dispatch -/

private structure ScanCpuPreserved (s0 sf : State) : Prop where
  sp_eq : sf.sp = s0.sp
  vregs_eq : calleeSavedVRegs sf = calleeSavedVRegs s0
  x28_eq : sf.readReg64 .x28 = s0.readReg64 .x28
  x29_eq : sf.readReg64 .x29 = s0.readReg64 .x29
  fs_eq : sf.fs = s0.fs
  trace_eq : sf.trace = s0.trace
  tpidrEl0_eq : sf.tpidrEl0 = s0.tpidrEl0
  sigActions_eq : sf.sigActions = s0.sigActions
  brk_eq : sf.brk = s0.brk
  brkStart_eq : sf.brkStart = s0.brkStart
  physMemAvail_eq : sf.physMemAvail = s0.physMemAvail
  mem_eq : sf.mem = s0.mem

private theorem ScanCpuPreserved.refl (s : State) : ScanCpuPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem ScanCpuPreserved.toNonVm {s0 sf : State} (h : ScanCpuPreserved s0 sf) :
    HbNonVmPreserved s0 sf :=
  ⟨h.tpidrEl0_eq, h.sigActions_eq,
    ⟨h.brk_eq, h.brkStart_eq, h.physMemAvail_eq, fun _ => by rw [h.mem_eq]⟩,
    h.mem_eq ▸ Memory.KeepsFrozen.refl s0.mem⟩

private theorem ScanCpuPreserved.setPC {s0 s : State} (pc : BitVec 64) :
    ScanCpuPreserved s0 (s.setPC pc) ↔ ScanCpuPreserved s0 s := by
  constructor <;> intro h <;> exact ⟨h.sp_eq, h.vregs_eq, h.x28_eq, h.x29_eq, h.fs_eq,
    h.trace_eq, h.tpidrEl0_eq, h.sigActions_eq, h.brk_eq, h.brkStart_eq, h.physMemAvail_eq, h.mem_eq⟩

private theorem ScanCpuPreserved.setPState {s0 s : State} (ps : PState) :
    ScanCpuPreserved s0 (s.setPState ps) ↔ ScanCpuPreserved s0 s := by
  constructor <;> intro h <;> exact ⟨h.sp_eq, h.vregs_eq, h.x28_eq, h.x29_eq, h.fs_eq,
    h.trace_eq, h.tpidrEl0_eq, h.sigActions_eq, h.brk_eq, h.brkStart_eq, h.physMemAvail_eq, h.mem_eq⟩

private theorem ScanCpuPreserved.writeGpr {s0 s : State} (n : BitVec 5) (v : BitVec 64)
    (h28 : n ≠ 28#5) (h29 : n ≠ 29#5) :
    ScanCpuPreserved s0 (s.writeReg64 (.gpr n) v) ↔ ScanCpuPreserved s0 s := by
  have hr28 : (s.writeReg64 (.gpr n) v).readReg64 .x28 = s.readReg64 .x28 := by
    simp [wp_norm, arm64_norm, h28.symm]
  have hr29 : (s.writeReg64 (.gpr n) v).readReg64 .x29 = s.readReg64 .x29 := by
    simp [wp_norm, arm64_norm, h29.symm]
  constructor <;> intro h <;> exact ⟨h.sp_eq, h.vregs_eq, by simpa [hr28] using h.x28_eq,
    by simpa [hr29] using h.x29_eq, h.fs_eq, h.trace_eq, h.tpidrEl0_eq, h.sigActions_eq,
    h.brk_eq, h.brkStart_eq, h.physMemAvail_eq, h.mem_eq⟩

private theorem ult_4096_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ult 4096#64 (BitVec.ofNat 64 n) = decide (MaxLineLen < n) := by
  simp [BitVec.ult, MaxLineLen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; rfl

private theorem byte_ze32_beq_0a (b : BitVec 8) :
    (b.zeroExtend 32 == 10#32) = (b == 0x0a#8) := by
  revert b; decide

private theorem mvn_add_sub_ofNat {rem off k : Nat} (hk : k < rem - off) :
    ~~~ BitVec.ofNat 64 k + BitVec.ofNat 64 (rem - off) =
      BitVec.ofNat 64 (rem - (off + (k + 1))) := by
  have hnot : ~~~ BitVec.ofNat 64 k = -1#64 - BitVec.ofNat 64 k := by bv_bits
  have hsum : BitVec.ofNat 64 (rem - (off + (k + 1))) + (BitVec.ofNat 64 k + 1#64) =
      BitVec.ofNat 64 (rem - off) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 1; omega
  rw [hnot, ← hsum]; bv_lin

private theorem step_ldrb_words_main {prog : Program} {target_pc addr pc pc' vecPtr : BitVec 64}
    {words : List (BitVec 32)} {wIdx : Nat} {w : BitVec 32} {rt rn rm : Reg}
    {bs : List (BitVec 8)} {idx : Nat}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hw : prog.hasCode addr words)
    (hpc_off : pc = addr + BitVec.ofNat 64 (4 * wIdx) := by bv_lin)
    (hget : words[wIdx]? = some w := by rfl)
    (hdec : decode w = some (.ldr .W32 .B8 false rt (.RegOffset rn rm .UXTX 0)) := by rfl)
    (hrn : rn ≠ .sp := by decide)
    (hidx : idx < bs.length)
    (hpc : s.pc = pc := by simp [wp_norm, arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp [wp_norm, arm64_norm, *])
    (hea : vecPtr + BitVec.ofNat 64 idx = s.readReg64 rn + s.readReg64 rm)
    (hpc' : pc + 4#64 = pc' := by bv_lin)
    (hnext : SepWP prog target_pc
      ((s.writeReg64 rt ((bs[idx]'hidx).zeroExtend 64)).setPC pc')
      ((vecPtr ↦ₛ bs) ∗ F) post oom) :
    SepWP prog target_pc s ((vecPtr ↦ₛ bs) ∗ F) post oom := by
  rw [← hpc'] at hnext
  have hf : prog.fetch pc = some (.ldr .W32 .B8 false rt (.RegOffset rn rm .UXTX 0)) :=
    Program.fetch_of_hasWords_getElem_decode wIdx w hw hpc_off hget hdec
  have hsp : checkAddrSPAligned s (.RegOffset rn rm .UXTX 0) = true := by
    cases rn <;> simp_all [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned]
  have haddr : evalAddrMode s (.RegOffset rn rm .UXTX 0) = (s.readReg64 rn + s.readReg64 rm, none) := by
    simp [evalAddrMode, extendVal]
  have hgetb : bs.getD idx 0#8 = bs[idx]'hidx := by simp [List.getD_eq_getElem?_getD, hidx]
  refine SepWP.step_ldr8 hpc hrun hf hsp haddr
    (SepLoad8.of_pointsToBytes rfl (by omega) hea) ?_ hnext
  dsimp only [applyWriteback, State.writeReg]; rw [hgetb]; congr 2; bv_bits

private theorem hashbrownCliPost_nil {sf : State} (htr : sf.trace = []) :
    HashbrownCliPost [] (ProcessOutcome.ofState 0#64 sf) := by
  unfold HashbrownCliPost splitLines evalLines ProcessOutcome.ofState ProcessOutcome.traceStreamBytes
  simp [htr]

private theorem hashbrownCliPost_of_lineTooLong {stdinBytes : List (BitVec 8)} {sf : State}
    (hany : (splitLines stdinBytes).any (·.length > MaxLineLen) = true)
    (htr : sf.trace = TraceEvent.ofBytes .stderr errLineTooLongBytes) :
    HashbrownCliPost stdinBytes (ProcessOutcome.ofState 1#64 sf) := by
  unfold errLineTooLongBytes at htr
  unfold HashbrownCliPost ProcessOutcome.ofState
  simp [hany, htr]

private theorem hbMain_lineTooLong_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hV : C.Valid) (hc : HbUserMainCode P C) (hcShims : HbShimsCode P C)
    (hc_sys : HbSyscallsAndStderrCode P C)
    (hatom : StdOutlineAtomics P C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
      C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr)
    (M : HbMallocngIface P C.mallocng lim) (γ : GhostName)
    {sp_m vecPtr : BitVec 64} {cap lcRest blkRest : Nat}
    {stdinBytes : List (BitVec 8)} {haveLse : BitVec 8} {e0 : BitVec 32}
    {s_main s_ref s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (hsp_m : sp_m = s_main.sp - 0xe0#64) (hsp_main_al : s_main.spAligned = true)
    (hany : (splitLines stdinBytes).any (·.length > MaxLineLen) = true)
    (hpc : s.pc = C.std.userMainAddr + 0x324#64) (hrun : s.status = .Running)
    (hcpu : ScanCpuPreserved s_ref s) (hsp_ref : s_ref.sp = sp_m)
    (hx28_ref : s_ref.readReg64 .x28 = s_main.readReg64 .x28)
    (hvregs_ref : calleeSavedVRegs s_ref = calleeSavedVRegs s_main)
    (hret : ∀ (s_ret : State) (e_ret : BitVec 32) (Pf : SepProp),
      s_ret.sp = s_main.sp → CalleeSavedPreserved s_main s_ret →
      s_ret.fs = s_ref.fs → s_ret.tpidrEl0 = s_ref.tpidrEl0 →
      s_ret.sigActions = s_ref.sigActions → s_ref.mem.KeepsFrozen s_ret.mem →
      (s_ref.trace = [] → HashbrownCliPost stdinBytes
        (ProcessOutcome.ofState (((s_ret.readReg32 .x0).truncate 8).zeroExtend 64) s_ret)) →
      (Pf ⊢ M.Heap γ lcRest blkRest s_ret ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
        (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗ HbThreadIdInv C s_ret.tpidrEl0 ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        (muslErrnoAddr s_ret ↦₃₂ e_ret) ∗ stackAt s_ret.sp 261984 ∗ F) → post s_ret Pf) :
    SepWP P (s_main.readReg64 .lr) s
      (HbByteVec M.toMallocngCoreIface γ (sp_m + 0x08#64) cap vecPtr stdinBytes ∗
        memRegion sp_m 8 ∗ HbMainSavedRegs sp_m s_main ∗ memRegion (sp_m + 0x98#64) 8 ∗
        stackAt (sp_m + 0x80#64) 96 ∗ stackAt sp_m (261984 - 224) ∗
        M.Heap γ (lcRest + hbByteVecCost cap) (blkRest + hbByteVecBlocks cap) s_ref ∗
        (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗
        HbThreadIdInv C s_ref.tpidrEl0 ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (muslErrnoAddr s_ref ↦₃₂ e0) ∗ F) post := by
  have hsp : s.sp = sp_m := hcpu.sp_eq.trans hsp_ref; cases hsp.symm
  have hsp_al : s.spAligned = true := by
    simp only [State.spAligned, hsp_m]; exact s_main.spAligned_sub 0xe0#64 hsp_main_al
  conv => arg 4; rw [stackAt96_split_slot20 s.sp]
  unpack_cells 1
  refine seq_nonVm_kf (mid := C.stderrWriteAllAddr) hext hsvc ?_
  have hc_nv := (hc.withSvc nonVmSvc).rustMain
  unpack_hb_subchunks hbRustMainReadScanChunks hc_nv [9, 10, 11, 12, 13, 14]
  iterate 6 (try (wp_steps; (try norm_jmp)))
  conv in State.setPC _ _ => arg 2; try rw [bv64_add_sub_cancel]
  conv => arg 4; simp only [bv64_add_sub_cancel]
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) (fun hvm1 hkf1 => ?_)
  conv => arg 4; rw [stackAt_split_main s.sp 256 (261984 - 224 - 256) (n := 261984 - 224),
    ← hcpu.tpidrEl0_eq]
  refine call_hbStderrWriteAll true hc_sys hatom hV.stderrGlobal_align hV.threadIdCtr_align hsvc hext
    (selfPtr := s.sp + 0x20#64) (msgPtr := C.errLineTooLongAddr) (msgBytes := errLineTooLongBytes)
    (haveLse := haveLse) (ret_pc := C.std.userMainAddr + 0x344#64) (by decide) (by decide) hV.errLong_noWrap
    (by dsimp only [hbBytesSlice]; simp only [wp_norm, arm64_norm, bv64_add_sub_cancel]; sep_frame)
    (fun s2 hpc2 hrun2 hsp2 hcs2 hx0_2 hfs2 htr2 hnv2 => ?_)
    (hpc := wp_a) (hrun := by simp [wp_norm, arm64_norm, hrun])
    (hsp_align := by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al)
    (hlr := wp_a) (hx0 := wp_a)
    (hx1 := by simp [wp_norm, arm64_norm, bv64_add_sub_cancel])
    (hx2 := by simp [wp_norm, arm64_norm])
  conv => arg 4; dsimp only [hbBytesSlice]; simp only [wp_norm, arm64_norm, sepConj_assoc]
  have hnv1 : HbNonVmPreserved s _ :=
    ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], hvm1, hkf1⟩
  have hnv02 : HbNonVmPreserved s_ref s2 := (hcpu.toNonVm.trans hnv1).trans hnv2
  have herr2 : muslErrnoAddr s_ref = muslErrnoAddr s2 := by simp [muslErrnoAddr, hnv02.tpidrEl0_eq]
  have htp2 : s.tpidrEl0 = s2.tpidrEl0 := hcpu.tpidrEl0_eq.trans hnv02.tpidrEl0_eq.symm
  have hstk_back : stackAt s.sp 256 ∗ stackAt (s.sp - BitVec.ofNat 64 256) (261984 - 224 - 256) ⊢
      stackAt s.sp (261984 - 224) := by
    rw [stackAt_split_main s.sp 256 (261984 - 224 - 256) (n := 261984 - 224)]; sep_entail
  apply sepWP_mono_atom hstk_back
  apply sepWP_mono_atom (hnv02.heap_transport M.toMallocngCoreIface)
  conv => arg 4; rw [herr2, htp2]
  apply SepWP.weaken_pre (P' :=
      stackAt (s.sp + 0x80#64) 96 ∗
      HbByteVec M.toMallocngCoreIface γ (s.sp + 0x08#64) cap vecPtr stdinBytes ∗
      memRegion s.sp 8 ∗ HbMainSavedRegs s.sp s_main ∗ memRegion (s.sp + 0x98#64) 8 ∗
      stackAt s.sp (261984 - 224) ∗
      M.Heap γ (lcRest + hbByteVecCost cap) (blkRest + hbByteVecBlocks cap) s2 ∗
      (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗
      HbThreadIdInv C s2.tpidrEl0 ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
      (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (muslErrnoAddr s2 ↦₃₂ e0) ∗ F)
    (Entails.trans (by sep_entail) (sepConj_mono_left (stackAt96_repack_slot20 s.sp C.stderrGlobalAddr)))
  have hx0_2' : s2.readReg64 (.gpr 0#5) = 0#64 := by simpa [Reg.x0] using hx0_2
  have hsp2_eq : s2.sp = s.sp := by rw [hsp2]; simp [wp_norm, arm64_norm]
  have hx28_2 : s2.readReg64 .x28 = s_main.readReg64 .x28 := by
    rw [hcs2.readReg64_x28]; simp [wp_norm, arm64_norm]; exact hcpu.x28_eq.trans hx28_ref
  have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s_main := by
    rw [hcs2.vregs]; simp only [wp_norm, arm64_norm]; exact hcpu.vregs_eq.trans hvregs_ref
  have hc_rm := hc.rustMain
  unpack_hb_subchunks hbRustMainReadScanChunks hc_rm [15, 16]
  iterate 3 (try (wp_steps; (try norm_jmp)))
  have hheap_step : M.Heap γ (lcRest + hbByteVecCost cap) (blkRest + hbByteVecBlocks cap) s2 ⊢
      M.Heap γ (lcRest + hbByteVecCost cap) (blkRest + hbByteVecBlocks cap)
        ((s2.writeReg64 (.gpr 19#5) 1#64).setPC (C.std.userMainAddr + 0x78#64)) :=
    M.heap_transport rfl rfl rfl (fun _ => rfl)
  have herr_step : muslErrnoAddr s2 =
      muslErrnoAddr ((s2.writeReg64 (.gpr 19#5) 1#64).setPC (C.std.userMainAddr + 0x78#64)) := rfl
  apply sepWP_mono_atom hheap_step
  conv => arg 4; rw [herr_step]
  refine hbMain_epilogue_wp hc hcShims M.toMallocngCoreIface γ hsvc hext hsp_m hsp_main_al
    wp_a (by simp [wp_norm, arm64_norm, hrun2]) (by simpa [wp_norm, arm64_norm] using hsp2_eq)
    (by simpa [Reg.x28, wp_norm, arm64_norm] using hx28_2)
    (by simpa [wp_norm, arm64_norm] using hvregs_2) (by sep_frame)
    (fun s_ret e_ret Pf hsp_r hx0_r hcs_r hmsp_r hPf => ?_)
  have hx0_val : ((s_ret.readReg32 .x0).truncate 8).zeroExtend 64 = 1#64 := by
    rw [hx0_r]; simp [wp_norm, arm64_norm]
  have htp_ret : s_ret.tpidrEl0 = s2.tpidrEl0 := hmsp_r.2.2.2.1
  have hfs2' : s2.fs = s.fs := by simpa [wp_norm, arm64_norm] using hfs2
  refine hret s_ret e_ret Pf hsp_r hcs_r (hmsp_r.1.trans (hfs2'.trans hcpu.fs_eq))
    (htp_ret.trans hnv02.tpidrEl0_eq) (hmsp_r.2.2.1.trans hnv02.sigActions_eq)
    (Memory.KeepsFrozen.trans hnv02.keepsFrozen hmsp_r.2.2.2.2) (fun hs_tr => ?_)
    (Entails.trans hPf (by rw [← htp_ret]; sep_entail))
  rw [hx0_val]; refine hashbrownCliPost_of_lineTooLong hany ?_
  rw [hmsp_r.2.1]; simp only [wp_norm, arm64_norm]; rw [htr2]
  simp [wp_norm, arm64_norm, hcpu.trace_eq, hs_tr]

private theorem hbMain_scanInner_wp {P : Program} {C : HbCliLayout}
    (hc_rm : CodeChunks P (hbRustMainReadScanChunks C))
    {target_pc vecPtr : BitVec 64} {stdinBytes core : List (BitVec 8)} {coreLen off : Nat}
    {s_ref : State} {F_scan : SepProp} {post : State → SepProp → Prop}
    (hcore : core = stdinBytes.take coreLen)
    (hcore_le : coreLen ≤ stdinBytes.length)
    (hL : stdinBytes.length ≤ HashbrownCliMaxStdin)
    (hlong : ∀ s', (splitOnByte 0x0a#8 (core.drop off)).any (·.length > MaxLineLen) = true →
      s'.pc = C.std.userMainAddr + 0x324#64 → s'.status = .Running →
      ScanCpuPreserved s_ref s' →
      SepWP P target_pc s' ((vecPtr ↦ₛ stdinBytes) ∗ F_scan) post)
    (hdone : ∀ s', (splitOnByte 0x0a#8 (core.drop off)).any (·.length > MaxLineLen) = false →
      s'.pc = C.std.userMainAddr + 0x13c#64 → s'.status = .Running →
      s'.readReg64 .x9 = vecPtr → s'.readReg64 .x22 = BitVec.ofNat 64 coreLen →
      ScanCpuPreserved s_ref s' →
      SepWP P target_pc s' ((vecPtr ↦ₛ stdinBytes) ∗ F_scan) post)
    (hnextLine : ∀ s' (k' : Nat) (_hk' : k' < coreLen - off),
      k' ≤ MaxLineLen →
      (core.drop off)[k']'(by subst hcore; rw [List.length_drop, List.length_take_of_le hcore_le]; omega) = 0x0a#8 →
      (∀ j (_hj : j < k'),
        (core.drop off)[j]'(by subst hcore; rw [List.length_drop, List.length_take_of_le hcore_le]; omega) ≠ 0x0a#8) →
      s'.pc = C.std.userMainAddr + 0xec#64 → s'.status = .Running →
      s'.readReg64 .x8 = BitVec.ofNat 64 (coreLen - (off + (k' + 1))) →
      s'.readReg64 .x9 = vecPtr →
      s'.readReg64 .x10 = vecPtr + BitVec.ofNat 64 (off + (k' + 1)) →
      s'.readReg64 .x11 = 0#64 →
      s'.readReg64 .x22 = BitVec.ofNat 64 coreLen →
      ScanCpuPreserved s_ref s' →
      SepWP P target_pc s' ((vecPtr ↦ₛ stdinBytes) ∗ F_scan) post) :
    ∀ (rem_k k : Nat) (s : State),
      rem_k = coreLen - off - k →
      (hoff : off ≤ coreLen) → (hk : k < coreLen - off) →
      (∀ j (_hj : j < k),
        (core.drop off)[j]'(by subst hcore; rw [List.length_drop, List.length_take_of_le hcore_le]; omega) ≠ 0x0a#8) →
      s.pc = C.std.userMainAddr + 0xf8#64 → s.status = .Running →
      s.readReg64 .x8 = BitVec.ofNat 64 (coreLen - off) →
      s.readReg64 .x9 = vecPtr →
      s.readReg64 .x10 = vecPtr + BitVec.ofNat 64 off →
      s.readReg64 .x12 = BitVec.ofNat 64 k →
      s.readReg64 .x22 = BitVec.ofNat 64 coreLen →
      ScanCpuPreserved s_ref s →
      SepWP P target_pc s ((vecPtr ↦ₛ stdinBytes) ∗ F_scan) post := by
  have hc_scan : P.hasCode (C.std.userMainAddr + 0xb4#64) hbMainScanWords :=
    codeChunks_getElem? hc_rm (i := 8) rfl
  intro rem_k
  induction rem_k using Nat.strongRecOn with
  | ind rem_k ih =>
  intro k s hrem hoff hk hprev hpc hrun hx8 hx9 hx10 hx12 hx22 hcpu
  have hL_bound : stdinBytes.length ≤ 10737418240 := hL
  have hcore_len : core.length = coreLen := by subst hcore; exact List.length_take_of_le hcore_le
  have hdrop_len : (core.drop off).length = coreLen - off := by rw [List.length_drop, hcore_len]
  simp only [arm64_norm] at hx8 hx9 hx10 hx12 hx22
  have hidx : off + k < stdinBytes.length := by omega
  have hb_eq : stdinBytes[off + k]'hidx = (core.drop off)[k]'(by omega) := by
    subst hcore; simp [List.getElem_drop, List.getElem_take]
  refine step_ldrb_words_main (addr := C.std.userMainAddr + 0xb4#64) (words := hbMainScanWords)
    (wIdx := 17) (w := 0x386c694b#32)
    (pc := C.std.userMainAddr + 0xf8#64) (pc' := C.std.userMainAddr + 0xfc#64)
    (vecPtr := vecPtr) (rt := .gpr 11#5) (rn := .gpr 10#5) (rm := .gpr 12#5)
    hc_scan (by bv_lin) rfl rfl (by decide) hidx hpc hrun
    (by rw [hx10, hx12, BitVec.ofNat_add]; bv_lin) (by bv_lin) ?_
  obtain ⟨b, hb_def⟩ : ∃ b, stdinBytes[off + k]'hidx = b := ⟨_, rfl⟩
  rw [hb_def]
  have hk1_add : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by rw [BitVec.ofNat_add]
  unpack_hb_subchunks hbRustMainReadScanChunks hc_rm [8]
  by_cases hbeq : b = 0x0a#8
  · subst hbeq
    iterate 10 (wp_step; (try norm_jmp))
    have hult : BitVec.ult 4096#64 (BitVec.ofNat 64 k) = decide (MaxLineLen < k) := ult_4096_ofNat (by omega)
    have hsub8 : ~~~ BitVec.ofNat 64 k + BitVec.ofNat 64 (coreLen - off) =
        BitVec.ofNat 64 (coreLen - (off + (k + 1))) := mvn_add_sub_ofNat hk
    have hadd10 : vecPtr + BitVec.ofNat 64 off + BitVec.ofNat 64 k + 1#64 =
        vecPtr + BitVec.ofNat 64 (off + (k + 1)) := by
      rw [BitVec.add_assoc _ (BitVec.ofNat 64 k) 1#64, hk1_add, BitVec.add_assoc, ← BitVec.ofNat_add]
    by_cases hgt : MaxLineLen < k
    · have hsplit := splitOnByte_of_first_eq (bs := core.drop off) (sep := 0x0a#8) (k := k)
        (by omega) (hb_eq.symm.trans hb_def) hprev
      have htk : ((core.drop off).take k).length > MaxLineLen := by
        rw [List.length_take_of_le (by omega)]; exact hgt
      have hany : (splitOnByte 0x0a#8 (core.drop off)).any (·.length > MaxLineLen) = true := by
        rw [hsplit, List.any_cons, decide_eq_true htk, Bool.true_or]
      exact hlong _ hany
        (by simp only [wp_norm, arm64_norm, hult, hgt, decide_true, ↓reduceIte]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [ScanCpuPreserved.writeGpr, ScanCpuPreserved.setPC, ScanCpuPreserved.setPState]; exact hcpu)
    · exact hnextLine _ k hk (by omega) (hb_eq.symm.trans hb_def) hprev
        (by simp only [wp_norm, arm64_norm, hult, hgt, decide_false, Bool.false_eq_true, ↓reduceIte]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsub8])
        (by simp [wp_norm, arm64_norm, hx9]) (by simp only [wp_norm, arm64_norm, hadd10])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx22])
        (by simp (config := { decide := true }) only [ScanCpuPreserved.writeGpr, ScanCpuPreserved.setPC, ScanCpuPreserved.setPState]; exact hcpu)
  · have hbeq_f : (b == 0x0a#8) = false := beq_eq_false_iff_ne.mpr hbeq
    have hprev' : ∀ j (hj : j < k + 1), (core.drop off)[j]'(by omega) ≠ 0x0a#8 := by
      intro j hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · exact hprev j hlt
      · rw [← hb_eq, hb_def]; exact hbeq
    iterate 2 (wp_step; (try norm_jmp))
    conv => arg 3; simp only [wp_norm, arm64_norm, byte_ze32_beq_0a, hbeq_f, Bool.false_eq_true, ↓reduceIte]
    iterate 3 (wp_step; (try norm_jmp))
    by_cases hk1 : k + 1 < coreLen - off
    · have hne_bv : (BitVec.ofNat 64 (coreLen - off) != BitVec.ofNat 64 (k + 1)) = true :=
        bne_iff_ne.mpr fun heq => by
          have := congrArg BitVec.toNat heq
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : coreLen - off < 18446744073709551616),
            Nat.mod_eq_of_lt (by omega : k + 1 < 18446744073709551616)] at this; omega
      exact ih (coreLen - off - (k + 1)) (by omega) (k + 1) _ rfl hoff hk1 hprev'
        (by simp only [wp_norm, arm64_norm, hne_bv, ↓reduceIte]; try bv_lin)
        (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hx8])
        (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx10])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx22])
        (by simp (config := { decide := true }) only [ScanCpuPreserved.writeGpr, ScanCpuPreserved.setPC, ScanCpuPreserved.setPState]; exact hcpu)
    · have hk_eq : k + 1 = coreLen - off := by omega
      have hne_bv : (BitVec.ofNat 64 (coreLen - off) != BitVec.ofNat 64 (k + 1)) = false := by
        rw [hk_eq]; simp
      have hsplit : splitOnByte 0x0a#8 (core.drop off) = [core.drop off] :=
        splitOnByte_of_forall_ne (List.ne_nil_of_length_pos (by omega)) (fun j hj => hprev' j (by omega))
      conv => arg 3; simp only [wp_norm, arm64_norm, hx8, hx12, hk1_add, hne_bv, Bool.false_eq_true, ↓reduceIte]
      iterate 5 (wp_step; (try norm_jmp))
      have hult : BitVec.ult 4096#64 (BitVec.ofNat 64 (coreLen - off)) = decide (MaxLineLen < coreLen - off) :=
        ult_4096_ofNat (by omega)
      by_cases hgt : MaxLineLen < coreLen - off
      · have hany : (splitOnByte 0x0a#8 (core.drop off)).any (·.length > MaxLineLen) = true := by
          rw [hsplit]; simp [hdrop_len, hgt]
        exact hlong _ hany
          (by simp only [wp_norm, arm64_norm, hult, hgt, decide_true, ↓reduceIte]; try bv_lin)
          (by simp [wp_norm, arm64_norm, hrun])
          (by simp (config := { decide := true }) only [ScanCpuPreserved.writeGpr, ScanCpuPreserved.setPC, ScanCpuPreserved.setPState]; exact hcpu)
      · have hany : (splitOnByte 0x0a#8 (core.drop off)).any (·.length > MaxLineLen) = false := by
          rw [hsplit]; simp [hdrop_len, hgt]
        conv => arg 3; simp only [wp_norm, arm64_norm, hx8, hult, hgt, decide_false, Bool.false_eq_true, ↓reduceIte]
        wp_step; (try norm_jmp)
        exact hdone _ hany wp_a (by simp [wp_norm, arm64_norm, hrun])
          (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx22])
          (by simp (config := { decide := true }) only [ScanCpuPreserved.writeGpr, ScanCpuPreserved.setPC, ScanCpuPreserved.setPState]; exact hcpu)

private theorem hbMain_scanOuter_wp {P : Program} {C : HbCliLayout}
    (hc_rm : CodeChunks P (hbRustMainReadScanChunks C))
    {target_pc vecPtr : BitVec 64} {stdinBytes core : List (BitVec 8)} {coreLen : Nat}
    {s_ref s0 : State} {F_scan : SepProp} {post : State → SepProp → Prop}
    (hcore : core = stdinBytes.take coreLen)
    (hcore_le : coreLen ≤ stdinBytes.length)
    (hL : stdinBytes.length ≤ HashbrownCliMaxStdin)
    (hlong : ∀ s', (splitOnByte 0x0a#8 core).any (·.length > MaxLineLen) = true →
      s'.pc = C.std.userMainAddr + 0x324#64 → s'.status = .Running →
      ScanCpuPreserved s_ref s' →
      SepWP P target_pc s' ((vecPtr ↦ₛ stdinBytes) ∗ F_scan) post)
    (hdone : ∀ s', (splitOnByte 0x0a#8 core).any (·.length > MaxLineLen) = false →
      s'.pc = C.std.userMainAddr + 0x13c#64 → s'.status = .Running →
      s'.readReg64 .x9 = vecPtr → s'.readReg64 .x22 = BitVec.ofNat 64 coreLen →
      ScanCpuPreserved s_ref s' →
      SepWP P target_pc s' ((vecPtr ↦ₛ stdinBytes) ∗ F_scan) post)
    (hpc0 : s0.pc = C.std.userMainAddr + 0xec#64) (hrun0 : s0.status = .Running)
    (hx8_0 : s0.readReg64 .x8 = BitVec.ofNat 64 coreLen)
    (hx9_0 : s0.readReg64 .x9 = vecPtr)
    (hx10_0 : s0.readReg64 .x10 = vecPtr)
    (hx11_0 : s0.readReg64 .x11 = 0#64)
    (hx22_0 : s0.readReg64 .x22 = BitVec.ofNat 64 coreLen)
    (hcpu0 : ScanCpuPreserved s_ref s0) :
    SepWP P target_pc s0 ((vecPtr ↦ₛ stdinBytes) ∗ F_scan) post := by
  suffices hgo : ∀ (rem off : Nat) (s : State),
      rem = coreLen - off → off ≤ coreLen →
      (∀ s', (splitOnByte 0x0a#8 (core.drop off)).any (·.length > MaxLineLen) = true →
        s'.pc = C.std.userMainAddr + 0x324#64 → s'.status = .Running →
        ScanCpuPreserved s_ref s' →
        SepWP P target_pc s' ((vecPtr ↦ₛ stdinBytes) ∗ F_scan) post) →
      (∀ s', (splitOnByte 0x0a#8 (core.drop off)).any (·.length > MaxLineLen) = false →
        s'.pc = C.std.userMainAddr + 0x13c#64 → s'.status = .Running →
        s'.readReg64 .x9 = vecPtr → s'.readReg64 .x22 = BitVec.ofNat 64 coreLen →
        ScanCpuPreserved s_ref s' →
        SepWP P target_pc s' ((vecPtr ↦ₛ stdinBytes) ∗ F_scan) post) →
      s.pc = C.std.userMainAddr + 0xec#64 → s.status = .Running →
      s.readReg64 .x8 = BitVec.ofNat 64 (coreLen - off) →
      s.readReg64 .x9 = vecPtr →
      s.readReg64 .x10 = vecPtr + BitVec.ofNat 64 off →
      s.readReg64 .x11 = 0#64 →
      s.readReg64 .x22 = BitVec.ofNat 64 coreLen →
      ScanCpuPreserved s_ref s →
      SepWP P target_pc s ((vecPtr ↦ₛ stdinBytes) ∗ F_scan) post by
    exact hgo coreLen 0 s0 rfl (Nat.zero_le _) (by simpa using hlong) (by simpa using hdone)
      hpc0 hrun0 (by simpa using hx8_0) hx9_0 (by simpa using hx10_0) hx11_0 hx22_0 hcpu0
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
  intro off s hrem hoff hlong_off hdone_off hpc hrun hx8 hx9 hx10 hx11 hx22 hcpu
  have hL_bound : stdinBytes.length ≤ 10737418240 := hL
  have hcore_len : core.length = coreLen := by subst hcore; exact List.length_take_of_le hcore_le
  simp only [arm64_norm] at hx8 hx9 hx10 hx11 hx22
  unpack_hb_subchunks hbRustMainReadScanChunks hc_rm [8]
  wp_step; (try norm_jmp)
  conv => arg 3; simp (config := { decide := true }) only [wp_norm, arm64_norm, hx11, ↓reduceIte]
  iterate 2 (wp_step; (try norm_jmp))
  by_cases hoff_lt : off < coreLen
  · have h8_nz : (BitVec.ofNat 64 (coreLen - off) == 0#64) = false :=
      beq_eq_false_iff_ne.mpr fun heq => by
        have := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : coreLen - off < 18446744073709551616)] at this; omega
    refine hbMain_scanInner_wp hc_rm hcore hcore_le hL hlong_off hdone_off
      (fun s' k' hk' hk'_le heq' hprev' hpc' hrun' hx8' hx9' hx10' hx11' hx22' hcpu' => ?_)
      (coreLen - off) 0 _ rfl hoff (by omega) (fun _ hj => absurd hj (Nat.not_lt_zero _))
      (by simp only [wp_norm, arm64_norm, h8_nz, Bool.false_eq_true, ↓reduceIte]; try bv_lin)
      (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hx8])
      (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx10])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx22])
      (by simp (config := { decide := true }) only [ScanCpuPreserved.writeGpr, ScanCpuPreserved.setPC]; exact hcpu)
    have hany_eq : (splitOnByte 0x0a#8 (core.drop off)).any (·.length > MaxLineLen) =
        (splitOnByte 0x0a#8 (core.drop (off + (k' + 1)))).any (·.length > MaxLineLen) := by
      have hsplit := splitOnByte_of_first_eq (bs := core.drop off) (sep := 0x0a#8) (k := k')
        (by rw [List.length_drop, hcore_len]; omega) heq' hprev'
      have htk_le : ¬ (((core.drop off).take k').length > MaxLineLen) := by
        rw [List.length_take_of_le (by rw [List.length_drop, hcore_len]; omega)]; omega
      have hdd : (core.drop off).drop (k' + 1) = core.drop (off + (k' + 1)) := by
        rw [List.drop_drop, Nat.add_comm]
      rw [hsplit, List.any_cons, hdd, decide_eq_false htk_le, Bool.false_or]
    exact ih (coreLen - (off + (k' + 1))) (by omega) (off + (k' + 1)) s' rfl (by omega)
      (fun s'' h => hlong_off s'' (hany_eq.trans h)) (fun s'' h => hdone_off s'' (hany_eq.trans h))
      hpc' hrun' hx8' hx9' hx10' hx11' hx22' hcpu'
  · have hoff_eq : off = coreLen := by omega
    have hx8_z : s.readReg64 (.gpr 8#5) = 0#64 := by rw [hx8, hoff_eq, Nat.sub_self]
    conv => arg 3; simp (config := { decide := true }) only [wp_norm, arm64_norm, hx8_z, ↓reduceIte]
    iterate 4 (wp_step; (try norm_jmp))
    have hany : (splitOnByte 0x0a#8 (core.drop off)).any (·.length > MaxLineLen) = false := by
      rw [hoff_eq, List.drop_of_length_le (by omega)]; decide
    exact hdone_off _ hany wp_a (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx22])
      (by simp (config := { decide := true }) only [ScanCpuPreserved.writeGpr, ScanCpuPreserved.setPC, ScanCpuPreserved.setPState]; exact hcpu)

private theorem sepWP_transport_scan {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (M : HbMallocngIface P C.mallocng lim) (γ : GhostName)
    {target_pc : BitVec 64} {lc blk : Nat} {e0 : BitVec 32} {s s' : State}
    {A B C_prop : SepProp} {post : State → SepProp → Prop}
    (hcpu : ScanCpuPreserved s s')
    (hnext : SepWP P target_pc s'
      (A ∗ M.Heap γ lc blk s' ∗ B ∗ HbThreadIdInv C s'.tpidrEl0 ∗
        C_prop ∗ (muslErrnoAddr s' ↦₃₂ e0)) post) :
    SepWP P target_pc s'
      (A ∗ M.Heap γ lc blk s ∗ B ∗ HbThreadIdInv C s.tpidrEl0 ∗
        C_prop ∗ (muslErrnoAddr s ↦₃₂ e0)) post := by
  have herr : muslErrnoAddr s = muslErrnoAddr s' := by simp [muslErrnoAddr, hcpu.tpidrEl0_eq]
  rw [herr, ← hcpu.tpidrEl0_eq]
  exact SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (hcpu.toNonVm.heap_transport M.toMallocngCoreIface))) hnext

/-- Line-length pre-scan and early-return dispatch from `u + 0xb4`: handles empty input (exit `0`),
lines exceeding `MaxLineLen` (stderr message and exit `1`), and valid non-empty inputs (entering
the command loop at `u + 0x13c`). -/
theorem hbMain_scanLines_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hV : C.Valid) (hc : HbUserMainCode P C) (hcShims : HbShimsCode P C)
    (hc_sys : HbSyscallsAndStderrCode P C)
    (hatom : StdOutlineAtomics P C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
      C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr)
    (M : HbMallocngIface P C.mallocng lim) (γ : GhostName)
    {sp_m vecPtr : BitVec 64} {cap lcRest blkRest : Nat}
    {stdinBytes : List (BitVec 8)} {haveLse : BitVec 8} {e0 : BitVec 32}
    {s_main s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    (hsp_m : sp_m = s_main.sp - 0xe0#64) (hsp_main_al : s_main.spAligned = true)
    (hL : stdinBytes.length ≤ HashbrownCliMaxStdin)
    (hpc : s.pc = C.std.userMainAddr + 0xb4#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_m)
    (hx28 : s.readReg64 .x28 = s_main.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s_main)
    (hpre : Pre ⊢
      HbByteVec M.toMallocngCoreIface γ (sp_m + 0x08#64) cap vecPtr stdinBytes ∗
      memRegion sp_m 8 ∗ HbMainSavedRegs sp_m s_main ∗ memRegion (sp_m + 0x98#64) 8 ∗
      stackAt (sp_m + 0x80#64) 96 ∗ stackAt sp_m (261984 - 224) ∗
      M.Heap γ (lcRest + hbByteVecCost cap) (blkRest + hbByteVecBlocks cap) s ∗
      (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗
      HbThreadIdInv C s.tpidrEl0 ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
      (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (muslErrnoAddr s ↦₃₂ e0) ∗ F)
    (hret : ∀ (s_ret : State) (e_ret : BitVec 32) (Pf : SepProp),
      s_ret.sp = s_main.sp → CalleeSavedPreserved s_main s_ret →
      s_ret.fs = s.fs → s_ret.tpidrEl0 = s.tpidrEl0 →
      s_ret.sigActions = s.sigActions → s.mem.KeepsFrozen s_ret.mem →
      (s.trace = [] → HashbrownCliPost stdinBytes
        (ProcessOutcome.ofState (((s_ret.readReg32 .x0).truncate 8).zeroExtend 64) s_ret)) →
      (Pf ⊢ M.Heap γ lcRest blkRest s_ret ∗ (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗
        (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗ HbThreadIdInv C s_ret.tpidrEl0 ∗
        (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
        (muslErrnoAddr s_ret ↦₃₂ e_ret) ∗ stackAt s_ret.sp 261984 ∗ F) → post s_ret Pf)
    (hcmd : ∀ (s_cmd : State) (coreLen : Nat),
      stdinBytes ≠ [] → (splitLines stdinBytes).any (·.length > MaxLineLen) = false →
      coreLen ≤ stdinBytes.length →
      splitLines stdinBytes = splitOnByte 0x0a#8 (stdinBytes.take coreLen) →
      s_cmd.pc = C.std.userMainAddr + 0x13c#64 → s_cmd.status = .Running →
      s_cmd.sp = sp_m → s_cmd.spAligned = true →
      s_cmd.readReg64 .x9 = vecPtr → s_cmd.readReg64 .x22 = BitVec.ofNat 64 coreLen →
      s_cmd.readReg64 .x28 = s_main.readReg64 .x28 → s_cmd.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s_cmd = calleeSavedVRegs s_main →
      HbNonVmPreserved s s_cmd → s_cmd.fs = s.fs → s_cmd.trace = s.trace →
      SepWP P (s_main.readReg64 .lr) s_cmd
        (HbByteVec M.toMallocngCoreIface γ (sp_m + 0x08#64) cap vecPtr stdinBytes ∗
          memRegion sp_m 8 ∗ HbMainSavedRegs sp_m s_main ∗ memRegion (sp_m + 0x98#64) 8 ∗
          stackAt (sp_m + 0x80#64) 96 ∗ stackAt sp_m (261984 - 224) ∗
          M.Heap γ (lcRest + hbByteVecCost cap) (blkRest + hbByteVecBlocks cap) s_cmd ∗
          (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗
          HbThreadIdInv C s_cmd.tpidrEl0 ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
          (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (muslErrnoAddr s_cmd ↦₃₂ e0) ∗ F) post) :
    SepWP P (s_main.readReg64 .lr) s Pre post := by
  cases hsp.symm
  have hsp_al : s.spAligned = true := by
    simp only [State.spAligned, hsp_m]; exact s_main.spAligned_sub 0xe0#64 hsp_main_al
  have hc_rm := hc.rustMain
  have hc_scan : P.hasCode (C.std.userMainAddr + 0xb4#64) hbMainScanWords :=
    codeChunks_getElem? hc_rm (i := 8) rfl
  apply SepWP.weaken_pre hpre
  rcases stdinBytes with _ | ⟨b0, bsRest⟩
  · conv => arg 4; dsimp only [HbByteVec]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
    unpack_hb_subchunks hbRustMainReadScanChunks hc_rm [8]
    iterate 4 (wp_step; (try norm_jmp))
    apply SepWP.weaken_pre
      (P' := (HbByteVec M.toMallocngCoreIface γ (s.sp + 0x08#64) cap vecPtr [] ∗
        memRegion s.sp 8 ∗ HbMainSavedRegs s.sp s_main ∗ memRegion (s.sp + 0x98#64) 8 ∗
        stackAt (s.sp + 0x80#64) 96 ∗ stackAt s.sp (261984 - 224) ∗ F) ∗
        M.Heap γ (lcRest + hbByteVecCost cap) (blkRest + hbByteVecBlocks cap) s ∗
        ((C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes)) ∗
        HbThreadIdInv C s.tpidrEl0 ∗
        ((C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse)) ∗
        (muslErrnoAddr s ↦₃₂ e0))
      (by dsimp only [HbByteVec]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_entail)
    refine sepWP_transport_scan M γ
      (by simp (config := { decide := true }) only [ScanCpuPreserved.writeGpr, ScanCpuPreserved.setPC]; exact ScanCpuPreserved.refl s) ?_
    refine hbMain_epilogue_wp hc hcShims M.toMallocngCoreIface γ hsvc hext hsp_m hsp_main_al
      wp_a (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm])
      (by simpa [Reg.x28, wp_norm, arm64_norm] using hx28)
      (by simp [wp_norm, arm64_norm, hvregs]) (by sep_frame)
      (fun s_ret e_ret Pf hsp_r hx0_r hcs_r hmsp_r hPf => ?_)
    have hx0_val : ((s_ret.readReg32 .x0).truncate 8).zeroExtend 64 = 0#64 := by
      rw [hx0_r]; simp [wp_norm, arm64_norm]
    have htp_ret : s_ret.tpidrEl0 = s.tpidrEl0 := by simpa [wp_norm, arm64_norm] using hmsp_r.2.2.2.1
    have htr_ret : s_ret.trace = s.trace := by simpa [wp_norm, arm64_norm] using hmsp_r.2.1
    refine hret s_ret e_ret Pf hsp_r hcs_r (by simpa [wp_norm, arm64_norm] using hmsp_r.1) htp_ret
      (by simpa [wp_norm, arm64_norm] using hmsp_r.2.2.1)
      (by simpa [wp_norm, arm64_norm] using hmsp_r.2.2.2.2) (fun hs_tr => ?_)
      (Entails.trans hPf (by rw [← hmsp_r.2.2.2.1]; sep_entail))
    rw [hx0_val]; exact hashbrownCliPost_nil (htr_ret.trans hs_tr)
  · obtain ⟨stdinNe, hne_def⟩ : ∃ stdinNe, b0 :: bsRest = stdinNe := ⟨_, rfl⟩
    rw [hne_def] at hL hret hcmd ⊢
    have hpos : 0 < stdinNe.length := by rw [← hne_def]; simp
    have hne : stdinNe ≠ [] := List.ne_nil_of_length_pos hpos
    have hL_bound : stdinNe.length ≤ 10737418240 := hL
    rcases Nat.eq_zero_or_pos cap with rfl | hcap_pos
    · conv => arg 4; simp only [HbByteVec, HbByteVecBuf, ↓reduceIte, sepConj_assoc, sepConj_pull_pure]
      exact SepWP.pure_elim fun ⟨h_emp, _⟩ => absurd h_emp hne
    · have hcap_ne : cap ≠ 0 := by omega
      conv => arg 4; simp only [HbByteVec, HbByteVecBuf, hcap_ne, ↓reduceIte,
        BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, sepConj_pull_pure]
      refine SepWP.pure_elim fun hpure_vec => ?_
      have hlen_beq : (BitVec.ofNat 64 stdinNe.length == 0#64) = false :=
        beq_eq_false_iff_ne.mpr fun heq => by
          have := congrArg BitVec.toNat heq
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : stdinNe.length < 18446744073709551616)] at this; omega
      have hsub1 : BitVec.ofNat 64 stdinNe.length - 1#64 = BitVec.ofNat 64 (stdinNe.length - 1) := by
        have hsum : BitVec.ofNat 64 (stdinNe.length - 1) + 1#64 = BitVec.ofNat 64 stdinNe.length := by
          rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]; congr 1; omega
        rw [← hsum]; bv_lin
      unpack_hb_subchunks hbRustMainReadScanChunks hc_rm [8]
      iterate 2 (wp_step; (try norm_jmp))
      conv => arg 3; simp only [wp_norm, arm64_norm, hlen_beq, Bool.false_eq_true, ↓reduceIte]
      iterate 3 (wp_step; (try norm_jmp))
      conv => arg 3; simp only [wp_norm, arm64_norm, hsub1]
      let F_scan : SepProp :=
        ((s.sp + 0x08#64) ↦₆₄ BitVec.ofNat 64 cap) ∗ ((s.sp + 0x10#64) ↦₆₄ vecPtr) ∗
        ((s.sp + 0x18#64) ↦₆₄ BitVec.ofNat 64 stdinNe.length) ∗ M.Block γ vecPtr cap ∗
        memRegion (vecPtr + BitVec.ofNat 64 stdinNe.length) (cap - stdinNe.length) ∗
        memRegion s.sp 8 ∗ HbMainSavedRegs s.sp s_main ∗ memRegion (s.sp + 0x98#64) 8 ∗
        stackAt (s.sp + 0x80#64) 96 ∗ stackAt s.sp (261984 - 224) ∗
        M.Heap γ (lcRest + hbByteVecCost cap) (blkRest + hbByteVecBlocks cap) s ∗
        (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗
        HbThreadIdInv C s.tpidrEl0 ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
        (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (muslErrnoAddr s ↦₃₂ e0) ∗ F
      have hrepack_vec : (vecPtr ↦ₛ stdinNe) ∗ F_scan ⊢
          HbByteVec M.toMallocngCoreIface γ (s.sp + 0x08#64) cap vecPtr stdinNe ∗
          memRegion s.sp 8 ∗ HbMainSavedRegs s.sp s_main ∗ memRegion (s.sp + 0x98#64) 8 ∗
          stackAt (s.sp + 0x80#64) 96 ∗ stackAt s.sp (261984 - 224) ∗
          M.Heap γ (lcRest + hbByteVecCost cap) (blkRest + hbByteVecBlocks cap) s ∗
          (C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes) ∗
          HbThreadIdInv C s.tpidrEl0 ∗ (C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗
          (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ (muslErrnoAddr s ↦₃₂ e0) ∗ F := by
        dsimp only [F_scan]; simp only [HbByteVec, HbByteVecBuf, hcap_ne, ↓reduceIte,
          BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, sepConj_pull_pure]
        exact Entails.pure_right hpure_vec (by sep_entail)
      apply SepWP.weaken_pre (P' := (vecPtr ↦ₛ stdinNe) ∗ F_scan) (by dsimp only [F_scan]; sep_entail)
      refine step_ldrb_words_main (addr := C.std.userMainAddr + 0xb4#64) (words := hbMainScanWords)
        (wIdx := 5) (w := 0x386a692c#32)
        (pc := C.std.userMainAddr + 0xc8#64) (pc' := C.std.userMainAddr + 0xcc#64)
        (vecPtr := vecPtr) (rt := .gpr 12#5) (rn := .gpr 9#5) (rm := .gpr 10#5)
        hc_scan (by bv_lin) rfl rfl (by decide) (show stdinNe.length - 1 < stdinNe.length by omega)
        wp_a (by simp [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm]) (by bv_lin) ?_
      iterate 5 (wp_step; (try norm_jmp))
      obtain ⟨coreLen, hcoreLen_def⟩ : ∃ coreLen,
          (if stdinNe[stdinNe.length - 1]'(by omega) = 0x0a#8
            then stdinNe.length - 1 else stdinNe.length) = coreLen := ⟨_, rfl⟩
      have hcore_le : coreLen ≤ stdinNe.length := by rw [← hcoreLen_def]; split <;> omega
      have hsplit_eq : splitLines stdinNe = splitOnByte 0x0a#8 (stdinNe.take coreLen) := by
        rw [← hcoreLen_def]; exact splitLines_of_pos hpos
      have hb_nl : ((stdinNe[stdinNe.length - 1]'(by omega)).zeroExtend 32 == 10#32) =
          ((stdinNe[stdinNe.length - 1]'(by omega)) == 0x0a#8) := byte_ze32_beq_0a _
      refine hbMain_scanOuter_wp hc_rm rfl hcore_le hL
        (fun s' hany_c hpc' hrun' hcpu' => SepWP.weaken_pre hrepack_vec
          (hbMain_lineTooLong_wp hV hc hcShims hc_sys hatom M γ hsvc hext hsp_m hsp_main_al
            (hsplit_eq.symm ▸ hany_c) hpc' hrun' hcpu' rfl hx28 hvregs hret))
        (fun s_cmd hany_c hpc' hrun' hx9' hx22' hcpu' => ?_)
        wp_a (by simp [wp_norm, arm64_norm, hrun])
        (by simp only [wp_norm, arm64_norm, hb_nl]; rw [← hcoreLen_def]
            by_cases heq_nl : (stdinNe[stdinNe.length - 1]'(by omega)) = 0x0a#8 <;> simp [heq_nl])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hb_nl]; rw [← hcoreLen_def]
            by_cases heq_nl : (stdinNe[stdinNe.length - 1]'(by omega)) = 0x0a#8 <;> simp [heq_nl])
        (by simp (config := { decide := true }) only [ScanCpuPreserved.writeGpr, ScanCpuPreserved.setPC, ScanCpuPreserved.setPState]
            exact ScanCpuPreserved.refl s)
      apply SepWP.weaken_pre hrepack_vec
      apply SepWP.weaken_pre
        (P' := (HbByteVec M.toMallocngCoreIface γ (s.sp + 0x08#64) cap vecPtr stdinNe ∗
          memRegion s.sp 8 ∗ HbMainSavedRegs s.sp s_main ∗ memRegion (s.sp + 0x98#64) 8 ∗
          stackAt (s.sp + 0x80#64) 96 ∗ stackAt s.sp (261984 - 224) ∗ F) ∗
          M.Heap γ (lcRest + hbByteVecCost cap) (blkRest + hbByteVecBlocks cap) s ∗
          ((C.stderrGlobalAddr ↦ₛ List.replicate 24 0#8) ∗ (C.errLineTooLongAddr ↦ᵣ errLineTooLongBytes)) ∗
          HbThreadIdInv C s.tpidrEl0 ∗
          ((C.osFunctionsGotAddr ↦₆₄ᵣ C.osFunctionsAddr) ∗ (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse)) ∗
          (muslErrnoAddr s ↦₃₂ e0))
        (by sep_entail)
      refine sepWP_transport_scan M γ hcpu' ?_
      exact SepWP.weaken_pre (by sep_entail)
        (hcmd s_cmd coreLen hne (hsplit_eq.symm ▸ hany_c) hcore_le hsplit_eq hpc' hrun'
          hcpu'.sp_eq (by simpa [State.spAligned, hcpu'.sp_eq] using hsp_al)
          hx9' hx22' (hcpu'.x28_eq.trans hx28) hcpu'.x29_eq
          (hcpu'.vregs_eq.trans hvregs) hcpu'.toNonVm hcpu'.fs_eq hcpu'.trace_eq)

namespace MainReadScanInternal
end MainReadScanInternal

end CaseStudies.Hashbrown.Proofs.StdCli
