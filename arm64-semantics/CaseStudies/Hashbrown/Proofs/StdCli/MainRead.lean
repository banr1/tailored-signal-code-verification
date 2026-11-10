/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.MainEpilogue
public meta import ProofLib.LiteralFetchLint
import ProofLib.BV

/-!
# Layout-Generic `OnceLock<Stdin>` Initialization and `Read::read_to_end`

Placement-generic `SepWP` proofs for `std::io::stdio::stdin` and `std::io::default_read_to_end`
parameterized over `C : HbCliLayout`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open CaseStudies.Hashbrown CaseStudies.Hashbrown.Proofs

local macro "unpack_hb_main_code " chunks:ident h:term : tactic => `(tactic| (
  have _hc := chunksToStepFacts $h
  simp only [$chunks:ident, chunksStepFacts, chunkStepAcc, fetchAtAcc,
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

local macro "unpack_hb_subchunks " chunks:ident h:term:arg idxs:term:arg : tactic => `(tactic| (
  have _hc := chunksToStepFacts (codeChunks_select $h $idxs)
  simp only [$chunks:ident, List.filterMap_cons, List.filterMap_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
    chunksStepFacts, chunkStepAcc, fetchAtAcc,
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))

local macro "norm_jmp" : tactic => `(tactic| (
  (try (conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel]))
  (try (conv in State.setPC _ _ => arg 2; rw [BitVec.add_assoc]; simp only [BitVec.reduceAdd]))))

local macro "unpack_cells " k:num : tactic => `(tactic| (
  conv => arg 4; (try simp only [Nat.reduceMul])
  cells_unfold
  conv => arg 4; (try simp only [sepExists_sepConj_left, sepExists_sepConj_right])
  iterate $k (apply SepWP.exists_left; intro _)))

local macro "repack_cells" : tactic => `(tactic| (
  (try simp only [Nat.reduceMul]); cells_unfold
  (try simp only [BitVec.ofNat_eq_ofNat, sepExists_sepConj_left, sepExists_sepConj_right]); sep_entail))

local macro "unpack_cs " h:ident : tactic =>
  `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := $h)

local macro "close_cs" : tactic =>
  `(tactic| simp [CalleeSavedPreserved.iff_regs, Reg.fp, wp_norm, arm64_norm, *])

local macro "wp_a" : term => `(by simp [wp_norm, arm64_norm, bv_lin_norm, *] <;> try bv_lin)

/-! ## Stack Budgets, `ldar` Stepper, and `HbStdinLockedRest` -/

abbrev hbStdioStdinStackBytes    : Nat := 16 + hbStdinInitStackBytes
abbrev hbDefaultReadStackBytes   : Nat := 144 + hbSmallProbeStackBytes
abbrev hbBufReaderReadStackBytes : Nat := 128 + hbDefaultReadStackBytes
abbrev hbStdinReadStackBytes     : Nat := 64 + hbBufReaderReadStackBytes

theorem step_ldar32_words_main {prog : Program} {target_pc : BitVec 64}
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
    simp [Program.evalInst, execInstWithSvc, Memory.readSized, State.writeReg, State.advancePC,
      State.setPC, hsp, haddr, halign, hread, hcan, MemWidth.bytes, hpc4]

theorem stdinGlobal_isAligned32 {C : HbCliLayout} (hV : C.Valid) :
    MemWidth.isAligned .W32 C.stdinGlobalAddr = true := by
  have hal := hV.stdinGlobal_align
  simp only [MemWidth.isAligned]
  have h0 : C.stdinGlobalAddr &&& 3#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    change C.stdinGlobalAddr.toNat &&& 3 = 0
    rw [Nat.and_two_pow_sub_one_eq_mod _ 2]; omega
  simp [h0]

theorem take_append_drop_take {α : Type} (xs : List α) {pos : Nat} (cnt : Nat)
    (hpos : pos ≤ xs.length) :
    xs.take pos ++ (xs.drop pos).take cnt = xs.take (pos + ((xs.drop pos).take cnt).length) := by
  have hlen : ((xs.drop pos).take cnt).length = min cnt (xs.length - pos) := by
    rw [List.length_take, List.length_drop]
  by_cases hle : cnt ≤ xs.length - pos
  · rw [hlen, Nat.min_eq_left hle, List.take_add]
  · have hdt : (xs.drop pos).take cnt = xs.drop pos :=
      List.take_of_length_le (by rw [List.length_drop]; omega)
    rw [hdt, List.length_drop, show pos + (xs.length - pos) = xs.length by omega,
        List.take_append_drop, List.take_length]

def HbStdinLockedRest {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P addrs lim) (γ : GhostName) (bufPtr : BitVec 64) : SepProp :=
  let g := C.stdinGlobalAddr
  memRegion (g + 0x04#64) 4 ∗ ((g + 0x08#64) ↦₆₄ bufPtr) ∗ ((g + 0x10#64) ↦₆₄ 8192#64) ∗
  ((g + 0x18#64) ↦₆₄ 0#64) ∗ ((g + 0x20#64) ↦₆₄ 0#64) ∗ ((g + 0x28#64) ↦₈ 0#8) ∗
  memRegion (g + 0x29#64) 7 ∗ ((g + 0x30#64) ↦₃₂ 0#32) ∗ M.Block γ bufPtr 8192 ∗ memRegion bufPtr 8192

theorem HbStdinLockedRest_repack {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (C : HbCliLayout) (M : MallocngCoreIface P addrs lim) (γ : GhostName) {bufPtr : BitVec 64}
    (hbuf : bufPtr ≠ 0#64 ∧ 16 ∣ bufPtr.toNat ∧ bufPtr.toNat + 8192 < 2 ^ 64) :
    (C.stdinGlobalAddr ↦₃₂ 0#32) ∗ HbStdinLockedRest C M γ bufPtr ⊢ HbStdinInv C M γ true := by
  dsimp only [HbStdinInv, HbStdinLockedRest, ↓reduceIte]
  exact Entails.sepExists_right bufPtr (Entails.pure_right hbuf (by sep_entail))

private theorem seq_nonVm_kf {prog : Program} {mid target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hext : ∀ pc, prog.externAt? pc = none) (hsvc : prog.svc = Syscall.standard)
    (h : SepWP (prog.withSvc nonVmSvc) mid s P
      (fun sm Pm => VmFieldsPreserved s sm → s.mem.KeepsFrozen sm.mem → SepWP prog target sm Pm post)) :
    SepWP prog target s P post :=
  SepWP.seq_nonVm hext hsvc (SepWP.with_keepsFrozen (SepWP.mono h fun _ _ _ _ hp hkf hvm => hp hvm hkf))

/-! ## `std::io::stdio::stdin` -/

/-- `SepWP` call contract for `std::io::stdio::stdin` (`C.stdioStdinAddr`):
    fast-paths when `init = true` (`[g + 0x30] = 0#32`) and calls `OnceLock<Stdin>::initialize`
    when `init = false` (`[g + 0x30] = 3#32`), returning `x0 = C.stdinGlobalAddr` and
    `HbStdinInv C M γ true`. -/
theorem stdioStdin_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    {target_pc ret_pc : BitVec 64}
    (hV : C.Valid) (hc : HbUserMainCode P C)
    (hc_stdin : HbStdinAndVecCode P C) (honce : HbOnceCallCode P C)
    (hatom : StdOutlineAtomics P C.std.haveLseAtomicsAddr C.std.cas8RelaxAddr
      C.std.cas4AcqAddr C.std.cas8AcqAddr C.std.swp4RelAddr)
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    {init : Bool} {lc blk : Nat} {haveLse : BitVec 8} {e0 : BitVec 32}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    (hlim : init = false →
      8192 ≤ lim.maxReq ∧
      lc + mallocngBlockCost 8192 ≤ lim.maxPeakCost ∧
      blk + 1 ≤ lim.maxPeakBlocks)
    (hpc : s.pc = C.stdioStdinAddr) (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : Pre ⊢
      HbStdinInv C M γ init ∗
      (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
      StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
      M.Heap γ lc blk s ∗
      (muslErrnoAddr s ↦₃₂ e0) ∗
      stackAt s.sp hbStdioStdinStackBytes ∗ F)
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      let lc' := lc + if init then 0 else mallocngBlockCost 8192
      let blk' := blk + if init then 0 else 1
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      sf.readReg64 .x0 = C.stdinGlobalAddr →
      CalleeSavedPreserved s sf → MallocngStatePreserved s sf →
      SepWP P target_pc sf
        (HbStdinInv C M γ true ∗
          (C.std.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗
          StdVtableRo C.stdinInitVtableAddr C.stdinInitShimAddr C.stdinInitClosureAddr ∗
          M.Heap γ lc' blk' sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗
          stackAt s.sp hbStdioStdinStackBytes ∗ F) post) :
    SepWP P target_pc s Pre post := by
  cases hlr.symm
  apply SepWP.weaken_pre hpre
  cases init
  ·
    conv =>
      arg 4
      simp only [HbStdinInv, Bool.false_eq_true, ↓reduceIte]
      rw [show hbStdioStdinStackBytes = hbStdinInitStackBytes + 8 * 2 from rfl,
          stackAt_split_cells s.sp hbStdinInitStackBytes 2 (by decide)]
    unpack_cells 2
    conv => arg 4; rw [show s.sp - BitVec.ofNat 64 (8 * 2) = s.sp - 16#64 from rfl]
    refine seq_nonVm_kf (mid := C.stdinOnceLockInitAddr) hext hsvc ?_
    have hc_nv1 := (hc.withSvc nonVmSvc).stdioStdin
    unpack_hb_main_code hbStdioStdinChunks hc_nv1
    wp_steps
    refine step_ldar32_words_main (C.stdioStdinAddr + 0x08#64)
      [0x88dffd08#32, 0x35000088#32, 0xd503201f#32] 0
      (C.stdioStdinAddr + 0x0c#64) hV.stdinOnceAligned (hnext := ?_)
    wp_steps; (try norm_jmp); wp_steps; (try norm_jmp)
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) (fun hvm1 hkf1 => ?_)
    have hmsp01 : MallocngStatePreserved s _ :=
      ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
       by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], hkf1⟩
    refine hbStdinOnceLockInit_wp hV hc_stdin honce hatom M γ hvm1 hV.stdinGlobal_nz
      (init := false) (lc := lc) (blk := blk) (sp_call := s.sp - 16#64)
      (ret_pc := C.stdioStdinAddr + 0x28#64)
      (fun _ => hlim trivial)
      (by dsimp only [HbStdinInv]; simp only [Bool.false_eq_true, ↓reduceIte]; sep_frame)
      (fun s1 e1 hpc1 hrun1 hsp1 hcs1 hmsp1 => ?_) hsvc hext
      (hsp_call := by simp [wp_norm, arm64_norm])
      (hsp_align := by
        simp only [State.spAligned, wp_norm, arm64_norm]
        simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 16#64 hsp_al)
    conv => arg 4; simp (config := { zetaDelta := false }) only [Bool.false_eq_true, ↓reduceIte]
    have hsp1_eq : s1.sp = s.sp - 16#64 := by rw [hsp1]; simp [wp_norm, arm64_norm]
    refine seq_nonVm_kf (mid := s.readReg64 Reg.lr) hext hsvc ?_
    have hc_nv2 := (hc.withSvc nonVmSvc).stdioStdin
    unpack_hb_main_code hbStdioStdinChunks hc_nv2
    wp_steps; (try norm_jmp); wp_steps; (try norm_jmp)
    refine SepWP.done (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun1]) (fun hvm2 hkf2 => ?_)
    apply sepWP_mono_atom (vmHeapTransport M hvm2)
    have hmsp2 : MallocngStatePreserved s1 _ :=
      ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
       by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], hkf2⟩
    refine SepWP.weaken_pre_frame (fun R hm => ?_)
      (hnext _ e1
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun1])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm] <;> bv_lin)
        (by unpack_cs hcs1; close_cs)
        (MallocngStatePreserved.trans hmsp01 (MallocngStatePreserved.trans hmsp1 hmsp2)))
    simp only [Bool.false_eq_true, ↓reduceIte, muslErrnoAddr, wp_norm, arm64_norm] at hm ⊢
    rw [show hbStdioStdinStackBytes = hbStdinInitStackBytes + 8 * 2 from rfl,
        stackAt_split_cells s.sp hbStdinInitStackBytes 2 (by decide)]
    repack_cells
  ·
    conv =>
      arg 4
      simp only [HbStdinInv, ↓reduceIte, sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_elim fun bufPtr => ?_
    conv => arg 4; simp only [sepConj_assoc, sepConj_pull_pure]
    refine SepWP.pure_elim fun hbuf => ?_
    refine seq_nonVm_kf (mid := s.readReg64 Reg.lr) hext hsvc ?_
    have hc_nv := (hc.withSvc nonVmSvc).stdioStdin
    unpack_hb_main_code hbStdioStdinChunks hc_nv
    wp_steps
    refine step_ldar32_words_main (C.stdioStdinAddr + 0x08#64)
      [0x88dffd08#32, 0x35000088#32, 0xd503201f#32] 0
      (C.stdioStdinAddr + 0x0c#64) hV.stdinOnceAligned (hnext := ?_)
    wp_steps; (try norm_jmp); wp_steps; (try norm_jmp)
    refine SepWP.done (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun]) (fun hvm hkf => ?_)
    apply sepWP_mono_atom (vmHeapTransport M hvm)
    have hinv_re :
        (C.stdinGlobalAddr ↦₃₂ 0#32) ∗ memRegion (C.stdinGlobalAddr + 0x04#64) 4 ∗
        ((C.stdinGlobalAddr + 0x08#64) ↦₆₄ bufPtr) ∗ ((C.stdinGlobalAddr + 0x10#64) ↦₆₄ 8192#64) ∗
        ((C.stdinGlobalAddr + 0x18#64) ↦₆₄ 0#64) ∗ ((C.stdinGlobalAddr + 0x20#64) ↦₆₄ 0#64) ∗
        ((C.stdinGlobalAddr + 0x28#64) ↦₈ 0#8) ∗ memRegion (C.stdinGlobalAddr + 0x29#64) 7 ∗
        ((C.stdinGlobalAddr + 0x30#64) ↦₃₂ 0#32) ∗ M.Block γ bufPtr 8192 ∗ memRegion bufPtr 8192 ⊢
        HbStdinInv C M γ true := by
      dsimp only [HbStdinInv, ↓reduceIte]
      exact Entails.sepExists_right bufPtr (Entails.pure_right hbuf (by sep_entail))
    apply sepWP_mono_atom hinv_re
    have hmsp : MallocngStatePreserved s _ :=
      ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
       by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm], hkf⟩
    refine SepWP.weaken_pre ?_
      (hnext _ e0
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm] <;> bv_lin)
        (by close_cs)
        hmsp)
    simp only [↓reduceIte, Nat.add_zero, muslErrnoAddr, wp_norm, arm64_norm]
    sep_entail

/-! ## `std::io::default_read_to_end` -/

private def DefaultReadSavedRegs (sp_d : BitVec 64) (s0 : State) : SepProp :=
  ((sp_d + 0x30#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp_d + 0x38#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((sp_d + 0x40#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((sp_d + 0x48#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp_d + 0x50#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((sp_d + 0x58#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp_d + 0x60#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp_d + 0x68#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp_d + 0x70#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp_d + 0x78#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp_d + 0x80#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp_d + 0x88#64) ↦₆₄ s0.readReg64 .x19)

private def DefaultReadDonePost {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) (γ : GhostName)
    (vecSlotPtr : BitVec 64) (stdinBytes : List (BitVec 8))
    (lc blk : Nat) (s0 : State) (R_frame : SepProp) (sf : State) (Pf : SepProp) : Prop :=
  ∃ (cap : Nat) (vecPtr : BitVec 64) (e1 : BitVec 32),
    cap ≤ 2 * stdinBytes.length + 32 ∧
    HbStdinOpen [] sf.fs ∧ sf.sp = s0.sp ∧ sf.spAligned = true ∧
    sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = BitVec.ofNat 64 stdinBytes.length ∧
    CalleeSavedPreserved s0 sf ∧
    sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.sigActions = s0.sigActions ∧
    (Pf ⊢ HbByteVec M γ vecSlotPtr cap vecPtr stdinBytes ∗
      M.Heap γ (lc + hbByteVecCost cap) (blk + hbByteVecBlocks cap) sf ∗
      (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt s0.sp hbDefaultReadStackBytes ∗ R_frame)

private theorem defaultRead_epilogue_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hc : HbUserMainCode P C)
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    {sp_d vecSlotPtr vecPtr w0 w1 w2 w3 w4 w5 : BitVec 64} {cap lc blk : Nat}
    {stdinBytes : List (BitVec 8)} {e1 : BitVec 32}
    {s0 s : State} {R_frame : SepProp}
    (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (hsp_d : sp_d = s0.sp - 144#64) (hsp0_al : s0.spAligned = true)
    (hcap_le : cap ≤ 2 * stdinBytes.length + 32)
    (hpc : s.pc = C.defaultReadToEndAddr + 0x24c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_d) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = 0#64) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 stdinBytes.length)
    (hopen : HbStdinOpen [] s.fs)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) (htp : s.tpidrEl0 = s0.tpidrEl0) (hsig : s.sigActions = s0.sigActions) :
    SepWP P (s0.readReg64 Reg.lr) s
      (HbByteVec M γ vecSlotPtr cap vecPtr stdinBytes ∗
        (sp_d ↦₆₄ w0) ∗ ((sp_d + 0x08#64) ↦₆₄ w1) ∗ ((sp_d + 0x10#64) ↦₆₄ w2) ∗
        ((sp_d + 0x18#64) ↦₆₄ w3) ∗ ((sp_d + 0x20#64) ↦₆₄ w4) ∗ ((sp_d + 0x28#64) ↦₆₄ w5) ∗
        DefaultReadSavedRegs sp_d s0 ∗ stackAt sp_d hbSmallProbeStackBytes ∗
        M.Heap γ (lc + hbByteVecCost cap) (blk + hbByteVecBlocks cap) s ∗
        (muslErrnoAddr s ↦₃₂ e1) ∗ R_frame)
      (DefaultReadDonePost M γ vecSlotPtr stdinBytes lc blk s0 R_frame) := by
  cases hsp.symm
  conv => arg 4; dsimp only [DefaultReadSavedRegs]
  refine SepWP.seq_nonVm (mid := s0.readReg64 Reg.lr) hext hsvc ?_
  have hc_nv := (hc.withSvc nonVmSvc).defaultRead
  unpack_hb_subchunks hbDefaultReadToEndChunks hc_nv [14]
  wp_steps
  refine SepWP.done (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hrun]) (fun hvm => ?_)
  have hsp_ret : s.sp + 144#64 = s0.sp := by rw [hsp_d]; bv_lin
  refine SepWP.weaken_pre_frame
    (P' := HbByteVec M γ vecSlotPtr cap vecPtr stdinBytes ∗
      M.Heap γ (lc + hbByteVecCost cap) (blk + hbByteVecBlocks cap) s ∗
      (muslErrnoAddr s ↦₃₂ e1) ∗ stackAt s0.sp hbDefaultReadStackBytes ∗ R_frame)
    (fun R hm => ?_) ?_
  · simp only [hsp_d, wp_norm, arm64_norm] at hm ⊢
    rw [show hbDefaultReadStackBytes = hbSmallProbeStackBytes + 8 * 18 from rfl,
        stackAt_split_cells s0.sp hbSmallProbeStackBytes 18 (by decide)]
    repack_cells
  · apply sepWP_mono_atom (vmHeapTransport M hvm)
    refine SepWP.done (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun]) ⟨cap, vecPtr, e1, hcap_le,
      by simpa [wp_norm, arm64_norm] using hopen,
      by simp [wp_norm, arm64_norm],
      by simpa [State.spAligned, wp_norm, arm64_norm] using hsp0_al,
      by simp [wp_norm, arm64_norm, hx0],
      by simp [wp_norm, arm64_norm, hx1],
      by simp [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm, hvregs],
      by simp [wp_norm, arm64_norm, htr],
      by simp [wp_norm, arm64_norm, htp],
      by simp [wp_norm, arm64_norm, hsig], ?_⟩
    simp only [muslErrnoAddr, wp_norm, arm64_norm]
    sep_entail

private theorem defaultRead_readStep_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hc : HbUserMainCode P C) (hc_sys : HbSyscallsAndStderrCode P C)
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    {sp_d vecSlotPtr vecPtr w1 w2 w3 w4 w5 : BitVec 64} {pos cap lc blk : Nat}
    {stdinBytes : List (BitVec 8)} {e0 : BitVec 32}
    {s0 s : State} {R_frame : SepProp}
    (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (hsp_d : sp_d = s0.sp - 144#64) (hsp0_al : s0.spAligned = true)
    (hL : stdinBytes.length ≤ HashbrownCliMaxStdin)
    (hpos1 : 1 ≤ pos) (hpos_le : pos ≤ stdinBytes.length)
    (hpos_lt : pos < cap) (hcap8 : 8 ≤ cap) (hcap_le : cap ≤ 2 * stdinBytes.length + 32)
    (hpc : s.pc = C.defaultReadToEndAddr + 0x128#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_d) (hsp_al : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = vecSlotPtr) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 cap)
    (hx23 : s.readReg64 .x23 = vecPtr) (hx25 : 1 ≤ (s.readReg64 .x25).toNat)
    (hx26 : s.readReg64 .x26 = 0#64) (hx27 : s.readReg64 .x27 = 0#64)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 pos)
    (hopen : HbStdinOpen (stdinBytes.drop pos) s.fs)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) (htp : s.tpidrEl0 = s0.tpidrEl0) (hsig : s.sigActions = s0.sigActions)
    (hloop : ∀ (s' : State) (pos' : Nat),
      pos < pos' → pos' ≤ stdinBytes.length → pos' ≤ cap →
      s'.pc = C.defaultReadToEndAddr + 0x118#64 → s'.status = .Running →
      s'.sp = sp_d → s'.spAligned = true →
      s'.readReg64 .x19 = vecSlotPtr → s'.readReg64 .x22 = BitVec.ofNat 64 cap →
      1 ≤ (s'.readReg64 .x25).toNat → s'.readReg64 .x26 = 0#64 →
      s'.readReg64 .x27 = 0#64 → s'.readReg64 .x28 = BitVec.ofNat 64 pos' →
      HbStdinOpen (stdinBytes.drop pos') s'.fs →
      calleeSavedVRegs s' = calleeSavedVRegs s0 →
      s'.trace = s0.trace → s'.tpidrEl0 = s0.tpidrEl0 → s'.sigActions = s0.sigActions →
      SepWP P (s0.readReg64 Reg.lr) s'
        (HbByteVec M γ vecSlotPtr cap vecPtr (stdinBytes.take pos') ∗
          (sp_d ↦₆₄ 0#64) ∗ ((sp_d + 0x08#64) ↦₆₄ w1) ∗ ((sp_d + 0x10#64) ↦₆₄ w2) ∗
          ((sp_d + 0x18#64) ↦₆₄ w3) ∗ ((sp_d + 0x20#64) ↦₆₄ w4) ∗ ((sp_d + 0x28#64) ↦₆₄ w5) ∗
          DefaultReadSavedRegs sp_d s0 ∗ stackAt sp_d hbSmallProbeStackBytes ∗
          M.Heap γ (lc + hbByteVecCost cap) (blk + hbByteVecBlocks cap) s' ∗
          (muslErrnoAddr s' ↦₃₂ e0) ∗ R_frame)
        (DefaultReadDonePost M γ vecSlotPtr stdinBytes lc blk s0 R_frame)) :
    SepWP P (s0.readReg64 Reg.lr) s
      (HbByteVec M γ vecSlotPtr cap vecPtr (stdinBytes.take pos) ∗
        (sp_d ↦₆₄ 0#64) ∗ ((sp_d + 0x08#64) ↦₆₄ w1) ∗ ((sp_d + 0x10#64) ↦₆₄ w2) ∗
        ((sp_d + 0x18#64) ↦₆₄ w3) ∗ ((sp_d + 0x20#64) ↦₆₄ w4) ∗ ((sp_d + 0x28#64) ↦₆₄ w5) ∗
        DefaultReadSavedRegs sp_d s0 ∗ stackAt sp_d hbSmallProbeStackBytes ∗
        M.Heap γ (lc + hbByteVecCost cap) (blk + hbByteVecBlocks cap) s ∗
        (muslErrnoAddr s ↦₃₂ e0) ∗ R_frame)
      (DefaultReadDonePost M γ vecSlotPtr stdinBytes lc blk s0 R_frame) := by
  cases hsp.symm
  simp only [arm64_norm] at hx19 hx22 hx23 hx25 hx26 hx27 hx28
  have hL_bound : stdinBytes.length ≤ 10737418240 := hL
  have hcap_ne : cap ≠ 0 := by omega
  have htk_len : (stdinBytes.take pos).length = pos := List.length_take_of_le hpos_le
  obtain ⟨cnt, hcnt_def⟩ : ∃ cnt, min (s.readReg64 (.gpr 25#5)).toNat (cap - pos) = cnt := ⟨_, rfl⟩
  have hcnt_pos : 1 ≤ cnt := by rw [← hcnt_def]; omega
  have hcnt_le : cnt ≤ cap - pos := hcnt_def ▸ Nat.min_le_right _ _
  have hcnt_lt63 : cnt < 9223372036854775807 := by omega
  have hsub_eq : BitVec.ofNat 64 cap - BitVec.ofNat 64 pos = BitVec.ofNat 64 (cap - pos) := by
    rw [← (show BitVec.ofNat 64 (cap - pos) + BitVec.ofNat 64 pos = BitVec.ofNat 64 cap by
      rw [← BitVec.ofNat_add, Nat.sub_add_cancel (by omega)])]; bv_lin
  have hcsel1 : (if BitVec.ult (s.readReg64 (.gpr 25#5)) (BitVec.ofNat 64 (cap - pos)) = true
      then s.readReg64 (.gpr 25#5) else BitVec.ofNat 64 (cap - pos)) = BitVec.ofNat 64 cnt := by
    simp only [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : cap - pos < 18446744073709551616)]
    split
    · rw [show cnt = (s.readReg64 (.gpr 25#5)).toNat by rw [← hcnt_def]; omega,
          BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [show cnt = cap - pos by rw [← hcnt_def]; omega]
  have hcsel2 : (if BitVec.ult (BitVec.ofNat 64 cnt) 0x7fffffffffffffff#64 = true
      then BitVec.ofNat 64 cnt else 0x7fffffffffffffff#64) = BitVec.ofNat 64 cnt := by
    have hlt : BitVec.ult (BitVec.ofNat 64 cnt) 0x7fffffffffffffff#64 = true := by
      rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : cnt < 18446744073709551616)]
      simp only [BitVec.toNat_ofNat]; omega
    simp only [hlt, ↓reduceIte]
  conv => arg 4; simp only [HbByteVec, HbByteVecBuf, hcap_ne, ↓reduceIte, htk_len, sepConj_assoc, sepConj_pull_pure]
  refine SepWP.pure_elim fun ⟨hptr_nz, hptr_al, hptr_nw, _⟩ => ?_
  apply sepWP_mono_atom (M.block_userVa γ vecPtr cap)
  conv => arg 4; simp only [sepConj_assoc, sepConj_pull_pure]
  refine SepWP.pure_elim fun hptr_va => ?_
  conv => arg 4; rw [memRegion_split_le (vecPtr + BitVec.ofNat 64 pos) cnt (cap - pos) hcnt_le (by omega),
    stackAt_split_main s.sp 32 (hbSmallProbeStackBytes - 32)]
  refine SepWP.seq_nonVm (mid := C.readAddr) hext hsvc ?_
  have hc_nv1 := (hc.withSvc nonVmSvc).defaultRead
  unpack_hb_main_code hbDefaultReadToEndChunks hc_nv1
  wp_steps
  refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) (fun hvm1 => ?_)
  apply sepWP_mono_atom (vmHeapTransport M hvm1)
  have hcnt_tn : (BitVec.ofNat 64 cnt).toNat = cnt := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cnt < 18446744073709551616)]
  refine call_hbRead hc_sys (rem := stdinBytes.drop pos) (bufPtr := vecPtr + BitVec.ofNat 64 pos)
    (count := BitVec.ofNat 64 cnt) (ret_pc := C.defaultReadToEndAddr + 0x154#64) hsvc hext
    (by rw [hcnt_tn]; omega)
    (by
      rw [hcnt_tn, BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : pos < 18446744073709551616),
          Nat.mod_eq_of_lt (by omega : vecPtr.toNat + pos < 18446744073709551616)]
      omega)
    (by simpa [wp_norm, arm64_norm] using hopen)
    (by simp only [hcnt_tn, wp_norm, arm64_norm]; sep_frame)
    (fun s2 => ?_)
    (hsp_align := by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al)
    (hx1 := by simp only [wp_norm, arm64_norm])
    (hx2 := by simp only [wp_norm, arm64_norm])
  dsimp only
  intro hpc2 hrun2 hsp2 hcs2 hx0_2 hopen2 htr2 hnv2
  rw [hcnt_tn] at hx0_2 hopen2 ⊢
  obtain ⟨chunk, hchunk_def⟩ : ∃ chunk, (stdinBytes.drop pos).take (min cnt Arm64.MAX_RW_COUNT) = chunk := ⟨_, rfl⟩
  have ⟨hchunk_le_cnt, hchunk_le_rem, hchunk_pos_imp⟩ :
      chunk.length ≤ cnt ∧ chunk.length ≤ stdinBytes.length - pos ∧
      (pos < stdinBytes.length → 1 ≤ chunk.length) := by
    have hchunk_len_eq : chunk.length = min (min cnt Arm64.MAX_RW_COUNT) (stdinBytes.length - pos) := by
      rw [← hchunk_def, List.length_take, List.length_drop]
    have : 0 < Arm64.MAX_RW_COUNT := by decide
    omega
  rw [hchunk_def] at hx0_2 hopen2 ⊢
  simp only [arm64_norm] at hx0_2
  have hsp2_eq : s2.sp = s.sp := by rw [hsp2]; simp [wp_norm, arm64_norm]
  have hsp2_al : s2.spAligned = true := by simpa [State.spAligned, hsp2_eq] using hsp_al
  have herr2 : muslErrnoAddr s = muslErrnoAddr s2 := by
    simp [muslErrnoAddr, hnv2.tpidrEl0_eq, wp_norm, arm64_norm]
  apply sepWP_mono_atom (hnv2.heap_transport M)
  have hrepack_vec :
      (vecPtr ↦ₛ stdinBytes.take pos) ∗ ((vecPtr + BitVec.ofNat 64 pos) ↦ₛ chunk) ∗
      memRegion (vecPtr + BitVec.ofNat 64 pos + BitVec.ofNat 64 chunk.length) (cnt - chunk.length) ∗
      memRegion (vecPtr + BitVec.ofNat 64 pos + BitVec.ofNat 64 cnt) (cap - pos - cnt) ∗
      M.Block γ vecPtr cap ⊢
      HbByteVecBuf M γ cap vecPtr (stdinBytes.take (pos + chunk.length)) := by
    have hpb : (vecPtr ↦ₛ stdinBytes.take pos) ∗ ((vecPtr + BitVec.ofNat 64 pos) ↦ₛ chunk) ⊢
        (vecPtr ↦ₛ stdinBytes.take (pos + chunk.length)) := by
      rw [← hchunk_def, ← take_append_drop_take stdinBytes (min cnt Arm64.MAX_RW_COUNT) hpos_le, pointsToBytes_append, htk_len]
      exact Entails.refl _
    have hmr :
        memRegion (vecPtr + BitVec.ofNat 64 pos + BitVec.ofNat 64 chunk.length) (cnt - chunk.length) ∗
        memRegion (vecPtr + BitVec.ofNat 64 pos + BitVec.ofNat 64 cnt) (cap - pos - cnt) ⊢
        memRegion (vecPtr + BitVec.ofNat 64 (pos + chunk.length)) (cap - (pos + chunk.length)) := by
      rw [memRegion_split_le (vecPtr + BitVec.ofNat 64 (pos + chunk.length)) (cnt - chunk.length)
            (cap - (pos + chunk.length)) (by omega) (by omega)]
      have ha1 : vecPtr + BitVec.ofNat 64 pos + BitVec.ofNat 64 chunk.length =
          vecPtr + BitVec.ofNat 64 (pos + chunk.length) := by rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      have ha2 : vecPtr + BitVec.ofNat 64 (pos + chunk.length) + BitVec.ofNat 64 (cnt - chunk.length) =
          vecPtr + BitVec.ofNat 64 pos + BitVec.ofNat 64 cnt := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, show (pos + chunk.length) + (cnt - chunk.length) = pos + cnt by omega,
            BitVec.ofNat_add, ← BitVec.add_assoc]
      rw [ha1, ha2, show cap - (pos + chunk.length) - (cnt - chunk.length) = cap - pos - cnt by omega]
      exact Entails.refl _
    refine Entails.trans (by sep_entail)
      (Entails.trans (sepConj_mono hpb (sepConj_mono hmr (Entails.refl (M.Block γ vecPtr cap)))) ?_)
    simp only [HbByteVecBuf, hcap_ne, ↓reduceIte,
      List.length_take_of_le (by omega : pos + chunk.length ≤ stdinBytes.length)]
    exact Entails.pure_right ⟨hptr_nz, hptr_al, hptr_nw, by omega⟩ (by sep_entail)
  have hstk_merge : stackAt s.sp 32 ∗ stackAt (s.sp - BitVec.ofNat 64 32) (hbSmallProbeStackBytes - 32) ⊢
      stackAt s.sp hbSmallProbeStackBytes := by
    rw [stackAt_split_main s.sp 32 (hbSmallProbeStackBytes - 32) (n := hbSmallProbeStackBytes)]; sep_entail
  have hx19_2 : s2.readReg64 (.gpr 19#5) = vecSlotPtr := by
    rw [← Reg.x19, hcs2.readReg64_x19]; simp [wp_norm, arm64_norm, hx19]
  have hx22_2 : s2.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap := by
    rw [← Reg.x22, hcs2.readReg64_x22]; simp [wp_norm, arm64_norm, hx22]
  have hx26_2 : s2.readReg64 (.gpr 26#5) = 0#64 := by
    rw [← Reg.x26, hcs2.readReg64_x26]; simp [wp_norm, arm64_norm, hx26]
  have hx27_2 : s2.readReg64 (.gpr 27#5) = 0#64 := by
    rw [← Reg.x27, hcs2.readReg64_x27]; simp [wp_norm, arm64_norm, hx27]
  have hx28_2 : s2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 pos := by
    rw [← Reg.x28, hcs2.readReg64_x28]; simp [wp_norm, arm64_norm, hx28]
  have hcmn_ne : BitVec.ofNat 64 chunk.length + 1#64 ≠ 0#64 := by
    change BitVec.ofNat 64 chunk.length + BitVec.ofNat 64 1 ≠ 0#64
    rw [← BitVec.ofNat_add]; intro heq; have ht := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : chunk.length + 1 < 18446744073709551616)] at ht
    simp only [BitVec.toNat_ofNat] at ht; omega
  conv => arg 4; simp (config := { zetaDelta := false }) only [herr2, wp_norm, arm64_norm]
  apply sepWP_mono_atom hrepack_vec
  apply sepWP_mono_atom hstk_merge
  by_cases heof : pos = stdinBytes.length
  · subst heof
    have hchunk_nil : chunk = [] := by rw [← hchunk_def, List.drop_length, List.take_nil]
    subst hchunk_nil
    simp only [List.length_nil, List.drop_zero, List.drop_length] at hopen2 hx0_2 ⊢
    conv => arg 4; rw [show (s.sp ↦₆₄ 0#64) = (s2.sp ↦₆₄ 0#64) by rw [hsp2_eq]]
    refine SepWP.seq_nonVm (mid := C.defaultReadToEndAddr + 0x24c#64) hext hsvc ?_
    have hc_nv2 := (hc.withSvc nonVmSvc).defaultRead
    unpack_hb_subchunks hbDefaultReadToEndChunks hc_nv2 [10, 14]
    wp_steps; (try norm_jmp); wp_steps
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun2]) (fun hvm2 => ?_)
    apply sepWP_mono_atom (vmHeapTransport M hvm2)
    conv => arg 4; rw [show (s2.sp ↦₆₄ 0#64) = (s.sp ↦₆₄ 0#64) by rw [hsp2_eq]]
    conv => arg 4; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.zero_add]
    have hvec_full : (vecSlotPtr ↦₆₄ BitVec.ofNat 64 cap) ∗ ((vecSlotPtr + 0x08#64) ↦₆₄ vecPtr) ∗
        ((vecSlotPtr + 16#64) ↦₆₄ BitVec.ofNat 64 stdinBytes.length) ∗
        HbByteVecBuf M γ cap vecPtr (stdinBytes.take (stdinBytes.length + 0)) ⊢
        HbByteVec M γ vecSlotPtr cap vecPtr stdinBytes := by
      rw [Nat.add_zero, List.take_length, show (16#64 : BitVec 64) = 0x10#64 from rfl]
      dsimp only [HbByteVec]; sep_entail
    apply sepWP_mono_atom hvec_full
    refine SepWP.weaken_pre ?_ (defaultRead_epilogue_wp hc M γ
      (vecPtr := vecPtr) (w0 := 0#64) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5) (e1 := e0)
      hsvc hext hsp_d hsp0_al hcap_le
      wp_a (by simp [wp_norm, arm64_norm, hrun2]) (by simpa [wp_norm, arm64_norm] using hsp2_eq)
      (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp2_al)
      (by simp [wp_norm, arm64_norm, hx0_2])
      (by simp [wp_norm, arm64_norm] <;> bv_lin)
      (by simpa [wp_norm, arm64_norm] using hopen2)
      (by simp [wp_norm, arm64_norm, hcs2.vregs, hvregs])
      (by simp [wp_norm, arm64_norm, htr2, htr])
      (by simp [wp_norm, arm64_norm, hnv2.tpidrEl0_eq, htp])
      (by simp [wp_norm, arm64_norm, hnv2.sigActions_eq, hsig]))
    simp (config := { zetaDelta := false, failIfUnchanged := false }) only [muslErrnoAddr, wp_norm, arm64_norm]
    sep_entail
  · have hpos_lt_L : pos < stdinBytes.length := by omega
    have hchunk_pos : 1 ≤ chunk.length := hchunk_pos_imp hpos_lt_L
    have hchunk_nz : BitVec.ofNat 64 chunk.length ≠ 0#64 := by
      intro heq; have ht := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : chunk.length < 18446744073709551616)] at ht
      simp only [BitVec.toNat_ofNat] at ht; omega
    have hcap_nz : BitVec.ofNat 64 cap ≠ 0#64 := by
      intro heq; have ht := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cap < 18446744073709551616)] at ht
      simp only [BitVec.toNat_ofNat] at ht; omega
    have hadd_pos : BitVec.ofNat 64 chunk.length + BitVec.ofNat 64 pos =
        BitVec.ofNat 64 (pos + chunk.length) := by rw [← BitVec.ofNat_add, Nat.add_comm]
    have hvec_step : (vecSlotPtr ↦₆₄ BitVec.ofNat 64 cap) ∗ ((vecSlotPtr + 0x08#64) ↦₆₄ vecPtr) ∗
        ((vecSlotPtr + 16#64) ↦₆₄ (BitVec.ofNat 64 chunk.length + BitVec.ofNat 64 pos)) ∗
        HbByteVecBuf M γ cap vecPtr (stdinBytes.take (pos + chunk.length)) ⊢
        HbByteVec M γ vecSlotPtr cap vecPtr (stdinBytes.take (pos + chunk.length)) := by
      rw [hadd_pos, show (16#64 : BitVec 64) = 0x10#64 from rfl]
      dsimp only [HbByteVec]
      rw [List.length_take_of_le (by omega : pos + chunk.length ≤ stdinBytes.length)]
      sep_entail
    by_cases hfull : pos + chunk.length = cap
    · have heq_cap : BitVec.ofNat 64 chunk.length + BitVec.ofNat 64 pos = BitVec.ofNat 64 cap := by
        rw [hadd_pos, hfull]
      refine SepWP.seq_nonVm (mid := C.defaultReadToEndAddr + 0x118#64) hext hsvc ?_
      have hc_nv2 := (hc.withSvc nonVmSvc).defaultRead
      unpack_hb_subchunks hbDefaultReadToEndChunks hc_nv2 [10, 6]
      wp_steps; (try norm_jmp); wp_steps; (try norm_jmp)
      refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun2]) (fun hvm2 => ?_)
      apply sepWP_mono_atom (vmHeapTransport M hvm2)
      have hvec_step' : (vecSlotPtr ↦₆₄ BitVec.ofNat 64 cap) ∗ ((vecSlotPtr + 0x08#64) ↦₆₄ vecPtr) ∗
          ((vecSlotPtr + 16#64) ↦₆₄ BitVec.ofNat 64 cap) ∗
          HbByteVecBuf M γ cap vecPtr (stdinBytes.take (pos + chunk.length)) ⊢
          HbByteVec M γ vecSlotPtr cap vecPtr (stdinBytes.take (pos + chunk.length)) := by
        rw [show (16#64 : BitVec 64) = 0x10#64 from rfl]
        dsimp only [HbByteVec]
        rw [List.length_take_of_le (by omega : pos + chunk.length ≤ stdinBytes.length), hfull]
        sep_entail
      apply sepWP_mono_atom hvec_step'
      refine SepWP.weaken_pre ?_ (hloop _ (pos + chunk.length) (by omega) (by omega) (by omega)
        wp_a (by simp [wp_norm, arm64_norm, hrun2]) (by simpa [wp_norm, arm64_norm] using hsp2_eq)
        (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp2_al)
        (by simp [wp_norm, arm64_norm, hx19_2]) (by simp [wp_norm, arm64_norm, hx22_2])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx26_2])
        (by simp [wp_norm, arm64_norm, hx27_2]) (by simp [wp_norm, arm64_norm, hfull])
        (by simp only [wp_norm, arm64_norm]; rwa [List.drop_drop] at hopen2)
        (by simp [wp_norm, arm64_norm, hcs2.vregs, hvregs])
        (by simp [wp_norm, arm64_norm, htr2, htr])
        (by simp [wp_norm, arm64_norm, hnv2.tpidrEl0_eq, htp])
        (by simp [wp_norm, arm64_norm, hnv2.sigActions_eq, hsig]))
      simp (config := { zetaDelta := false, failIfUnchanged := false }) only [muslErrnoAddr, wp_norm, arm64_norm]
      sep_entail
    · have hne_cap : BitVec.ofNat 64 chunk.length + BitVec.ofNat 64 pos ≠ BitVec.ofNat 64 cap := by
        rw [hadd_pos]; intro heq; have ht := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pos + chunk.length < 18446744073709551616),
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cap < 18446744073709551616)] at ht
        omega
      refine SepWP.seq_nonVm (mid := C.defaultReadToEndAddr + 0x118#64) hext hsvc ?_
      have hc_nv2 := (hc.withSvc nonVmSvc).defaultRead
      unpack_hb_subchunks hbDefaultReadToEndChunks hc_nv2 [10]
      wp_steps; (try norm_jmp)
      refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun2]) (fun hvm2 => ?_)
      apply sepWP_mono_atom (vmHeapTransport M hvm2)
      apply sepWP_mono_atom hvec_step
      refine SepWP.weaken_pre ?_ (hloop _ (pos + chunk.length) (by omega) (by omega) (by omega)
        wp_a (by simp [wp_norm, arm64_norm, hrun2]) (by simpa [wp_norm, arm64_norm] using hsp2_eq)
        (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp2_al)
        (by simp [wp_norm, arm64_norm, hx19_2]) (by simp [wp_norm, arm64_norm, hx22_2])
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hx26_2])
        (by simp [wp_norm, arm64_norm, hx27_2]) (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm]; rwa [List.drop_drop] at hopen2)
        (by simp [wp_norm, arm64_norm, hcs2.vregs, hvregs])
        (by simp [wp_norm, arm64_norm, htr2, htr])
        (by simp [wp_norm, arm64_norm, hnv2.tpidrEl0_eq, htp])
        (by simp [wp_norm, arm64_norm, hnv2.sigActions_eq, hsig]))
      simp (config := { zetaDelta := false, failIfUnchanged := false }) only [muslErrnoAddr, wp_norm, arm64_norm]
      sep_entail

private theorem defaultRead_readLoop_wp {P : Program} {C : HbCliLayout} {L : Nat}
    (hc : HbUserMainCode P C) (hc_stdin : HbStdinAndVecCode P C) (hc_sys : HbSyscallsAndStderrCode P C)
    (M : HbMallocngIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    {sp_d vecSlotPtr w1 w2 : BitVec 64} {lc blk : Nat}
    {stdinBytes : List (BitVec 8)} {s0 : State} {R_frame : SepProp}
    (pos cap : Nat) (vecPtr w3 w4 w5 : BitVec 64) (e0 : BitVec 32) (s : State)
    (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    (hsp_d : sp_d = s0.sp - 144#64) (hsp0_al : s0.spAligned = true)
    (hL_eq : stdinBytes.length = L) (hL : L ≤ HashbrownCliMaxStdin)
    (hlc_le : lc ≤ mallocngBlockCost 1024 + mallocngBlockCost 8192) (hblk_le : blk ≤ 2)
    (hpos1 : 1 ≤ pos) (hpos_le : pos ≤ stdinBytes.length) (hpos_cap : pos ≤ cap)
    (hcap8 : 8 ≤ cap) (hcap_le : cap ≤ 2 * stdinBytes.length + 32)
    (hpc : s.pc = C.defaultReadToEndAddr + 0x118#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp_d) (hsp_al : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = vecSlotPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 cap)
    (hx25 : 1 ≤ (s.readReg64 .x25).toNat)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx27 : s.readReg64 .x27 = 0#64)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 pos)
    (hopen : HbStdinOpen (stdinBytes.drop pos) s.fs)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) (htp : s.tpidrEl0 = s0.tpidrEl0) (hsig : s.sigActions = s0.sigActions) :
    SepWP P (s0.readReg64 Reg.lr) s
      (HbByteVec M.toMallocngCoreIface γ vecSlotPtr cap vecPtr (stdinBytes.take pos) ∗
        (sp_d ↦₆₄ 0#64) ∗ ((sp_d + 0x08#64) ↦₆₄ w1) ∗ ((sp_d + 0x10#64) ↦₆₄ w2) ∗
        ((sp_d + 0x18#64) ↦₆₄ w3) ∗ ((sp_d + 0x20#64) ↦₆₄ w4) ∗ ((sp_d + 0x28#64) ↦₆₄ w5) ∗
        DefaultReadSavedRegs sp_d s0 ∗ stackAt sp_d hbSmallProbeStackBytes ∗
        M.Heap γ (lc + hbByteVecCost cap) (blk + hbByteVecBlocks cap) s ∗
        (muslErrnoAddr s ↦₃₂ e0) ∗ R_frame)
      (DefaultReadDonePost M.toMallocngCoreIface γ vecSlotPtr stdinBytes lc blk s0 R_frame) := by
  obtain ⟨rem, hrem_eq⟩ : ∃ rem, stdinBytes.length - pos = rem := ⟨_, rfl⟩
  revert hpos1 hpos_le hpos_cap hcap8 hcap_le hpc hrun hsp hsp_al hx19 hx22 hx25 hx26 hx27 hx28
    hopen hvregs htr htp hsig
  revert hrem_eq; revert pos cap vecPtr w3 w4 w5 e0 s
  induction rem using Nat.strongRecOn with | ind rem ih =>
  intro pos cap vecPtr w3 w4 w5 e0 s hrem_eq hpos1 hpos_le hpos_cap hcap8 hcap_le
    hpc hrun hsp hsp_al hx19 hx22 hx25 hx26 hx27 hx28 hopen hvregs htr htp hsig
  cases hsp.symm
  have hsp_d' : s0.sp - 144#64 = s.sp := hsp_d.symm
  clear hsp_d
  have hSL_bound : stdinBytes.length ≤ 10737418240 := hL_eq ▸ hL
  have hx19' : s.readReg64 (.gpr 19#5) = vecSlotPtr := hx19
  have hx22' : s.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap := hx22
  have hx28' : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 pos := hx28
  by_cases hlt : pos < cap
  · have hne_bv : BitVec.ofNat 64 pos ≠ BitVec.ofNat 64 cap := by
      intro heq; have ht := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pos < 18446744073709551616),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cap < 18446744073709551616)] at ht
      omega
    conv => arg 4; dsimp only [HbByteVec]
    refine SepWP.seq_nonVm (mid := C.defaultReadToEndAddr + 0x128#64) hext hsvc ?_
    have hc_nv := (hc.withSvc nonVmSvc).defaultRead
    unpack_hb_subchunks hbDefaultReadToEndChunks hc_nv [8]
    wp_steps 4
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) (fun hvm1 => ?_)
    apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm1)
    have hvec_re : (vecSlotPtr ↦₆₄ BitVec.ofNat 64 cap) ∗ ((vecSlotPtr + 0x08#64) ↦₆₄ vecPtr) ∗
        ((vecSlotPtr + 0x10#64) ↦₆₄ BitVec.ofNat 64 (stdinBytes.take pos).length) ∗
        HbByteVecBuf M.toMallocngCoreIface γ cap vecPtr (stdinBytes.take pos) ⊢
        HbByteVec M.toMallocngCoreIface γ vecSlotPtr cap vecPtr (stdinBytes.take pos) := by
      dsimp only [HbByteVec]; sep_entail
    apply sepWP_mono_atom hvec_re
    refine SepWP.weaken_pre ?_ (defaultRead_readStep_wp hc hc_sys M.toMallocngCoreIface γ
      hsvc hext hsp_d'.symm hsp0_al (hL_eq ▸ hL) hpos1 hpos_le hlt hcap8 hcap_le
      wp_a (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm])
      (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al)
      (by simp [wp_norm, arm64_norm, hx19]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simpa [wp_norm, arm64_norm] using hx25)
      (by simp [wp_norm, arm64_norm, hx26]) (by simp [wp_norm, arm64_norm, hx27])
      (by simp [wp_norm, arm64_norm, hx28]) (by simpa [wp_norm, arm64_norm] using hopen)
      (by simp [wp_norm, arm64_norm, hvregs]) (by simp [wp_norm, arm64_norm, htr])
      (by simp [wp_norm, arm64_norm, htp]) (by simp [wp_norm, arm64_norm, hsig])
      (fun s' pos' hgt hp_le hp_cap hpc' hrun' hsp' hal' hx19' hx22' hx25' hx26' hx27' hx28' ho' hv' htr' htp' hsig' =>
        ih (stdinBytes.length - pos') (show stdinBytes.length - pos' < rem by omega)
          pos' cap vecPtr w3 w4 w5 e0 s' rfl (by omega) hp_le hp_cap hcap8 hcap_le
          hpc' hrun' hsp' hal' hx19' hx22' hx25' hx26' hx27' hx28' ho' hv' htr' htp' hsig'))
    simp (config := { zetaDelta := false, failIfUnchanged := false }) only [muslErrnoAddr, wp_norm, arm64_norm]
    sep_entail
  · have hpos_eq : pos = cap := by omega
    subst hpos_eq
    have hcap_L : pos ≤ L := by omega
    obtain ⟨hnew_le, _, hpeak_fn⟩ := hbCli_vecGrow_budget (by omega) hcap_L hL
    let newCap := max (pos + 32) (2 * pos)
    have hlsl_eq : (BitVec.ofNat 64 pos) <<< 1 = BitVec.ofNat 64 (2 * pos) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : pos < 18446744073709551616),
        Nat.mod_eq_of_lt (by omega : 2 * pos < 18446744073709551616)]
      rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : pos * 2 ^ 1 < 18446744073709551616)]; omega
    have hadd32_eq : BitVec.ofNat 64 pos + 32#64 = BitVec.ofNat 64 (pos + 32) :=
      (BitVec.ofNat_add pos 32).symm
    have hcsel_new : (if BitVec.ult (BitVec.ofNat 64 (2 * pos)) (BitVec.ofNat 64 (pos + 32)) = true
        then BitVec.ofNat 64 (pos + 32) else BitVec.ofNat 64 (2 * pos)) = BitVec.ofNat 64 newCap := by
      simp only [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 2 * pos < 18446744073709551616),
        Nat.mod_eq_of_lt (by omega : pos + 32 < 18446744073709551616)]
      split <;> (congr 1; omega)
    conv => arg 4; dsimp only [HbByteVec]
    conv => arg 4; rw [stackAt_split_main s.sp (48 + MallocngStackBytes)
      (hbSmallProbeStackBytes - (48 + MallocngStackBytes)) (n := hbSmallProbeStackBytes)]
    refine SepWP.seq_nonVm (mid := C.rawVecFinishGrowAddr) hext hsvc ?_
    have hc_nv1 := (hc.withSvc nonVmSvc).defaultRead
    unpack_hb_subchunks hbDefaultReadToEndChunks hc_nv1 [8, 11, 12]
    iterate 3 (wp_steps; (try norm_jmp))
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) (fun hvm1 => ?_)
    have hcap_ne0 : pos ≠ 0 := by omega
    have hnew_ne0 : newCap ≠ 0 := by dsimp [newCap]; omega
    have hmax_blk_val : (hbStdLimits L).maxPeakBlocks = 5 := rfl
    refine hbRawVecFinishGrow_wp hc_stdin M γ hvm1
      (outPtr := s.sp + 0x18#64) (v0 := w3) (v1 := w4) (v2 := w5)
      (oldCap := pos) (oldPtr := vecPtr) (bs := stdinBytes.take pos)
      (newCap := newCap) (lc := lc + hbByteVecCost pos) (blk := blk + hbByteVecBlocks pos)
      (sp_call := s.sp) (ret_pc := C.defaultReadToEndAddr + 0x224#64)
      (by dsimp [newCap]; omega) (by dsimp [newCap]; omega) (by dsimp [newCap]; omega)
      (by simp [hbByteVecBlocks, hcap_ne0])
      (by dsimp [newCap, hbStdLimits]; omega)
      (hpeak_fn (lc + hbByteVecCost pos) (by simp only [hbByteVecCost, hcap_ne0, ↓reduceIte]; omega))
      (by rw [hmax_blk_val]; simp only [hbByteVecBlocks, hcap_ne0, ↓reduceIte]; omega)
      (by simp (config := { zetaDelta := false }) only [BitVec.add_assoc, BitVec.reduceAdd]; sep_frame)
      (fun s2 newPtr e1 hpc2 hrun2 hsp2 hcs2 hmsp2 => ?_) hsvc hext
      (hsp_align := by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al)
      (hx0 := wp_a)
      (hx1 := by simp [wp_norm, arm64_norm])
      (hx2 := by simp [wp_norm, arm64_norm])
      (hx3 := by simp [wp_norm, arm64_norm])
    conv => arg 4; simp (config := { zetaDelta := false }) only [BitVec.add_assoc, BitVec.reduceAdd,
      hbByteVecCost, hbByteVecBlocks, hcap_ne0, ↓reduceIte, Nat.add_sub_cancel]
    have hsp2_eq : s2.sp = s.sp := by rw [hsp2]; simp [wp_norm, arm64_norm]
    clear hsp2
    have hsp2_al : ((s2.sp &&& 15#64) == 0#64) = true := by
      simpa [State.spAligned, hsp2_eq] using hsp_al
    have hx19_2 : s2.readReg64 (.gpr 19#5) = vecSlotPtr := by
      rw [← Reg.x19, hcs2.readReg64_x19]; simp [wp_norm, arm64_norm, hx19]
    have hx24_2 : s2.readReg64 (.gpr 24#5) = BitVec.ofNat 64 newCap := by
      rw [← Reg.x24, hcs2.readReg64_x24]; simp [wp_norm, arm64_norm]
    have hx25_2 : 1 ≤ (s2.readReg64 .x25).toNat := by
      rw [hcs2.readReg64_x25]; simpa [wp_norm, arm64_norm] using hx25
    have hx26_2 : s2.readReg64 (.gpr 26#5) = 0#64 := by
      rw [← Reg.x26, hcs2.readReg64_x26]; simp [wp_norm, arm64_norm, hx26]
    have hx27_2 : s2.readReg64 (.gpr 27#5) = 0#64 := by
      rw [← Reg.x27, hcs2.readReg64_x27]; simp [wp_norm, arm64_norm, hx27]
    have hx28_2 : s2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 pos := by
      rw [← Reg.x28, hcs2.readReg64_x28]; simp [wp_norm, arm64_norm, hx28]
    conv => arg 4; rw [show ((s.sp + 24#64) ↦₆₄ 0#64) = ((s2.sp + 24#64) ↦₆₄ 0#64) by rw [hsp2_eq],
      show ((s.sp + 32#64) ↦₆₄ newPtr) = ((s2.sp + 32#64) ↦₆₄ newPtr) by rw [hsp2_eq]]
    refine SepWP.seq_nonVm (mid := C.defaultReadToEndAddr + 0x128#64) hext hsvc ?_
    have hc_nv2 := (hc.withSvc nonVmSvc).defaultRead
    unpack_hb_subchunks hbDefaultReadToEndChunks hc_nv2 [13]
    wp_steps; norm_jmp
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun2]) (fun hvm2 => ?_)
    apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm2)
    conv => arg 4; rw [show ((s2.sp + 24#64) ↦₆₄ 0#64) = ((s.sp + 24#64) ↦₆₄ 0#64) by rw [hsp2_eq],
      show ((s2.sp + 32#64) ↦₆₄ newPtr) = ((s.sp + 32#64) ↦₆₄ newPtr) by rw [hsp2_eq]]
    have hstk_fg : stackAt s.sp (48 + MallocngStackBytes) ∗
        stackAt (s.sp - BitVec.ofNat 64 (48 + MallocngStackBytes))
          (hbSmallProbeStackBytes - (48 + MallocngStackBytes)) ⊢
        stackAt s.sp hbSmallProbeStackBytes := by
      rw [stackAt_split_main s.sp (48 + MallocngStackBytes)
        (hbSmallProbeStackBytes - (48 + MallocngStackBytes)) (n := hbSmallProbeStackBytes)]
      sep_entail
    have hvec_fg : (vecSlotPtr ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((vecSlotPtr + 8#64) ↦₆₄ newPtr) ∗
        ((vecSlotPtr + 0x10#64) ↦₆₄ BitVec.ofNat 64 (stdinBytes.take pos).length) ∗
        HbByteVecBuf M.toMallocngCoreIface γ newCap newPtr (stdinBytes.take pos) ⊢
        HbByteVec M.toMallocngCoreIface γ vecSlotPtr newCap newPtr (stdinBytes.take pos) := by
      rw [show (8#64 : BitVec 64) = 0x08#64 from rfl]; dsimp only [HbByteVec]; sep_entail
    conv => arg 4; rw [show lc + mallocngBlockCost newCap = lc + hbByteVecCost newCap by
      simp [hbByteVecCost, hnew_ne0], show blk + 1 = blk + hbByteVecBlocks newCap by
      simp [hbByteVecBlocks, hnew_ne0]]
    apply sepWP_mono_atom hstk_fg
    apply sepWP_mono_atom hvec_fg
    refine SepWP.weaken_pre ?_ (defaultRead_readStep_wp hc hc_sys M.toMallocngCoreIface γ
      hsvc hext hsp_d'.symm hsp0_al (hL_eq ▸ hL) hpos1 hpos_le (by dsimp [newCap]; omega)
      (by dsimp [newCap]; omega) (by rw [hL_eq]; exact hnew_le)
      wp_a (by simp [wp_norm, arm64_norm, hrun2]) (by simpa [wp_norm, arm64_norm] using hsp2_eq)
      (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp2_al)
      (by simp [wp_norm, arm64_norm, hx19_2]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simpa [wp_norm, arm64_norm] using hx25_2)
      (by simp [wp_norm, arm64_norm, hx26_2]) (by simp [wp_norm, arm64_norm, hx27_2])
      (by simp [wp_norm, arm64_norm, hx28_2])
      (by simp only [wp_norm, arm64_norm]; rw [hmsp2.1]; simpa [wp_norm, arm64_norm] using hopen)
      (by simp [wp_norm, arm64_norm, hcs2.vregs, hvregs])
      (by simp only [wp_norm, arm64_norm]; rw [hmsp2.2.1]; simp [wp_norm, arm64_norm, htr])
      (by simp only [wp_norm, arm64_norm]; rw [hmsp2.2.2.2.1]; simp [wp_norm, arm64_norm, htp])
      (by simp only [wp_norm, arm64_norm]; rw [hmsp2.2.2.1]; simp [wp_norm, arm64_norm, hsig])
      (fun s' pos' hgt hp_le hp_cap hpc' hrun' hsp' hal' hx19' hx22' hx25' hx26' hx27' hx28' ho' hv' htr' htp' hsig' =>
        ih (stdinBytes.length - pos') (show stdinBytes.length - pos' < rem by omega)
          pos' newCap newPtr 0#64 newPtr (BitVec.ofNat 64 newCap) e1 s' rfl
          (by omega) hp_le hp_cap (by dsimp [newCap]; omega) (by rw [hL_eq]; exact hnew_le)
          hpc' hrun' hsp' hal' hx19' hx22' hx25' hx26' hx27' hx28' ho' hv' htr' htp' hsig'))
    simp (config := { zetaDelta := false, failIfUnchanged := false }) only [muslErrnoAddr, wp_norm, arm64_norm]
    sep_entail

/-- Placement-generic `SepWP` specification for `std::io::default_read_to_end`
    (`C.defaultReadToEndAddr`, `hbDefaultReadToEndChunks C`) on an initially empty `Vec<u8>`. -/
theorem defaultReadToEnd_wp {P : Program} {C : HbCliLayout} {L : Nat}
    {target_pc ret_pc sp_call : BitVec 64}
    (hc : HbUserMainCode P C) (hc_stdin : HbStdinAndVecCode P C) (hc_sys : HbSyscallsAndStderrCode P C)
    (hMem : StdMemOps P C.std.memcpyAddr C.std.memsetAddr)
    (M : HbMallocngIface P C.mallocng (hbStdLimits L)) (γ : GhostName)
    {vecSlotPtr ptr0 : BitVec 64} {lc blk : Nat}
    {stdinBytes : List (BitVec 8)} {e0 : BitVec 32}
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    (hL_eq : stdinBytes.length = L := by rfl) (hL : L ≤ HashbrownCliMaxStdin)
    (hlc_le : lc ≤ mallocngBlockCost 1024 + mallocngBlockCost 8192 := by omega)
    (hblk_le : blk ≤ 2 := by omega)
    (hpc : s.pc = C.defaultReadToEndAddr) (hrun : s.status = .Running)
    (hsp_call : s.sp = sp_call) (hsp_align : s.spAligned = true)
    (hsp_lo : 288 ≤ sp_call.toNat) (hsp_va : sp_call.toNat ≤ Arm64.USER_VA_LIMIT)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = vecSlotPtr) (hx1 : s.readReg64 .x1 = 0#64)
    (hopen : HbStdinOpen stdinBytes s.fs)
    (hpre : Pre ⊢ HbByteVec M.toMallocngCoreIface γ vecSlotPtr 0 ptr0 [] ∗
      M.Heap γ lc blk s ∗ (muslErrnoAddr s ↦₃₂ e0) ∗
      stackAt sp_call hbDefaultReadStackBytes ∗ F)
    (hnext : ∀ (sf : State) (cap : Nat) (vecPtr : BitVec 64) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.spAligned = true →
      sf.readReg64 .x0 = 0#64 → sf.readReg64 .x1 = BitVec.ofNat 64 stdinBytes.length →
      CalleeSavedPreserved s sf →
      cap ≤ 2 * stdinBytes.length + 32 → HbStdinOpen [] sf.fs →
      sf.trace = s.trace → sf.tpidrEl0 = s.tpidrEl0 → sf.sigActions = s.sigActions →
      s.mem.KeepsFrozen sf.mem →
      SepWP P target_pc sf
        (HbByteVec M.toMallocngCoreIface γ vecSlotPtr cap vecPtr stdinBytes ∗
          M.Heap γ (lc + hbByteVecCost cap) (blk + hbByteVecBlocks cap) sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt sp_call hbDefaultReadStackBytes ∗ F) post) :
    SepWP P target_pc s Pre post := by
  cases hsp_call
  cases hlr
  obtain ⟨sp_d, hsp_d_def⟩ : ∃ sp_d, s.sp - 144#64 = sp_d := ⟨_, rfl⟩
  have hsp_d_al : ((sp_d &&& 15#64) == 0#64) = true := hsp_d_def ▸ s.spAligned_sub 144#64 hsp_align
  have hx0' : s.readReg64 (.gpr 0#5) = vecSlotPtr := hx0
  have hx1' : s.readReg64 (.gpr 1#5) = 0#64 := hx1
  refine SepWP.seq (mid := s.readReg64 Reg.lr)
    (Mid := fun sf Pf => s.mem.KeepsFrozen sf.mem ∧
      DefaultReadDonePost M.toMallocngCoreIface γ vecSlotPtr stdinBytes lc blk s F sf Pf) ?_ ?_
  · apply SepWP.weaken_pre hpre
    refine SepWP.mono_frozen (Φ := s.mem.KeepsFrozen) (fun _ _ => Memory.KeepsFrozen.trans)
      (Memory.KeepsFrozen.refl s.mem)
      (post := DefaultReadDonePost M.toMallocngCoreIface γ vecSlotPtr stdinBytes lc blk s F)
      ?_ (fun _ _ _ _ hkf hdone => ⟨hkf, hdone⟩)
    conv => arg 4; rw [show hbDefaultReadStackBytes = hbSmallProbeStackBytes + 8 * 18 from rfl,
      stackAt_split_cells s.sp hbSmallProbeStackBytes 18 (by decide),
      show s.sp - BitVec.ofNat 64 (8 * 18) = sp_d from hsp_d_def]; dsimp only [HbByteVec]
    conv => arg 4; simp (config := { zetaDelta := false }) only [cells_succ, cells_zero,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_left fun w0 => SepWP.exists_left fun w1 => SepWP.exists_left fun w2 =>
      SepWP.exists_left fun w3 => SepWP.exists_left fun w4 => SepWP.exists_left fun w5 => ?_
    iterate 12 (apply SepWP.exists_left; intro _)
    refine SepWP.seq_nonVm (mid := C.smallProbeReadAddr) hext hsvc ?_
    have hc_nv1 := (hc.withSvc nonVmSvc).defaultRead
    unpack_hb_subchunks hbDefaultReadToEndChunks hc_nv1 [0, 1, 2]
    wp_steps; (try norm_jmp); wp_steps; (try norm_jmp)
    refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun]) (fun hvm1 => ?_)
    have hsaved :
        ((sp_d + 48#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((sp_d + 56#64) ↦₆₄ s.readReg64 (.gpr 30#5)) ∗
        ((sp_d + 64#64) ↦₆₄ s.readReg64 (.gpr 28#5)) ∗ ((sp_d + 72#64) ↦₆₄ s.readReg64 (.gpr 27#5)) ∗
        ((sp_d + 80#64) ↦₆₄ s.readReg64 (.gpr 26#5)) ∗ ((sp_d + 88#64) ↦₆₄ s.readReg64 (.gpr 25#5)) ∗
        ((sp_d + 96#64) ↦₆₄ s.readReg64 (.gpr 24#5)) ∗ ((sp_d + 104#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
        ((sp_d + 112#64) ↦₆₄ s.readReg64 (.gpr 22#5)) ∗ ((sp_d + 120#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
        ((sp_d + 128#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((sp_d + 136#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ⊢
        DefaultReadSavedRegs sp_d s := by
      dsimp only [DefaultReadSavedRegs]; simp only [arm64_norm]; sep_entail
    have hvec0 :
        (vecSlotPtr ↦₆₄ BitVec.ofNat 64 0) ∗ ((vecSlotPtr + 0x08#64) ↦₆₄ ptr0) ∗
        ((vecSlotPtr + 0x10#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length) ∗
        HbByteVecBuf M.toMallocngCoreIface γ 0 ptr0 [] ⊢
        HbByteVec M.toMallocngCoreIface γ vecSlotPtr 0 ptr0 [] := by
      dsimp only [HbByteVec]; sep_entail
    apply sepWP_mono_atom hsaved
    apply sepWP_mono_atom hvec0
    have hsp_d_lo : 144 ≤ sp_d.toNat := by
      rw [← hsp_d_def]; bv_omega
    have hsp_d_va : sp_d.toNat ≤ Arm64.USER_VA_LIMIT := by
      rw [← hsp_d_def]; unfold Arm64.USER_VA_LIMIT at hsp_va ⊢; bv_omega
    refine hbSmallProbeRead_wp hc_stdin hc_sys hMem M γ hvm1
      (vecPtr := vecSlotPtr) (cap := 0) (ptr := ptr0) (bs := []) (rem := stdinBytes)
      (lc := lc) (blk := blk) (sp_call := sp_d) (ret_pc := C.defaultReadToEndAddr + 0x94#64)
      (by simpa [wp_norm, arm64_norm] using hopen)
      hsp_d_lo hsp_d_va
      (by decide) (by decide)
      (fun _ => by
        simp only [List.length_nil]
        have htk : (stdinBytes.take 32).length ≤ 32 := List.length_take_le 32 stdinBytes
        have hm8 : max (max (0 + (stdinBytes.take 32).length) (2 * 0)) 8 ≤ 32 := by omega
        refine ⟨Nat.zero_le _, by dsimp [hbStdLimits]; omega, ?_, by dsimp [hbStdLimits]; omega⟩
        dsimp only [hbStdLimits, mallocngBlockCost, MallocngMinBlockCost] at hlc_le ⊢; omega)
      (by sep_frame)
      (fun s1 ptr1 e1 hpc1 hrun1 hsp1 hcs1 hx0_1 hx1_1 hopen1 htr1 htp1 hsig1 _ => ?_) hsvc hext
      (hsp_call := by simp [wp_norm, arm64_norm])
      (hsp_align := by simpa [State.spAligned, wp_norm, arm64_norm, hsp_d_def] using hsp_d_al)
      (hx0 := by simp [wp_norm, arm64_norm])
    simp (config := { zetaDelta := false }) only [List.nil_append, List.length_nil, Nat.sub_zero,
      Nat.zero_add, Nat.mul_zero] at hx1_1 hopen1 ⊢
    have hsp1_eq : s1.sp = sp_d := by rw [hsp1]; simp [wp_norm, arm64_norm]
    clear hsp1
    have hsp1_al : ((s1.sp &&& 15#64) == 0#64) = true := by
      simpa [State.spAligned, hsp1_eq] using hsp_d_al
    have hx0_1' : s1.readReg64 (.gpr 0#5) = 0#64 := hx0_1
    have hx19_1 : s1.readReg64 (.gpr 19#5) = vecSlotPtr := by
      rw [← Reg.x19, hcs1.readReg64_x19]; simp [wp_norm, arm64_norm]
    have hx25_1 : s1.readReg64 (.gpr 25#5) = 8192#64 := by
      rw [← Reg.x25, hcs1.readReg64_x25]; simp [wp_norm, arm64_norm]
    have hx26_1 : s1.readReg64 (.gpr 26#5) = 0#64 := by
      rw [← Reg.x26, hcs1.readReg64_x26]; simp [wp_norm, arm64_norm]
    have hx27_1 : s1.readReg64 (.gpr 27#5) = 0#64 := by
      rw [← Reg.x27, hcs1.readReg64_x27]; simp [wp_norm, arm64_norm]
    have hx28_1 : s1.readReg64 (.gpr 28#5) = 0#64 := by
      rw [← Reg.x28, hcs1.readReg64_x28]; simp [wp_norm, arm64_norm]
    have hv_1 : calleeSavedVRegs s1 = calleeSavedVRegs s := by
      rw [hcs1.vregs]; simp [wp_norm, arm64_norm]
    have htr_1 : s1.trace = s.trace := by rw [htr1]; simp [wp_norm, arm64_norm]
    have htp_1 : s1.tpidrEl0 = s.tpidrEl0 := by rw [htp1]; simp [wp_norm, arm64_norm]
    have hsig_1 : s1.sigActions = s.sigActions := by rw [hsig1]; simp [wp_norm, arm64_norm]
    rcases stdinBytes with _ | ⟨b0, bsRest⟩
    · simp (config := { zetaDelta := false }) only [List.take_nil, List.length_nil, Nat.lt_irrefl,
        ↓reduceIte] at hx1_1 hopen1 ⊢
      have hx1_1' : s1.readReg64 (.gpr 1#5) = 0#64 := hx1_1
      refine SepWP.seq_nonVm (mid := C.defaultReadToEndAddr + 0x24c#64) hext hsvc ?_
      have hc_nv2 := (hc.withSvc nonVmSvc).defaultRead
      unpack_hb_subchunks hbDefaultReadToEndChunks hc_nv2 [3, 5, 14]
      iterate 4 (wp_steps; (try norm_jmp))
      refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun1]) (fun hvm2 => ?_)
      apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm2)
      refine SepWP.weaken_pre ?_ (defaultRead_epilogue_wp hc M.toMallocngCoreIface γ
        (vecPtr := ptr1) (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
        (cap := 0) (e1 := e1)
        hsvc hext hsp_d_def.symm hsp_align (by omega)
        wp_a (by simp [wp_norm, arm64_norm, hrun1]) (by simpa [wp_norm, arm64_norm] using hsp1_eq)
        (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp1_al)
        (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
        (by simpa [wp_norm, arm64_norm] using hopen1)
        (by simp [wp_norm, arm64_norm, hv_1]) (by simp [wp_norm, arm64_norm, htr_1])
        (by simp [wp_norm, arm64_norm, htp_1]) (by simp [wp_norm, arm64_norm, hsig_1]))
      simp (config := { zetaDelta := false, failIfUnchanged := false }) only [hbByteVecCost,
        hbByteVecBlocks, ↓reduceIte, Nat.add_zero, muslErrnoAddr, wp_norm, arm64_norm]
      sep_entail
    · obtain ⟨stdinNe, hstdinNe_def⟩ : ∃ stdinNe, b0 :: bsRest = stdinNe := ⟨_, rfl⟩
      rw [hstdinNe_def] at hL_eq hx1_1 hopen1 ⊢
      obtain ⟨pos0, hpos0_def⟩ : ∃ pos0, (stdinNe.take 32).length = pos0 := ⟨_, rfl⟩
      obtain ⟨cap0, hcap0_def⟩ : ∃ cap0, max (max pos0 0) 8 = cap0 := ⟨_, rfl⟩
      have hpos0_1 : 1 ≤ pos0 := by rw [← hpos0_def, ← hstdinNe_def]; simp
      have hpos0_pos : 0 < pos0 := by omega
      have hpos0_32 : pos0 ≤ 32 := hpos0_def ▸ List.length_take_le 32 stdinNe
      have hpos0_le : pos0 ≤ stdinNe.length := hpos0_def ▸ List.length_take_le' 32 stdinNe
      have hlen_tk0 : (stdinNe.take pos0).length = pos0 := List.length_take_of_le hpos0_le
      have hcap0_8 : 8 ≤ cap0 := hcap0_def ▸ Nat.le_max_right _ 8
      have hcap0_32 : cap0 ≤ 32 := by rw [← hcap0_def]; omega
      have hpos0_cap0 : pos0 ≤ cap0 := by rw [← hcap0_def]; omega
      have hpos0_nz : BitVec.ofNat 64 pos0 ≠ 0#64 := by
        intro heq; have ht := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht; simp at ht; omega
      have hpos0_beq : (BitVec.ofNat 64 pos0 == 0#64) = false := beq_eq_false_iff_ne.mpr hpos0_nz
      have hcap0_nz : BitVec.ofNat 64 cap0 ≠ 0#64 := by
        intro heq; have ht := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht; simp at ht; omega
      have hcap0_beq : (BitVec.ofNat 64 cap0 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0_nz
      have hcap0_bne : (BitVec.ofNat 64 cap0 != 0#64) = true := bne_iff_ne.mpr hcap0_nz
      have htk_eq : stdinNe.take 32 = stdinNe.take pos0 := by
        have h := take_append_drop_take stdinNe 32 (pos := 0) (Nat.zero_le _)
        simpa [hpos0_def] using h
      simp (config := { zetaDelta := false }) only [hpos0_def, hpos0_pos, ↓reduceIte, hcap0_def,
        hbByteVecCost, hbByteVecBlocks, Nat.sub_zero] at hx1_1 hopen1 ⊢
      have hx1_1' : s1.readReg64 (.gpr 1#5) = BitVec.ofNat 64 pos0 := hx1_1
      conv => arg 4; rw [htk_eq, show (sp_d ↦₆₄ w0) = (s1.sp ↦₆₄ w0) by rw [hsp1_eq],
        show ((sp_d + 8#64) ↦₆₄ w1) = ((s1.sp + 8#64) ↦₆₄ w1) by rw [hsp1_eq],
        show ((sp_d + 16#64) ↦₆₄ w2) = ((s1.sp + 16#64) ↦₆₄ w2) by rw [hsp1_eq]]; dsimp only [HbByteVec]; rw [hlen_tk0]
      have hvec_init : (vecSlotPtr ↦₆₄ BitVec.ofNat 64 cap0) ∗ ((vecSlotPtr + 0x08#64) ↦₆₄ ptr1) ∗
          ((vecSlotPtr + 0x10#64) ↦₆₄ BitVec.ofNat 64 pos0) ∗
          HbByteVecBuf M.toMallocngCoreIface γ cap0 ptr1 (stdinNe.take pos0) ⊢
          HbByteVec M.toMallocngCoreIface γ vecSlotPtr cap0 ptr1 (stdinNe.take pos0) := by
        dsimp only [HbByteVec]; rw [hlen_tk0]; sep_entail
      by_cases hfull0 : pos0 = cap0
      · have heq0 : BitVec.ofNat 64 pos0 = BitVec.ofNat 64 cap0 := by rw [hfull0]
        refine SepWP.seq_nonVm (mid := C.defaultReadToEndAddr + 0x118#64) hext hsvc ?_
        have hc_nv2 := (hc.withSvc nonVmSvc).defaultRead
        unpack_hb_subchunks hbDefaultReadToEndChunks hc_nv2 [3, 4, 5, 6]
        iterate 5 (wp_steps; (try norm_jmp))
        refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun1]) (fun hvm2 => ?_)
        apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm2)
        apply sepWP_mono_atom hvec_init
        refine SepWP.weaken_pre ?_ (defaultRead_readLoop_wp hc hc_stdin hc_sys M γ
          (w1 := 0#64) (w2 := 0#64) pos0 cap0 ptr1 w3 w4 w5 e1 _
          hsvc hext hsp_d_def.symm hsp_align hL_eq hL hlc_le hblk_le
          hpos0_1 hpos0_le hpos0_cap0 hcap0_8 (by omega)
          wp_a (by simp [wp_norm, arm64_norm, hrun1]) (by simpa [wp_norm, arm64_norm] using hsp1_eq)
          (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp1_al)
          (by simp [wp_norm, arm64_norm, hx19_1]) (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hx25_1]) (by simp [wp_norm, arm64_norm, hx26_1])
          (by simp [wp_norm, arm64_norm, hx27_1]) (by simp [wp_norm, arm64_norm, hfull0])
          (by simpa [wp_norm, arm64_norm] using hopen1)
          (by simp [wp_norm, arm64_norm, hv_1]) (by simp [wp_norm, arm64_norm, htr_1])
          (by simp [wp_norm, arm64_norm, htp_1]) (by simp [wp_norm, arm64_norm, hsig_1]))
        simp (config := { zetaDelta := false, failIfUnchanged := false }) only [hbByteVecCost,
          hbByteVecBlocks, show cap0 ≠ 0 by omega, ↓reduceIte, hsp1_eq, muslErrnoAddr, wp_norm, arm64_norm]
        sep_entail
      · have hne0 : BitVec.ofNat 64 pos0 ≠ BitVec.ofNat 64 cap0 := by
          intro heq; have ht := congrArg BitVec.toNat heq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
              BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht; omega
        have hne0_beq : (BitVec.ofNat 64 pos0 == BitVec.ofNat 64 cap0) = false := beq_eq_false_iff_ne.mpr hne0
        refine SepWP.seq_nonVm (mid := C.defaultReadToEndAddr + 0x118#64) hext hsvc ?_
        have hc_nv2 := (hc.withSvc nonVmSvc).defaultRead
        unpack_hb_subchunks hbDefaultReadToEndChunks hc_nv2 [3, 4, 5]
        iterate 4 (wp_steps; (try norm_jmp))
        refine SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun1]) (fun hvm2 => ?_)
        apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm2)
        apply sepWP_mono_atom hvec_init
        refine SepWP.weaken_pre ?_ (defaultRead_readLoop_wp hc hc_stdin hc_sys M γ
          (w1 := 0#64) (w2 := 0#64) pos0 cap0 ptr1 w3 w4 w5 e1 _
          hsvc hext hsp_d_def.symm hsp_align hL_eq hL hlc_le hblk_le
          hpos0_1 hpos0_le hpos0_cap0 hcap0_8 (by omega)
          wp_a (by simp [wp_norm, arm64_norm, hrun1]) (by simpa [wp_norm, arm64_norm] using hsp1_eq)
          (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp1_al)
          (by simp [wp_norm, arm64_norm, hx19_1]) (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hx25_1]) (by simp [wp_norm, arm64_norm, hx26_1])
          (by simp [wp_norm, arm64_norm, hx27_1]) (by simp [wp_norm, arm64_norm])
          (by simpa [wp_norm, arm64_norm] using hopen1)
          (by simp [wp_norm, arm64_norm, hv_1]) (by simp [wp_norm, arm64_norm, htr_1])
          (by simp [wp_norm, arm64_norm, htp_1]) (by simp [wp_norm, arm64_norm, hsig_1]))
        simp (config := { zetaDelta := false, failIfUnchanged := false }) only [hbByteVecCost,
          hbByteVecBlocks, show cap0 ≠ 0 by omega, ↓reduceIte, hsp1_eq, muslErrnoAddr, wp_norm, arm64_norm]
        sep_entail
  · rintro sf Pf hpc_f hrun_f ⟨hkf, cap, vecPtr, e1, hcap_le, hopen_f, hsp_f, hal_f,
      hx0_f, hx1_f, hcs_f, htr_f, htp_f, hsig_f, hPf⟩
    exact SepWP.weaken_pre hPf
      (hnext sf cap vecPtr e1 hpc_f hrun_f hsp_f hal_f hx0_f hx1_f hcs_f hcap_le hopen_f
        htr_f htp_f hsig_f hkf)

end CaseStudies.Hashbrown.Proofs.StdCli
