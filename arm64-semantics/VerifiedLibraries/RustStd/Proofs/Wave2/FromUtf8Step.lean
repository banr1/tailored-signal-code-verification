/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.ExecSeg
public import VerifiedLibraries.RustStd.Proofs.CoreIo
public import VerifiedLibraries.RustStd.Spec.CoreFromUtf8
public import VerifiedLibraries.RustStd.Proofs.Wave2.FromUtf8Lemmas
public import ProofLib.GenPlacedFetches
public import ProofLib
public meta import ProofLib.ProgramReflection

/-!
# Block-Local Pure Segment, Return Blocks, and Multi-Byte Stepping for `from_utf8`

Generates placed instruction fetches for `coreMultiLib.blocks[1]` (`624` B) and lifts block-local
pure `SepWP` segments to arbitrary programs without hooks in that block. Also proves the `sret`
return-block lemmas and the 2-, 3-, and 4-byte UTF-8 sequence validation steps.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches

/-! ## Placed Fetch Generation -/

class CoreFromUtf8Pl where
  mpl : MultiPlacement
  placeable : coreMultiLib.Placeable mpl

abbrev fuMpl [CoreFromUtf8Pl] : MultiPlacement := CoreFromUtf8Pl.mpl

def fuLib1 : PlacedLib := coreMultiLib.blockLib 1
def fuPl1 [CoreFromUtf8Pl] : Placement := coreMultiLib.blockPlacement CoreFromUtf8Pl.mpl 1
theorem fuPlaceable1 [CoreFromUtf8Pl] : fuLib1.Placeable fuPl1 :=
  coreMultiLib.placeable_blockLib (by decide) CoreFromUtf8Pl.placeable
def fuPC1 [CoreFromUtf8Pl] : Program := fuLib1.program fuPl1

def fuProg1 : Program := { code := fuLib1.text.code, symbols := fuLib1.text.symbols }
def fuTree1 : WordTree := word_tree_of% fuProg1
theorem fu1_code_eq : fuLib1.text.code = fuTree1.toBytes := by rfl_kernel
theorem fu1_tree_size : fuTree1.checkSize? = some 156 := by rfl_kernel

section
set_option linter.literalFetch false
gen_placed_fetches fuPC1 fuLib1 fuTree1 fu1_code_eq fu1_tree_size
  via_placement fuPl1 fuPlaceable1 [0x0 → 0x26c]
end

theorem fuBlockNoSvc0_1 : checkBlockNoSvc0 (coreMultiLib.blockLib 1).text = true := by
  decide

/-! ## Block-Local Pure-Segment Lifting -/

private theorem fu_strip_codeLoaded {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hi
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem fu_strip_execOnlyIn (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) :=
  fun _ hpx => of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem fu_steps_start_running {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem fu_steps_rebase_lift_block {P R_j : Program}
    (hext_blk : ∀ off : Nat, off < R_j.code.length →
      P.externAt? (R_j.base + BitVec.ofNat 64 off) = none)
    (hext_R : ∀ pc, R_j.externAt? pc = none)
    (hall : R_j.allInstrs (fun i => !i.isSvc0) = true)
    {s1' sf' : State} (hsteps : Steps R_j s1' sf') (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = ProofLib.stripS (ProofLib.progKeep R_j) s1 → R_j.CodeLoaded s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (ProofLib.progKeep R_j) sf ∧
        Steps P s1 sf ∧ ProofLib.NonSyscallPreserved s1 sf := by
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, hs1, .refl s1, ProofLib.NonSyscallPreserved.refl s1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1
    have hrb' : sb'.status = .Running := fu_steps_start_running hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ => rw [hext_R] at he; cases he
    | extern_fault _ he _ => rw [hext_R] at he; cases he
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      have hL1' : R_j.CodeLoaded (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        fu_strip_codeLoaded hL1
      have hexec' : R_j.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        fu_strip_execOnlyIn R_j s1.mem
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall hL1' hexec' _ inst hfe'
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).pc = s1.pc := by cases s1; rfl
        have hmem_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem =
            ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem := by cases s1; rfl
        rw [hpc_eq, hmem_eq] at hfe'
        unfold Program.fetchMem at hfe' ⊢
        rw [hext_R] at hfe'
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'
        by_cases hal_pc : s1.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'
          split at hfe'
          · contradiction
          · rename_i hce'
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
            have hkeep0 : ProofLib.progKeep R_j s1.pc = true := by
              have hce0 := hce'
              unfold Memory.canExec at hce0
              rw [Memory.allPerm_iff] at hce0
              have hx0 := hce0 0 (by omega)
              have hk := (ProofLib.strip_perm_x_imp hx0).2
              simpa using hk
            have hoff_lt : (s1.pc - R_j.base).toNat < R_j.code.length :=
              of_decide_eq_true hkeep0
            have hpc_off : R_j.base + BitVec.ofNat 64 (s1.pc - R_j.base).toNat = s1.pc := by
              simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
              bv_lin
            have hext_P_pc : P.externAt? s1.pc = none :=
              hpc_off ▸ hext_blk (s1.pc - R_j.base).toNat hoff_lt
            rw [hext_P_pc]
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
              hal_pc, ne_eq, not_true_eq_false]
            have hce : s1.mem.canExec s1.pc 4 = true := by
              unfold Memory.canExec at hce' ⊢
              rw [Memory.allPerm_iff] at hce' ⊢
              intro k hk
              have hxk := hce' k hk
              rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
            have hr32 :
                (ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem).read32 s1.pc =
                  s1.mem.read32 s1.pc := by
              simp [Memory.read32, ProofLib.strip_read8]
            rw [hr32] at hfe'
            simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact hfe'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'
          contradiction
      have hev_R : R_j.evalInst inst (ProofLib.stripS (ProofLib.progKeep R_j) s1) =
          ProofLib.stripS (ProofLib.progKeep R_j) (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      obtain ⟨sf, hsf_eq, hsteps_P, hnsp_rest⟩ :=
        ih hrun_f (execInst inst s1) hev_R (hstep_P.codeLoaded hL1)
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P,
        ProofLib.NonSyscallPreserved.trans
          (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1) hnsp_rest⟩

set_option maxRecDepth 200000 in
/-- Lift a pure `SepWP` execution on `fuPC1.rebase fuPl1.base (fun _ => none)` to any `P : Program`
    with no hooks inside the 624-byte body of `coreMultiLib.blocks[1]`. -/
theorem sepWP_seg_block1_pure [CoreFromUtf8Pl] {P : Program}
    (hext_blk : ∀ off : Nat, off < 624 →
      P.externAt? (fuMpl.base 1 + BitVec.ofNat 64 off) = none)
    {mid target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : coreMultiLib.CodeLoaded fuMpl s.mem)
    (hseg : ∀ s' : State, SameCpuState s' s →
      SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) mid s' Pre (fun sm' Pm =>
        ∀ sm : State, SameCpuState sm sm' → coreMultiLib.CodeLoaded fuMpl sm.mem →
          ProofLib.NonSyscallPreserved s sm → SepWP P target_pc sm Pm post oom)) :
    SepWP P target_pc s Pre post oom := by
  let R_1 : Program := fuPC1.rebase fuPl1.base (fun _ => none)
  let keep := ProofLib.progKeep R_1
  have hR_eq : R_1 = (coreMultiLib.blockProgram fuMpl 1).rebase (fuMpl.base 1) (fun _ => none) := rfl
  have hL_R : R_1.CodeLoaded s.mem := (hcl 1 (by decide)).of_base_code rfl rfl
  have hext_R : ∀ pc, R_1.externAt? pc = none := by
    intro pc; rw [hR_eq]; exact MultiPlacedLib.externAt?_blockProgram_rebase_none _ _ _ _ _
  have hall : R_1.allInstrs (fun i => !i.isSvc0) = true := by
    rw [hR_eq]
    exact blockProgram_rebase_allInstrs_not_isSvc0 coreMultiLib fuMpl 1 fuBlockNoSvc0_1
  have hlen_R : R_1.code.length = 624 := by
    have hc : R_1.code = fuLib1.text.patched fuPl1 := rfl
    rw [hc, Obj.CodeBlock.length_patched, length_text_of_tree fu1_code_eq fu1_tree_size]
  have hext_R_blk : ∀ off : Nat, off < R_1.code.length →
      P.externAt? (R_1.base + BitVec.ofNat 64 off) = none := by
    rw [hlen_R]; exact hext_blk
  refine SepWP.of_reaches_pc fun R hm => ?_
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hm
  have hcpu_in : SameCpuState (ProofLib.stripS keep s) s :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨sm', hsteps', hout'⟩ :=
    SepWP.to_reaches_pc (hseg (ProofLib.stripS keep s) hcpu_in) hm_strip
      (fu_strip_codeLoaded hL_R)
  rcases hout' with ⟨_, hrun_m', Pm, hmm', hcont⟩ | ⟨_, hoom⟩
  · obtain ⟨sm, hsm_eq, hsteps_P, hnsp⟩ :=
      fu_steps_rebase_lift_block hext_R_blk hext_R hall hsteps' hrun_m' s rfl hL_R
    have hcl_m : coreMultiLib.CodeLoaded fuMpl sm.mem :=
      fun k hk => hsteps_P.codeLoaded (hcl k hk)
    have hperm_eq : ∀ a, sm.mem.perm a = s.mem.perm a := fun a => congrFun hnsp.2.1 a
    have hmm'_mem : ProofLib.stripExecOutside keep sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside keep sm.mem := by rw [hsm_eq]; rfl
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hperm_eq hmm'_mem
    have hwp_cont := hcont sm (SameCpuState.of_stripS_left hsm_eq) hcl_m hnsp
    exact fun hL_P => by
      obtain ⟨sf, hsteps2, hout2⟩ := SepWP.to_reaches_pc hwp_cont hmm (hsteps_P.codeLoaded hL_P)
      exact ⟨sf, hsteps_P.trans hsteps2, hout2⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩
    exact False.elim hf

section
arm64_proof_prelude

/-! ## Loop Invariants and Return-Block Lemmas -/

structure FuPreserved (s_entry s : State) : Prop where
  running : s.status = .Running
  sp_eq : s.sp = s_entry.sp
  lr_eq : s.readReg64 .lr = s_entry.readReg64 .lr
  cs : CalleeSavedPreserved s_entry s

theorem FuPreserved.refl {s : State} (hr : s.status = .Running) : FuPreserved s s :=
  ⟨hr, rfl, rfl, CalleeSavedPreserved.rfl s⟩

theorem FuPreserved.step {s0 s1 s2 : State} (h1 : FuPreserved s0 s1)
    (hr2 : s2.status = .Running) (hsp : s2.sp = s1.sp) (hlr : s2.readReg64 .lr = s1.readReg64 .lr)
    (hcs : CalleeSavedPreserved s1 s2) : FuPreserved s0 s2 :=
  ⟨hr2, hsp.trans h1.sp_eq, hlr.trans h1.lr_eq, h1.cs.trans hcs⟩

structure FuLoopRegs (s_entry s : State)
    (p tbl ret : BitVec 64) (len idx : Nat) : Prop where
  pres : FuPreserved s_entry s
  x0_eq : s.readReg64 .x0 = p
  x1_eq : s.readReg64 .x1 = BitVec.ofNat 64 len
  x8_eq : s.readReg64 .x8 = ret
  x9_eq : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 idx
  x10_eq : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 (len - 15)
  x11_eq : s.readReg64 (.gpr 11#5) = utf8AlignOff p
  x12_eq : s.readReg64 (.gpr 12#5) = tbl

theorem FuLoopRegs.preserve {s0 s1 s2 : State}
    {p tbl ret : BitVec 64} {len idx : Nat}
    (h : FuLoopRegs s0 s1 p tbl ret len idx)
    (hr2 : s2.status = .Running) (hsp : s2.sp = s1.sp)
    (hlr : s2.readReg64 .lr = s1.readReg64 .lr)
    (hcs : CalleeSavedPreserved s1 s2)
    (hx0 : s2.readReg64 .x0 = s1.readReg64 .x0)
    (hx1 : s2.readReg64 .x1 = s1.readReg64 .x1)
    (hx8 : s2.readReg64 .x8 = s1.readReg64 .x8)
    (hx9 : s2.readReg64 (.gpr 9#5) = s1.readReg64 (.gpr 9#5))
    (hx10 : s2.readReg64 (.gpr 10#5) = s1.readReg64 (.gpr 10#5))
    (hx11 : s2.readReg64 (.gpr 11#5) = s1.readReg64 (.gpr 11#5))
    (hx12 : s2.readReg64 (.gpr 12#5) = s1.readReg64 (.gpr 12#5)) :
    FuLoopRegs s0 s2 p tbl ret len idx :=
  ⟨h.pres.step hr2 hsp hlr hcs,
   hx0.trans h.x0_eq, hx1.trans h.x1_eq, hx8.trans h.x8_eq,
   hx9.trans h.x9_eq, hx10.trans h.x10_eq, hx11.trans h.x11_eq, hx12.trans h.x12_eq⟩

local macro "fu_step_pres " h:term:max hr:term:max : term =>
  `(FuPreserved.step $h (by simpa [arm64_norm] using $hr) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [CalleeSavedPreserved, calleeSavedVRegs, arm64_norm]))

local macro "fu_keep_regs " h:term:max hr:term:max : term =>
  `(FuLoopRegs.preserve $h (by simpa [arm64_norm] using $hr) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [CalleeSavedPreserved, calleeSavedVRegs, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]))

def fuWorkPre (p tbl ret : BitVec 64) (bs : List (BitVec 8))
    (s0 s8 : BitVec 64) (s16 s17 : BitVec 8) (b18 : BitVec 16) (b20 : BitVec 32) : SepProp :=
  (p ↦ₛ bs) ∗ (tbl ↦ᵣ corePlacedData1) ∗
  (ret ↦₆₄ s0) ∗ ((ret + 8#64) ↦₆₄ s8) ∗
  ((ret + 16#64) ↦₈ s16) ∗ ((ret + 17#64) ↦₈ s17) ∗
  ((ret + 18#64) ↦₁₆ b18) ∗ ((ret + 20#64) ↦₃₂ b20)

def fuPostProp (p tbl ret : BitVec 64) (bs : List (BitVec 8))
    (b18 : BitVec 16) (b20 : BitVec 32) : SepProp :=
  (p ↦ₛ bs) ∗ (tbl ↦ᵣ corePlacedData1) ∗
  fromUtf8SretPost ret p bs.length b18 b20 (runUtf8Validation bs)

abbrev FuPostCont (s_entry : State) (p tbl ret : BitVec 64) (bs : List (BitVec 8))
    (b18 : BitVec 16) (b20 : BitVec 32) (post : State → SepProp → Prop) : Prop :=
  ∀ (sf : State) (Q : SepProp),
    FuPreserved s_entry sf →
    sf.pc = s_entry.readReg64 .lr →
    (Q ⊢ fuPostProp p tbl ret bs b18 b20) →
    post sf Q

theorem fuRetOk [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {post : State → SepProp → Prop}
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hok : runUtf8Validation bs = .ok ())
    (hpc : s.pc = fuPl1.base + 524#64)
    (hpres : FuPreserved s_entry s)
    (hx0 : s.readReg64 .x0 = p)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs.length)
    (hx8 : s.readReg64 .x8 = ret) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running
  have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPre, sret_tail8_merge ret s16 s17 b18 b20]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  refine hpost _ _ (fu_step_pres hpres hrun) rfl ?_
  dsimp only [fuPostProp]
  rw [hok]
  dsimp only [fromUtf8SretPost]
  sep_entail

private theorem fuRetErrNone [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := none })
    (hpc : s.pc = fuPl1.base + 536#64)
    (hpres : FuPreserved s_entry s)
    (hx8 : s.readReg64 .x8 = ret)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running
  have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPre]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  refine hpost _ _ (fu_step_pres hpres hrun) rfl ?_
  dsimp only [fuPostProp]
  rw [herr]
  dsimp only [fromUtf8SretPost, utf8ErrorLenAt]
  have ha17 : (ret + 16#64) + 1#64 = ret + 17#64 := by bv_lin
  rw [ha17]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_right (BitVec.setWidth 8 (s.readReg64 (.gpr 13#5))) ?_
  sep_entail

private theorem fuRetErrSome_1f4 [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 k : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some k })
    (hpc : s.pc = fuPl1.base + 500#64)
    (hpres : FuPreserved s_entry s)
    (hx8 : s.readReg64 .x8 = ret)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 idx)
    (hx14 : BitVec.setWidth 8 (s.readReg64 (.gpr 14#5)) = 1#8)
    (hx13 : BitVec.setWidth 8 (s.readReg64 (.gpr 13#5)) = k) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running
  have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPre]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  refine hpost _ _ (fu_step_pres hpres hrun) rfl ?_
  dsimp only [fuPostProp]
  rw [herr]
  dsimp only [fromUtf8SretPost, utf8ErrorLenAt]
  have ha17 : (ret + 16#64) + 1#64 = ret + 17#64 := by bv_lin
  rw [ha17]
  sep_entail

private theorem fuRetErr2_1ec [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some 2#8 })
    (hpc : s.pc = fuPl1.base + 492#64)
    (hpres : FuPreserved s_entry s)
    (hx8 : s.readReg64 .x8 = ret)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running
  apply rustSepWP_cut (mid := fuPl1.base + 500#64)
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  exact fuRetErrSome_1f4 hpost herr rfl (fu_step_pres hpres hrun)
    (by simp [arm64_norm, hx8]) (by simp [arm64_norm, hx9])
    (by simp [arm64_norm]) (by simp [arm64_norm])

private theorem fuRetErr1_230 [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some 1#8 })
    (hpc : s.pc = fuPl1.base + 560#64)
    (hpres : FuPreserved s_entry s)
    (hx8 : s.readReg64 .x8 = ret)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running
  have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPre]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  refine hpost _ _ (fu_step_pres hpres hrun) rfl ?_
  dsimp only [fuPostProp]
  rw [herr]
  dsimp only [fromUtf8SretPost, utf8ErrorLenAt]
  have ha17 : (ret + 16#64) + 1#64 = ret + 17#64 := by bv_lin
  rw [ha17]
  sep_entail

private theorem fuRetErr3_250 [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some 3#8 })
    (hpc : s.pc = fuPl1.base + 592#64)
    (hpres : FuPreserved s_entry s)
    (hx8 : s.readReg64 .x8 = ret)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hpres.running
  have hlr : s.readReg64 (.gpr 30#5) = s_entry.readReg64 .lr := hpres.lr_eq
  wp_conv_pre => rw [fuWorkPre]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  refine hpost _ _ (fu_step_pres hpres hrun) rfl ?_
  dsimp only [fuPostProp]
  rw [herr]
  dsimp only [fromUtf8SretPost, utf8ErrorLenAt]
  have ha17 : (ret + 16#64) + 1#64 = ret + 17#64 := by bv_lin
  rw [ha17]
  sep_entail

/-! ## Multi-Byte UTF-8 Sequence Validation -/

theorem bv64_ofNat_add_small (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem fu_ule_false {k n : Nat} (hlt : k < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 k) = false := by
  simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  omega

theorem fu_ule_true {n : Nat} :
    (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 n) = true := by
  simp [BitVec.ule]

theorem truncate32_signExtend64 (b : BitVec 8) :
    BitVec.truncate 32 (BitVec.signExtend 64 b) = b.signExtend 32 := by
  revert b; decide

private theorem fu_cmn41_le (b : BitVec 8) :
    ConditionHolds .LE (addsPState32 (b.signExtend 32) 0x41#32) = isUtf8ContByte b := by
  unfold addsPState32; revert b; decide
private theorem fu_cmn41_gt (b : BitVec 8) :
    ConditionHolds .GT (addsPState32 (b.signExtend 32) 0x41#32) = !isUtf8ContByte b := by
  unfold addsPState32; revert b; decide
private theorem fu_cmn40_lt (b : BitVec 8) :
    ConditionHolds .LT (addsPState32 (b.signExtend 32) 0x40#32) = isUtf8ContByte b := by
  unfold addsPState32; revert b; decide
private theorem fu_cmn40_ge (b : BitVec 8) :
    ConditionHolds .GE (addsPState32 (b.signExtend 32) 0x40#32) = !isUtf8ContByte b := by
  unfold addsPState32; revert b; decide
private theorem fu_cmn61_le (b1 : BitVec 8) :
    ConditionHolds .LE (addsPState32 (b1.signExtend 32) 0x61#32) = (0x80#8 ≤ b1 && b1 ≤ 0x9f#8) := by
  unfold addsPState32; revert b1; decide
private theorem fu_cmn71_le (b1 : BitVec 8) :
    ConditionHolds .LE (addsPState32 (b1.signExtend 32) 0x71#32) = (0x80#8 ≤ b1 && b1 ≤ 0x8f#8) := by
  unfold addsPState32; revert b1; decide

abbrev FuNextCont [CoreFromUtf8Pl] (s_entry : State)
    (p tbl ret s0 s8 : BitVec 64) (s16 s17 : BitVec 8) (b18 : BitVec 16) (b20 : BitVec 32)
    (bs : List (BitVec 8)) (idx : Nat) (post : State → SepProp → Prop) : Prop :=
  ∀ (idx' : Nat) (sn : State),
    idx < idx' → idx' ≤ bs.length →
    runUtf8Validation bs = runUtf8ValidationLoop idx' (bs.drop idx') →
    sn.pc = fuPl1.base + 44#64 →
    FuLoopRegs s_entry sn p tbl ret bs.length idx' →
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) sn
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post

private theorem fuWidth2 [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hw2 : (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = true)
    (hpc : s.pc = fuPl1.base + 180#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
  by_cases h1 : idx + 1 < bs.length
  · have hptr1 : p + (BitVec.ofNat 64 idx + 1#64) = p + BitVec.ofNat 64 (idx + 1) := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small]
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = false := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small]
      exact fu_ule_false h1 hlen
    have hse1 := truncate32_signExtend64 (bs.getD (idx + 1) 0#8)
    have hstep := hval.trans (runUtf8ValidationLoop_width2_step h1 hw2)
    cases hc1 : isUtf8ContByte (bs.getD (idx + 1) 0#8)
    · have herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some 1#8 } := by
        simpa only [hc1, Bool.false_eq_true, ↓reduceIte] using hstep
      have hle_c : ConditionHolds .LE
          (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x41#32) = false := by
        rw [fu_cmn41_le]; exact hc1
      apply rustSepWP_cut (mid := fuPl1.base + 560#64)
      wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 1) h1, ← hptr1]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr1, ← pointsToBytes_focus8 p bs (idx + 1) h1, ← fuWorkPre]
      exact fuRetErr1_230 hpost herr rfl (fu_step_pres hregs.pres hrun)
        (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])
    · have hok2 : runUtf8Validation bs = runUtf8ValidationLoop (idx + 2) (bs.drop (idx + 2)) := by
        simpa only [hc1, ↓reduceIte] using hstep
      have hle_c : ConditionHolds .LE
          (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x41#32) = true := by
        rw [fu_cmn41_le]; exact hc1
      apply rustSepWP_cut (mid := fuPl1.base + 44#64)
      wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 1) h1, ← hptr1]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr1, ← pointsToBytes_focus8 p bs (idx + 1) h1, ← fuWorkPre]
      refine hnext (idx + 2) _ (by omega) (by omega) hok2 rfl
        ⟨fu_step_pres hregs.pres hrun,
          by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
          by simp [arm64_norm, hregs.x8_eq], ?_,
          by simp [arm64_norm, hregs.x10_eq], by simp [arm64_norm, hregs.x11_eq],
          by simp [arm64_norm, hregs.x12_eq]⟩
      simpa only [arm64_norm] using bv64_ofNat_add_small idx 2
  · have heof : idx + 1 = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = true := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small, heof]
      exact fu_ule_true
    apply rustSepWP_cut (mid := fuPl1.base + 536#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetErrNone hpost (hval.trans (runUtf8ValidationLoop_width2_eof hidx heof hw2)) rfl
      (fu_step_pres hregs.pres hrun) (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])

private theorem fuWidth3Tail [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx1 : idx + 1 < bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hw3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = true)
    (hok2 : utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) = true)
    (hpc : s.pc = fuPl1.base + 468#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running; have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq; have hx9 := hregs.x9_eq
  by_cases h2 : idx + 2 < bs.length
  · have hptr2 : p + (BitVec.ofNat 64 idx + 2#64) = p + BitVec.ofNat 64 (idx + 2) := by
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv64_ofNat_add_small]
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 2#64) = false := by
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv64_ofNat_add_small]
      exact fu_ule_false h2 hlen
    have hse2 := truncate32_signExtend64 (bs.getD (idx + 2) 0#8)
    have hstep := hval.trans (runUtf8ValidationLoop_width3_step h2 hw3 hok2)
    cases hc2 : isUtf8ContByte (bs.getD (idx + 2) 0#8)
    · have herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some 2#8 } := by
        simpa only [hc2, Bool.false_eq_true, ↓reduceIte] using hstep
      have hle_c : ConditionHolds .LE
          (addsPState32 ((bs.getD (idx + 2) 0#8).signExtend 32) 0x41#32) = false := by
        rw [fu_cmn41_le]; exact hc2
      apply rustSepWP_cut (mid := fuPl1.base + 492#64)
      wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 2) h2, ← hptr2]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr2, ← pointsToBytes_focus8 p bs (idx + 2) h2, ← fuWorkPre]
      exact fuRetErr2_1ec hpost herr rfl (fu_step_pres hregs.pres hrun)
        (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])
    · have hok3 : runUtf8Validation bs = runUtf8ValidationLoop (idx + 3) (bs.drop (idx + 3)) := by
        simpa only [hc2, ↓reduceIte] using hstep
      have hle_c : ConditionHolds .LE
          (addsPState32 ((bs.getD (idx + 2) 0#8).signExtend 32) 0x41#32) = true := by
        rw [fu_cmn41_le]; exact hc2
      apply rustSepWP_cut (mid := fuPl1.base + 44#64)
      wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 2) h2, ← hptr2]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr2, ← pointsToBytes_focus8 p bs (idx + 2) h2, ← fuWorkPre]
      refine hnext (idx + 3) _ (by omega) (by omega) hok3 rfl
        ⟨fu_step_pres hregs.pres hrun,
          by simp [arm64_norm, hx0], by simp [arm64_norm, hx1],
          by simp [arm64_norm, hregs.x8_eq], ?_,
          by simp [arm64_norm, hregs.x10_eq], by simp [arm64_norm, hregs.x11_eq],
          by simp [arm64_norm, hregs.x12_eq]⟩
      simpa only [arm64_norm] using bv64_ofNat_add_small idx 3
  · have heof2 : idx + 2 = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 2#64) = true := by
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv64_ofNat_add_small, heof2]
      exact fu_ule_true
    apply rustSepWP_cut (mid := fuPl1.base + 536#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetErrNone hpost (hval.trans (runUtf8ValidationLoop_width3_eof2 hidx1 heof2 hw3 hok2)) rfl
      (fu_step_pres hregs.pres hrun) (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])

private theorem fu_byte32_beq (b : BitVec 8) (k : BitVec 32) (hk : k.toNat < 256) :
    (BitVec.setWidth 32 b == k) = (b == BitVec.setWidth 8 k) :=
  utf8CharWidth_zeroExtend32_eq b k hk

private theorem fu_byte32_bne (b : BitVec 8) (k : BitVec 32) (hk : k.toNat < 256) :
    (BitVec.setWidth 32 b != k) = !(b == BitVec.ofNat 8 k.toNat) := by
  unfold bne
  rw [utf8CharWidth_zeroExtend32_eq b k hk]; rfl

private theorem fu_e0_mask_eq (b1 : BitVec 8) :
    ((BitVec.setWidth 32 b1 &&& 0xe0#32) == 0xa0#32) = (0xa0#8 ≤ b1 && b1 ≤ 0xbf#8) := by
  revert b1; decide

private theorem fu_f0_sub_ult (b1 : BitVec 8) :
    BitVec.ult (BitVec.setWidth 32 b1 - 0x90#32) 0x30#32 = (0x90#8 ≤ b1 && b1 ≤ 0xbf#8) := by
  revert b1; decide

private theorem fu_e_ee_ef_ne_false (b0 : BitVec 8)
    (hw3 : (0xe0#8 ≤ b0 && b0 ≤ 0xef#8) = true)
    (hne0 : (b0 == 0xe0#8) = false) (hned : (b0 == 0xed#8) = false)
    (hcs : BitVec.ule 0x0c#32 (BitVec.setWidth 32 b0 - 0xe1#32) = true) :
    ((BitVec.setWidth 32 b0 &&& 0xfe#32) != 0xee#32) = false := by
  revert b0; decide

private theorem fu_f_f1_f3_hi_false (b0 : BitVec 8)
    (hw4 : (0xf0#8 ≤ b0 && b0 ≤ 0xf4#8) = true)
    (hne0 : (b0 == 0xf0#8) = false) (hne4 : (b0 == 0xf4#8) = false) :
    BitVec.ult 0x02#32 (BitVec.setWidth 32 b0 - 0xf1#32) = false := by
  revert b0; decide

private theorem fu_multibyte_and64 (b0 : BitVec 8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.signExtend 64 b0)) &&& 255#64 =
      BitVec.ofNat 64 b0.toNat := by
  have h1 : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.signExtend 64 b0)) &&& 255#64 =
      b0.zeroExtend 64 := by revert b0; decide
  rw [h1, (signExtend32_and_ff64 b0).2]

private theorem fuWidth3 [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hw3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = true)
    (hpc : s.pc = fuPl1.base + 208#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx)
    (hx13 : BitVec.truncate 32 (s.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8)) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running
  have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq
  have hx9 := hregs.x9_eq
  by_cases h1 : idx + 1 < bs.length
  · have hptr1 : p + (BitVec.ofNat 64 idx + 1#64) = p + BitVec.ofNat 64 (idx + 1) := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small]
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = false := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small]
      exact fu_ule_false h1 hlen
    have hcut_e0 : ∀ sm : State,
        sm.pc = fuPl1.base + 224#64 →
        FuLoopRegs s_entry sm p tbl ret bs.length idx →
        BitVec.truncate 32 (sm.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8) →
        sm.readReg64 (.gpr 14#5) = (bs.getD (idx + 1) 0#8).zeroExtend 64 →
        SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) sm
          (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
      intro sm hpc_m hregs_m hx13_m hx14_m
      have hrun_m := hregs_m.pres.running
      cases hb0_e0 : (bs.getD idx 0#8 == 0xe0#8)
      · have heq_e0 : (BitVec.setWidth 32 (bs.getD idx 0#8) == 0xe0#32) = false := by
          rw [fu_byte32_beq _ 0xe0#32 (by decide)]; exact hb0_e0
        have hcut_ec : ∀ sn : State,
            sn.pc = fuPl1.base + 236#64 →
            FuLoopRegs s_entry sn p tbl ret bs.length idx →
            BitVec.truncate 32 (sn.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8) →
            BitVec.truncate 32 (sn.readReg64 (.gpr 14#5)) = (bs.getD (idx + 1) 0#8).signExtend 32 →
            SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) sn
              (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
          intro sn hpc_n hregs_n hx13_n hx14_n
          have hrun_n := hregs_n.pres.running
          cases hb0_ed : (bs.getD idx 0#8 == 0xed#8)
          · have hne_ed : (BitVec.setWidth 32 (bs.getD idx 0#8) != 0xed#32) = true := by
              rw [fu_byte32_bne _ 0xed#32 (by decide),
                  show BitVec.ofNat 8 (0xed#32).toNat = 0xed#8 from rfl, hb0_ed]
              rfl
            have hok2_eq : utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) =
                isUtf8ContByte (bs.getD (idx + 1) 0#8) := by
              simp only [utf8Width3Ok2, hb0_e0, hb0_ed, Bool.false_eq_true, ↓reduceIte]
            cases hcs_e1 : BitVec.ule 0x0c#32 (BitVec.setWidth 32 (bs.getD idx 0#8) - 0xe1#32)
            · cases hc1 : isUtf8ContByte (bs.getD (idx + 1) 0#8)
              · have hlt_c : ConditionHolds .LT
                    (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = false := by
                  rw [fu_cmn40_lt]; exact hc1
                have herr := hval.trans (runUtf8ValidationLoop_width3_err1 h1 hw3 (hok2_eq.trans hc1))
                apply rustSepWP_cut (mid := fuPl1.base + 560#64)
                wp_sym_steps
                refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
                exact fuRetErr1_230 hpost herr rfl (fu_step_pres hregs_n.pres hrun_n)
                  (by simp [arm64_norm, hregs_n.x8_eq]) (by simp [arm64_norm, hregs_n.x9_eq])
              · have hlt_c : ConditionHolds .LT
                    (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = true := by
                  rw [fu_cmn40_lt]; exact hc1
                apply rustSepWP_cut (mid := fuPl1.base + 468#64)
                wp_sym_steps
                refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
                exact fuWidth3Tail hlen hpost hnext h1 hval hw3 (hok2_eq.trans hc1) rfl
                  (fu_keep_regs hregs_n hrun_n)
            · have hne_ee := fu_e_ee_ef_ne_false (bs.getD idx 0#8) hw3 hb0_e0 hb0_ed hcs_e1
              cases hc1 : isUtf8ContByte (bs.getD (idx + 1) 0#8)
              · have hge_c : ConditionHolds .GE
                    (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = true := by
                  rw [fu_cmn40_ge, hc1]; rfl
                have herr := hval.trans (runUtf8ValidationLoop_width3_err1 h1 hw3 (hok2_eq.trans hc1))
                apply rustSepWP_cut (mid := fuPl1.base + 500#64)
                wp_sym_steps
                refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
                exact fuRetErrSome_1f4 hpost herr rfl (fu_step_pres hregs_n.pres hrun_n)
                  (by simp [arm64_norm, hregs_n.x8_eq]) (by simp [arm64_norm, hregs_n.x9_eq])
                  (by simp [arm64_norm]) (by simp [arm64_norm])
              · have hge_c : ConditionHolds .GE
                    (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = false := by
                  rw [fu_cmn40_ge, hc1]; rfl
                apply rustSepWP_cut (mid := fuPl1.base + 468#64)
                wp_sym_steps
                refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
                exact fuWidth3Tail hlen hpost hnext h1 hval hw3 (hok2_eq.trans hc1) rfl
                  (fu_keep_regs hregs_n hrun_n)
          · have hne_ed : (BitVec.setWidth 32 (bs.getD idx 0#8) != 0xed#32) = false := by
              rw [fu_byte32_bne _ 0xed#32 (by decide),
                  show BitVec.ofNat 8 (0xed#32).toNat = 0xed#8 from rfl, hb0_ed]
              rfl
            have hok2_eq : utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) =
                (0x80#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0x9f#8) := by
              simp only [utf8Width3Ok2, hb0_e0, hb0_ed, Bool.false_eq_true, ↓reduceIte]
            cases hed_ok : (0x80#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0x9f#8)
            · have hle_c : ConditionHolds .LE
                  (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x61#32) = false := by
                rw [fu_cmn61_le]; exact hed_ok
              have herr := hval.trans (runUtf8ValidationLoop_width3_err1 h1 hw3 (hok2_eq.trans hed_ok))
              apply rustSepWP_cut (mid := fuPl1.base + 560#64)
              wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact fuRetErr1_230 hpost herr rfl (fu_step_pres hregs_n.pres hrun_n)
                (by simp [arm64_norm, hregs_n.x8_eq]) (by simp [arm64_norm, hregs_n.x9_eq])
            · have hle_c : ConditionHolds .LE
                  (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x61#32) = true := by
                rw [fu_cmn61_le]; exact hed_ok
              apply rustSepWP_cut (mid := fuPl1.base + 468#64)
              wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact fuWidth3Tail hlen hpost hnext h1 hval hw3 (hok2_eq.trans hed_ok) rfl
                (fu_keep_regs hregs_n hrun_n)
        apply rustSepWP_cut (mid := fuPl1.base + 236#64)
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
        refine hcut_ec _ rfl (fu_keep_regs hregs_m hrun_m)
          (by simpa only [arm64_norm] using hx13_m) ?_
        simp only [arm64_norm]
        generalize bs.getD (idx + 1) 0#8 = b1; revert b1; decide
      · have heq_e0 : (BitVec.setWidth 32 (bs.getD idx 0#8) == 0xe0#32) = true := by
          rw [fu_byte32_beq _ 0xe0#32 (by decide)]; exact hb0_e0
        have hok2_eq : utf8Width3Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) =
            (0xa0#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0xbf#8) := by
          simp only [utf8Width3Ok2, hb0_e0, ↓reduceIte]
        cases he0_ok : (0xa0#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0xbf#8)
        · have hm_eq : ((BitVec.setWidth 32 (bs.getD (idx + 1) 0#8) &&& 0xe0#32) == 0xa0#32) = false := by
            rw [fu_e0_mask_eq]; exact he0_ok
          have herr := hval.trans (runUtf8ValidationLoop_width3_err1 h1 hw3 (hok2_eq.trans he0_ok))
          apply rustSepWP_cut (mid := fuPl1.base + 560#64)
          wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact fuRetErr1_230 hpost herr rfl (fu_step_pres hregs_m.pres hrun_m)
            (by simp [arm64_norm, hregs_m.x8_eq]) (by simp [arm64_norm, hregs_m.x9_eq])
        · have hm_eq : ((BitVec.setWidth 32 (bs.getD (idx + 1) 0#8) &&& 0xe0#32) == 0xa0#32) = true := by
            rw [fu_e0_mask_eq]; exact he0_ok
          apply rustSepWP_cut (mid := fuPl1.base + 468#64)
          wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact fuWidth3Tail hlen hpost hnext h1 hval hw3 (hok2_eq.trans he0_ok) rfl
            (fu_keep_regs hregs_m hrun_m)
    apply rustSepWP_cut (mid := fuPl1.base + 224#64)
    wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 1) h1, ← hptr1]
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    wp_conv_pre => rw [hptr1, ← pointsToBytes_focus8 p bs (idx + 1) h1, ← fuWorkPre]
    exact hcut_e0 _ rfl (fu_keep_regs hregs hrun)
      (by simpa only [arm64_norm] using hx13) (by simp [arm64_norm])
  · have heof : idx + 1 = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = true := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small, heof]
      exact fu_ule_true
    apply rustSepWP_cut (mid := fuPl1.base + 536#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetErrNone hpost (hval.trans (runUtf8ValidationLoop_width3_eof1 hidx heof hw3)) rfl
      (fu_step_pres hregs.pres hrun) (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])

private theorem fuWidth4Tail [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx1 : idx + 1 < bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hw4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = true)
    (hok2 : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) = true)
    (hpc : s.pc = fuPl1.base + 388#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running
  have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq
  have hx9 := hregs.x9_eq
  by_cases h2 : idx + 2 < bs.length
  · have hptr2 : p + (BitVec.ofNat 64 idx + 2#64) = p + BitVec.ofNat 64 (idx + 2) := by
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv64_ofNat_add_small]
    have hcs2 : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 2#64) = false := by
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv64_ofNat_add_small]
      exact fu_ule_false h2 hlen
    have hse2 := truncate32_signExtend64 (bs.getD (idx + 2) 0#8)
    cases hc2 : isUtf8ContByte (bs.getD (idx + 2) 0#8)
    · have hgt_c : ConditionHolds .GT
          (addsPState32 ((bs.getD (idx + 2) 0#8).signExtend 32) 0x41#32) = true := by
        rw [fu_cmn41_gt, hc2]; rfl
      have herr := hval.trans (runUtf8ValidationLoop_width4_err2 h2 hw4 hok2 hc2)
      apply rustSepWP_cut (mid := fuPl1.base + 492#64)
      wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 2) h2, ← hptr2]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr2, ← pointsToBytes_focus8 p bs (idx + 2) h2, ← fuWorkPre]
      exact fuRetErr2_1ec hpost herr rfl (fu_step_pres hregs.pres hrun)
        (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])
    · have hgt_c : ConditionHolds .GT
          (addsPState32 ((bs.getD (idx + 2) 0#8).signExtend 32) 0x41#32) = false := by
        rw [fu_cmn41_gt, hc2]; rfl
      have hcut_19c : ∀ sm : State,
          sm.pc = fuPl1.base + 412#64 →
          FuLoopRegs s_entry sm p tbl ret bs.length idx →
          SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) sm
            (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
        intro sm hpc_m hregs_m
        have hrun_m := hregs_m.pres.running
        have hx0_m := hregs_m.x0_eq
        have hx1_m := hregs_m.x1_eq
        have hx9_m := hregs_m.x9_eq
        by_cases h3 : idx + 3 < bs.length
        · have hptr3 : p + (BitVec.ofNat 64 idx + 3#64) = p + BitVec.ofNat 64 (idx + 3) := by
            rw [show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, bv64_ofNat_add_small]
          have hcs3 : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 3#64) = false := by
            rw [show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, bv64_ofNat_add_small]
            exact fu_ule_false h3 hlen
          have hse3 := truncate32_signExtend64 (bs.getD (idx + 3) 0#8)
          have hstep := hval.trans (runUtf8ValidationLoop_width4_step h3 hw4 hok2 hc2)
          cases hc3 : isUtf8ContByte (bs.getD (idx + 3) 0#8)
          · have herr : runUtf8Validation bs = .error { valid_up_to := idx, error_len := some 3#8 } := by
              simpa only [hc3, Bool.false_eq_true, ↓reduceIte] using hstep
            have hlt_c : ConditionHolds .LT
                (addsPState32 ((bs.getD (idx + 3) 0#8).signExtend 32) 0x40#32) = false := by
              rw [fu_cmn40_lt]; exact hc3
            apply rustSepWP_cut (mid := fuPl1.base + 592#64)
            wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 3) h3, ← hptr3]
            wp_sym_steps
            refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
            wp_conv_pre => rw [hptr3, ← pointsToBytes_focus8 p bs (idx + 3) h3, ← fuWorkPre]
            exact fuRetErr3_250 hpost herr rfl (fu_step_pres hregs_m.pres hrun_m)
              (by simp [arm64_norm, hregs_m.x8_eq]) (by simp [arm64_norm, hx9_m])
          · have hok4 : runUtf8Validation bs = runUtf8ValidationLoop (idx + 4) (bs.drop (idx + 4)) := by
              simpa only [hc3, ↓reduceIte] using hstep
            have hlt_c : ConditionHolds .LT
                (addsPState32 ((bs.getD (idx + 3) 0#8).signExtend 32) 0x40#32) = true := by
              rw [fu_cmn40_lt]; exact hc3
            apply rustSepWP_cut (mid := fuPl1.base + 44#64)
            wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 3) h3, ← hptr3]
            wp_sym_steps
            refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
            wp_conv_pre => rw [hptr3, ← pointsToBytes_focus8 p bs (idx + 3) h3, ← fuWorkPre]
            refine hnext (idx + 4) _ (by omega) (by omega) hok4 rfl
              ⟨fu_step_pres hregs_m.pres hrun_m,
                by simp [arm64_norm, hx0_m], by simp [arm64_norm, hx1_m],
                by simp [arm64_norm, hregs_m.x8_eq], ?_,
                by simp [arm64_norm, hregs_m.x10_eq], by simp [arm64_norm, hregs_m.x11_eq],
                by simp [arm64_norm, hregs_m.x12_eq]⟩
            simpa only [arm64_norm] using bv64_ofNat_add_small idx 4
        · have heof3 : idx + 3 = bs.length := by omega
          have hcs3 : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 3#64) = true := by
            rw [show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, bv64_ofNat_add_small, heof3]
            exact fu_ule_true
          apply rustSepWP_cut (mid := fuPl1.base + 536#64)
          wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact fuRetErrNone hpost (hval.trans (runUtf8ValidationLoop_width4_eof3 h2 heof3 hw4 hok2 hc2)) rfl
            (fu_step_pres hregs_m.pres hrun_m) (by simp [arm64_norm, hregs_m.x8_eq])
            (by simp [arm64_norm, hx9_m])
      apply rustSepWP_cut (mid := fuPl1.base + 412#64)
      wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 2) h2, ← hptr2]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr2, ← pointsToBytes_focus8 p bs (idx + 2) h2, ← fuWorkPre]
      exact hcut_19c _ rfl (fu_keep_regs hregs hrun)
  · have heof2 : idx + 2 = bs.length := by omega
    have hcs2 : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 2#64) = true := by
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bv64_ofNat_add_small, heof2]
      exact fu_ule_true
    apply rustSepWP_cut (mid := fuPl1.base + 536#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetErrNone hpost (hval.trans (runUtf8ValidationLoop_width4_eof2 hidx1 heof2 hw4 hok2)) rfl
      (fu_step_pres hregs.pres hrun) (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])

private theorem fuWidth4 [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hw4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = true)
    (hpc : s.pc = fuPl1.base + 256#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx)
    (hx13 : BitVec.truncate 32 (s.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8)) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running
  have hx0 := hregs.x0_eq
  have hx1 := hregs.x1_eq
  have hx9 := hregs.x9_eq
  by_cases h1 : idx + 1 < bs.length
  · have hptr1 : p + (BitVec.ofNat 64 idx + 1#64) = p + BitVec.ofNat 64 (idx + 1) := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small]
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = false := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small]
      exact fu_ule_false h1 hlen
    have hcut_110 : ∀ sm : State,
        sm.pc = fuPl1.base + 272#64 →
        FuLoopRegs s_entry sm p tbl ret bs.length idx →
        BitVec.truncate 32 (sm.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8) →
        sm.readReg64 (.gpr 14#5) = (bs.getD (idx + 1) 0#8).zeroExtend 64 →
        SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) sm
          (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
      intro sm hpc_m hregs_m hx13_m hx14_m
      have hrun_m := hregs_m.pres.running
      cases hb0_f0 : (bs.getD idx 0#8 == 0xf0#8)
      · have heq_f0 : (BitVec.setWidth 32 (bs.getD idx 0#8) == 0xf0#32) = false := by
          rw [fu_byte32_beq _ 0xf0#32 (by decide)]; exact hb0_f0
        have hcut_11c : ∀ sn : State,
            sn.pc = fuPl1.base + 284#64 →
            FuLoopRegs s_entry sn p tbl ret bs.length idx →
            BitVec.truncate 32 (sn.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8) →
            BitVec.truncate 32 (sn.readReg64 (.gpr 14#5)) = (bs.getD (idx + 1) 0#8).signExtend 32 →
            SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) sn
              (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
          intro sn hpc_n hregs_n hx13_n hx14_n
          have hrun_n := hregs_n.pres.running
          cases hb0_f4 : (bs.getD idx 0#8 == 0xf4#8)
          · have hne_f4 : (BitVec.setWidth 32 (bs.getD idx 0#8) != 0xf4#32) = true := by
              rw [fu_byte32_bne _ 0xf4#32 (by decide),
                  show BitVec.ofNat 8 (0xf4#32).toNat = 0xf4#8 from rfl, hb0_f4]
              rfl
            have hhi_false := fu_f_f1_f3_hi_false (bs.getD idx 0#8) hw4 hb0_f0 hb0_f4
            have hok2_eq : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) =
                isUtf8ContByte (bs.getD (idx + 1) 0#8) := by
              simp only [utf8Width4Ok2, hb0_f0, hb0_f4, Bool.false_eq_true, ↓reduceIte]
            cases hc1 : isUtf8ContByte (bs.getD (idx + 1) 0#8)
            · have hge_c : ConditionHolds .GE
                  (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = true := by
                rw [fu_cmn40_ge, hc1]; rfl
              have herr := hval.trans (runUtf8ValidationLoop_width4_err1 h1 hw4 (hok2_eq.trans hc1))
              apply rustSepWP_cut (mid := fuPl1.base + 500#64)
              wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact fuRetErrSome_1f4 hpost herr rfl (fu_step_pres hregs_n.pres hrun_n)
                (by simp [arm64_norm, hregs_n.x8_eq]) (by simp [arm64_norm, hregs_n.x9_eq])
                (by simp [arm64_norm]) (by simp [arm64_norm])
            · have hge_c : ConditionHolds .GE
                  (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x40#32) = false := by
                rw [fu_cmn40_ge, hc1]; rfl
              apply rustSepWP_cut (mid := fuPl1.base + 388#64)
              wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact fuWidth4Tail hlen hpost hnext h1 hval hw4 (hok2_eq.trans hc1) rfl
                (fu_keep_regs hregs_n hrun_n)
          · have hne_f4 : (BitVec.setWidth 32 (bs.getD idx 0#8) != 0xf4#32) = false := by
              rw [fu_byte32_bne _ 0xf4#32 (by decide),
                  show BitVec.ofNat 8 (0xf4#32).toNat = 0xf4#8 from rfl, hb0_f4]
              rfl
            have hok2_eq : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) =
                (0x80#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0x8f#8) := by
              simp only [utf8Width4Ok2, hb0_f0, hb0_f4, Bool.false_eq_true, ↓reduceIte]
            cases hf4_ok : (0x80#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0x8f#8)
            · have hle_c : ConditionHolds .LE
                  (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x71#32) = false := by
                rw [fu_cmn71_le]; exact hf4_ok
              have herr := hval.trans (runUtf8ValidationLoop_width4_err1 h1 hw4 (hok2_eq.trans hf4_ok))
              apply rustSepWP_cut (mid := fuPl1.base + 560#64)
              wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact fuRetErr1_230 hpost herr rfl (fu_step_pres hregs_n.pres hrun_n)
                (by simp [arm64_norm, hregs_n.x8_eq]) (by simp [arm64_norm, hregs_n.x9_eq])
            · have hle_c : ConditionHolds .LE
                  (addsPState32 ((bs.getD (idx + 1) 0#8).signExtend 32) 0x71#32) = true := by
                rw [fu_cmn71_le]; exact hf4_ok
              apply rustSepWP_cut (mid := fuPl1.base + 388#64)
              wp_sym_steps
              refine SepWP.done rfl (by simpa [arm64_norm] using hrun_n) ?_
              exact fuWidth4Tail hlen hpost hnext h1 hval hw4 (hok2_eq.trans hf4_ok) rfl
                (fu_keep_regs hregs_n hrun_n)
        apply rustSepWP_cut (mid := fuPl1.base + 284#64)
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
        refine hcut_11c _ rfl (fu_keep_regs hregs_m hrun_m)
          (by simpa only [arm64_norm] using hx13_m) ?_
        simp only [arm64_norm]
        generalize bs.getD (idx + 1) 0#8 = b1; revert b1; decide
      · have heq_f0 : (BitVec.setWidth 32 (bs.getD idx 0#8) == 0xf0#32) = true := by
          rw [fu_byte32_beq _ 0xf0#32 (by decide)]; exact hb0_f0
        have hok2_eq : utf8Width4Ok2 (bs.getD idx 0#8) (bs.getD (idx + 1) 0#8) =
            (0x90#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0xbf#8) := by
          simp only [utf8Width4Ok2, hb0_f0, ↓reduceIte]
        cases hf0_ok : (0x90#8 ≤ bs.getD (idx + 1) 0#8 && bs.getD (idx + 1) 0#8 ≤ 0xbf#8)
        · have hcc : BitVec.ult (BitVec.setWidth 32 (bs.getD (idx + 1) 0#8) - 0x90#32) 0x30#32 = false := by
            rw [fu_f0_sub_ult]; exact hf0_ok
          have herr := hval.trans (runUtf8ValidationLoop_width4_err1 h1 hw4 (hok2_eq.trans hf0_ok))
          apply rustSepWP_cut (mid := fuPl1.base + 560#64)
          wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact fuRetErr1_230 hpost herr rfl (fu_step_pres hregs_m.pres hrun_m)
            (by simp [arm64_norm, hregs_m.x8_eq]) (by simp [arm64_norm, hregs_m.x9_eq])
        · have hcc : BitVec.ult (BitVec.setWidth 32 (bs.getD (idx + 1) 0#8) - 0x90#32) 0x30#32 = true := by
            rw [fu_f0_sub_ult]; exact hf0_ok
          apply rustSepWP_cut (mid := fuPl1.base + 388#64)
          wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact fuWidth4Tail hlen hpost hnext h1 hval hw4 (hok2_eq.trans hf0_ok) rfl
            (fu_keep_regs hregs_m hrun_m)
    apply rustSepWP_cut (mid := fuPl1.base + 272#64)
    wp_conv_pre => rw [fuWorkPre, pointsToBytes_focus8 p bs (idx + 1) h1, ← hptr1]
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    wp_conv_pre => rw [hptr1, ← pointsToBytes_focus8 p bs (idx + 1) h1, ← fuWorkPre]
    exact hcut_110 _ rfl (fu_keep_regs hregs hrun)
      (by simpa only [arm64_norm] using hx13) (by simp [arm64_norm])
  · have heof : idx + 1 = bs.length := by omega
    have hcs : (BitVec.ofNat 64 bs.length).ule (BitVec.ofNat 64 idx + 1#64) = true := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_ofNat_add_small, heof]
      exact fu_ule_true
    apply rustSepWP_cut (mid := fuPl1.base + 536#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact fuRetErrNone hpost (hval.trans (runUtf8ValidationLoop_width4_eof1 hidx heof hw4)) rfl
      (fu_step_pres hregs.pres hrun) (by simp [arm64_norm, hregs.x8_eq]) (by simp [arm64_norm, hx9])

theorem fuMultiByte [CoreFromUtf8Pl] {s_entry s : State}
    {p tbl ret s0 s8 : BitVec 64} {s16 s17 : BitVec 8} {b18 : BitVec 16} {b20 : BitVec 32}
    {bs : List (BitVec 8)} {idx : Nat} {post : State → SepProp → Prop}
    (hlen : bs.length < 2 ^ 64)
    (hpost : FuPostCont s_entry p tbl ret bs b18 b20 post)
    (hnext : FuNextCont s_entry p tbl ret s0 s8 s16 s17 b18 b20 bs idx post)
    (hidx : idx < bs.length)
    (hval : runUtf8Validation bs = runUtf8ValidationLoop idx (bs.drop idx))
    (hnonAscii : ¬ (bs.getD idx 0#8 < 0x80#8))
    (hpc : s.pc = fuPl1.base + 144#64)
    (hregs : FuLoopRegs s_entry s p tbl ret bs.length idx)
    (hx13 : s.readReg64 (.gpr 13#5) =
      BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 (bs.getD idx 0#8)))) :
    SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) s
      (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
  have hrun := hregs.pres.running
  have hx12 := hregs.x12_eq
  have hb0_lt : (bs.getD idx 0#8).toNat < corePlacedData1.length := by
    rw [corePlacedData1_length]; exact (bs.getD idx 0#8).isLt
  have hand64 := fu_multibyte_and64 (bs.getD idx 0#8)
  have hcut_9c : ∀ sm : State,
      sm.pc = fuPl1.base + 156#64 →
      FuLoopRegs s_entry sm p tbl ret bs.length idx →
      BitVec.truncate 32 (sm.readReg64 (.gpr 13#5)) = BitVec.setWidth 32 (bs.getD idx 0#8) →
      sm.readReg64 (.gpr 14#5) = (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8).zeroExtend 64 →
      SepWP (fuPC1.rebase fuPl1.base (fun _ => none)) (s_entry.readReg64 .lr) sm
        (fuWorkPre p tbl ret bs s0 s8 s16 s17 b18 b20) post := by
    intro sm hpc_m hregs_m hx13_m hx14_m
    have hrun_m := hregs_m.pres.running
    cases hw4_eq : (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8 == 4#8)
    · have hc4 : (BitVec.setWidth 32 (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8) == 4#32) = false := by
        rw [fu_byte32_beq _ 4#32 (by decide)]; exact hw4_eq
      cases hw3_eq : (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8 == 3#8)
      · have hc3 : (BitVec.setWidth 32 (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8) == 3#32) = false := by
          rw [fu_byte32_beq _ 3#32 (by decide)]; exact hw3_eq
        cases hw2_eq : (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8 == 2#8)
        · have hc2 : (BitVec.setWidth 32 (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8) != 2#32) = true := by
            rw [fu_byte32_bne _ 2#32 (by decide),
                show BitVec.ofNat 8 (2#32).toNat = 2#8 from rfl, hw2_eq]
            rfl
          have hnot4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = false := by
            cases h : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8)
            · rfl
            · exact False.elim (Bool.noConfusion
                (hw4_eq.symm.trans (beq_iff_eq.mpr ((utf8CharWidth_eq_4_iff _).mpr h))))
          have hnot3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = false := by
            cases h : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8)
            · rfl
            · exact False.elim (Bool.noConfusion
                (hw3_eq.symm.trans (beq_iff_eq.mpr ((utf8CharWidth_eq_3_iff _).mpr h))))
          have hnot2 : (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = false := by
            cases h : (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8)
            · rfl
            · exact False.elim (Bool.noConfusion
                (hw2_eq.symm.trans (beq_iff_eq.mpr ((utf8CharWidth_eq_2_iff _).mpr h))))
          have herr := hval.trans (runUtf8ValidationLoop_err_lead hidx hnonAscii hnot2 hnot3 hnot4)
          apply rustSepWP_cut (mid := fuPl1.base + 560#64)
          wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact fuRetErr1_230 hpost herr rfl (fu_step_pres hregs_m.pres hrun_m)
            (by simp [arm64_norm, hregs_m.x8_eq]) (by simp [arm64_norm, hregs_m.x9_eq])
        · have hc2 : (BitVec.setWidth 32 (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8) != 2#32) = false := by
            rw [fu_byte32_bne _ 2#32 (by decide),
                show BitVec.ofNat 8 (2#32).toNat = 2#8 from rfl, hw2_eq]
            rfl
          have hw2 : (0xc2#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xdf#8) = true :=
            (utf8CharWidth_eq_2_iff _).mp (beq_iff_eq.mp hw2_eq)
          apply rustSepWP_cut (mid := fuPl1.base + 180#64)
          wp_sym_steps
          refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
          exact fuWidth2 hlen hpost hnext hidx hval hw2 rfl (fu_keep_regs hregs_m hrun_m)
      · have hc3 : (BitVec.setWidth 32 (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8) == 3#32) = true := by
          rw [fu_byte32_beq _ 3#32 (by decide)]; exact hw3_eq
        have hw3 : (0xe0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xef#8) = true :=
          (utf8CharWidth_eq_3_iff _).mp (beq_iff_eq.mp hw3_eq)
        apply rustSepWP_cut (mid := fuPl1.base + 208#64)
        wp_sym_steps
        refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
        exact fuWidth3 hlen hpost hnext hidx hval hw3 rfl (fu_keep_regs hregs_m hrun_m)
          (by simpa only [arm64_norm] using hx13_m)
    · have hc4 : (BitVec.setWidth 32 (corePlacedData1.getD (bs.getD idx 0#8).toNat 0#8) == 4#32) = true := by
        rw [fu_byte32_beq _ 4#32 (by decide)]; exact hw4_eq
      have hw4 : (0xf0#8 ≤ bs.getD idx 0#8 && bs.getD idx 0#8 ≤ 0xf4#8) = true :=
        (utf8CharWidth_eq_4_iff _).mp (beq_iff_eq.mp hw4_eq)
      apply rustSepWP_cut (mid := fuPl1.base + 256#64)
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun_m) ?_
      exact fuWidth4 hlen hpost hnext hidx hval hw4 rfl (fu_keep_regs hregs_m hrun_m)
        (by simpa only [arm64_norm] using hx13_m)
  apply rustSepWP_cut (mid := fuPl1.base + 156#64)
  wp_conv_pre =>
    rw [fuWorkPre, ← sepConj_assoc, sepConj_comm (p ↦ₛ bs) (tbl ↦ᵣ corePlacedData1),
        pointsToBytesRO_focus8 tbl corePlacedData1 (bs.getD idx 0#8).toNat hb0_lt]
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  wp_conv_pre =>
    rw [← pointsToBytesRO_focus8 tbl corePlacedData1 (bs.getD idx 0#8).toNat hb0_lt,
        sepConj_comm (tbl ↦ᵣ corePlacedData1) (p ↦ₛ bs), sepConj_assoc, ← fuWorkPre]
  refine hcut_9c _ rfl (fu_keep_regs hregs hrun) ?_ (by simp [arm64_norm])
  simp only [arm64_norm]
  generalize bs.getD idx 0#8 = b0; revert b0; decide

end

end VerifiedLibraries.RustStd
