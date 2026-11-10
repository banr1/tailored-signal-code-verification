/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.StartupPre
public import ProofLib.StdStartup.LangStartPre
public import ProofLib.SepLogic.WP.StepsProcessSyscalls
public import ProofLib.SepLogic.WP.StepsProcessLse
public import ProofLib.SepLogic.WP.StepsProcessLlsc
public import ProofLib.MallocngBridge
import ProofLib.StdStartup.StdDetect
import ProofLib.StdStartup.OutlineAtomics
import ProofLib.SyscallModels
import ProofLib.BV.Arith
import ProofLib.BV.WidthNorm
public meta import ProofLib.LiteralFetchLint

/-!
# Startup Helper Lemmas for `lang_start_internal`

Layout-generic `SepWP` step lemmas for the `musl` and Rust `std::rt` subroutines called before
`userMain`: `cas8_relax`, `getauxval`, `poll`, `sysconf(_SC_PAGESIZE)`, `signal`/`sigaction`, and
alternate signal stack setup (`sigaltstack`, `mmap`, `mprotect`, `make_handler`).
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup StdBinaryLayout

theorem hbThreadIdInv_one (C : HbCliLayout) (tp : BitVec 64) :
    ((tp + 0x58#64) ↦₆₄ 1#64) ∗ (C.std.threadIdCounterAddr ↦₆₄ 1#64) ⊢ HbThreadIdInv C tp := by
  unfold HbThreadIdInv
  exact Entails.trans (Entails.pure_right (Or.inr rfl) (Entails.refl _)) (Entails.sepExists_right 1#64 (Entails.refl _))

private theorem hbFetchAtAcc_withSvc {P : Program} (svc : State → State) {b : BitVec 64} :
    ∀ {off : Nat} {is : List Instr} {acc acc' : Prop}, (acc → acc') → hbFetchAtAcc P b off is acc → hbFetchAtAcc (P.withSvc svc) b off is acc'
  | _, [], _, _, himp, h => himp h
  | _, _ :: _, _, _, himp, ⟨hf, hr⟩ => ⟨hf, hbFetchAtAcc_withSvc svc himp hr⟩

private theorem hbChunkStepAcc_withSvc {P : Program} (svc : State → State) {acc acc' : Prop} (himp : acc → acc') :
    ∀ {c : CodeChunk}, hbChunkStepAcc P acc c → hbChunkStepAcc (P.withSvc svc) acc' c
  | .words _ _, ⟨hc, ha⟩ => ⟨hc, himp ha⟩
  | .instrs0 _ _, h => hbFetchAtAcc_withSvc svc himp h
  | .instrs _ _ _, h => hbFetchAtAcc_withSvc svc himp h

private theorem hbCodeStepFacts_withSvc {P : Program} (svc : State → State) :
    ∀ {cs : List CodeChunk}, HbCodeStepFacts P cs → HbCodeStepFacts (P.withSvc svc) cs
  | [], _ => trivial
  | _ :: _, h => hbChunkStepAcc_withSvc svc (hbCodeStepFacts_withSvc svc) h

/-! ## Auxiliary vector, `cas8_relax`, and `getauxval` -/

private theorem hbPageAlignUp_add_page (n : Nat) : Arm64.pageAlignUp (n + 4096) = Arm64.pageAlignUp n + 4096 := by
  unfold Arm64.pageAlignUp Arm64.PAGE_SIZE; omega

private theorem hbPointsToBytes_encodeAuxvBytes_nil (ptr : BitVec 64) :
    (ptr ↦ₛ encodeAuxvBytes []) = (ptr ↦₆₄ 0#64) ∗ ((ptr + 8#64) ↦₆₄ 0#64) := by
  have heq : encodeAuxvBytes [] = unpack64 0#64 ++ unpack64 0#64 := by simp [encodeAuxvBytes_eq_flatMap_bytesLE]; rfl
  rw [heq, pointsToBytes_append, ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes, unpack64_length]

private theorem hbPointsToBytes_encodeAuxvBytes_cons (ptr t v : BitVec 64) (rest : List (BitVec 64 × BitVec 64)) :
    (ptr ↦ₛ encodeAuxvBytes ((t, v) :: rest)) = (ptr ↦₆₄ t) ∗ ((ptr + 8#64) ↦₆₄ v) ∗ ((ptr + 16#64) ↦ₛ encodeAuxvBytes rest) := by
  have heq : encodeAuxvBytes ((t, v) :: rest) = unpack64 t ++ (unpack64 v ++ encodeAuxvBytes rest) := by simp [encodeAuxvBytes_eq_flatMap_bytesLE]; rfl
  rw [heq, pointsToBytes_append, pointsToBytes_append, ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes, unpack64_length, BitVec.add_assoc]; rfl

theorem hb_step_b_to {P : Program} {target_pc pc dst : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.b (dst - pc)))
    (hnext : SepWP P target_pc (s.setPC dst) Pre post oom) : SepWP P target_pc s Pre post oom :=
  SepWP.step_pure (s' := s.setPC dst) hpc hrun hfetch
    (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.b (dst - pc)) _ rfl]; simp [wp_norm, arm64_norm]; rw [show pc + (dst - pc) = dst by bv_omega])
    rfl hnext

theorem hb_step_bl_to {P : Program} {target_pc pc dst : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.bl (dst - pc)))
    (hnext : SepWP P target_pc ((s.writeReg64 .lr (pc + 4#64)).setPC dst) Pre post oom) : SepWP P target_pc s Pre post oom :=
  SepWP.step_pure (s' := (s.writeReg64 .lr (pc + 4#64)).setPC dst) hpc hrun hfetch
    (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.bl (dst - pc)) _ rfl]; simp [wp_norm, arm64_norm]; rw [show pc + (dst - pc) = dst by bv_omega])
    rfl hnext

local macro "hb_wp_simp" : tactic => `(tactic|
  simp (config := { decide := true }) [State.stepExclOracle, State.stepExclLoop, State.readReg32, wp_norm, arm64_norm, bv_lin_norm, *])

/-- Non-VM process fields preserved across non-signal, non-altstack startup steps. -/
def HbNonVmFields (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.sigActions = s0.sigActions ∧ sf.sigAltStack = s0.sigAltStack

theorem HbNonVmFields.rfl (s : State) : HbNonVmFields s s := ⟨_root_.rfl, _root_.rfl, _root_.rfl, _root_.rfl, _root_.rfl⟩
theorem HbNonVmFields.trans {s0 s1 s2 : State} (h01 : HbNonVmFields s0 s1) (h12 : HbNonVmFields s1 s2) : HbNonVmFields s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1, h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.trans h01.2.2.2.2⟩
theorem HbNonVmFields.of_std {s0 sf : State} (h : StdStatePreserved s0 sf) (hsas : sf.sigAltStack = s0.sigAltStack) : HbNonVmFields s0 sf :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hsas⟩

@[local simp] private theorem hbNonVm_w64_r (a b : State) (r : Reg) (v : BitVec 64) : HbNonVmFields a (b.writeReg64 r v) ↔ HbNonVmFields a b := by cases r <;> rfl
@[local simp] private theorem hbNonVm_w64_l (a b : State) (r : Reg) (v : BitVec 64) : HbNonVmFields (a.writeReg64 r v) b ↔ HbNonVmFields a b := by cases r <;> rfl
@[local simp] private theorem hbNonVm_w32_r (a b : State) (r : Reg) (v : BitVec 32) : HbNonVmFields a (b.writeReg32 r v) ↔ HbNonVmFields a b := by simp [State.writeReg32]
@[local simp] private theorem hbNonVm_w32_l (a b : State) (r : Reg) (v : BitVec 32) : HbNonVmFields (a.writeReg32 r v) b ↔ HbNonVmFields a b := by simp [State.writeReg32]
@[local simp] private theorem hbNonVm_pc_r (a b : State) (p : BitVec 64) : HbNonVmFields a (b.setPC p) ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_pc_l (a b : State) (p : BitVec 64) : HbNonVmFields (a.setPC p) b ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_mem_r (a b : State) (m : Memory) : HbNonVmFields a (b.setMem m) ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_mem_l (a b : State) (m : Memory) : HbNonVmFields (a.setMem m) b ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_ps_r (a b : State) (p : PState) : HbNonVmFields a (b.setPState p) ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_ps_l (a b : State) (p : PState) : HbNonVmFields (a.setPState p) b ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_adv_r (a b : State) : HbNonVmFields a b.advancePC ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_adv_l (a b : State) : HbNonVmFields a.advancePC b ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_excl_r (a b : State) : HbNonVmFields a b.stepExclOracle ↔ HbNonVmFields a b := by cases b; rfl
@[local simp] private theorem hbNonVm_excl_l (a b : State) : HbNonVmFields a.stepExclOracle b ↔ HbNonVmFields a b := by cases a; rfl
@[local simp] private theorem hbNonVm_exclLoop_r (a b : State) : HbNonVmFields a b.stepExclLoop ↔ HbNonVmFields a b := by cases b; rfl
@[local simp] private theorem hbNonVm_exclLoop_l (a b : State) : HbNonVmFields a.stepExclLoop b ↔ HbNonVmFields a b := by cases a; rfl

local macro "hb_nv_rfl " s:term : tactic => `(tactic|
  (simp only [hbNonVm_w64_r, hbNonVm_w32_r, hbNonVm_pc_r, hbNonVm_mem_r, hbNonVm_ps_r,
    hbNonVm_adv_r, hbNonVm_excl_r, hbNonVm_exclLoop_r]
   exact HbNonVmFields.rfl $s))

section
arm64_proof_prelude

/-- Step `__aarch64_cas8_relax` (`L.cas8RelaxAddr`) when `L.haveLseAtomicsAddr ↦₈ haveLse` is writable (`↦₈`). -/
theorem step_hb_cas8Relax_rw {P : Program} {L : StdBinaryLayout} (hc : hasInstrs P L.cas8RelaxAddr (cas8RelaxInstrs L))
    {target_pc ptr v0 exp new : BitVec 64} {haveLse : BitVec 8} {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s0.pc = L.cas8RelaxAddr) (hrun : s0.status = .Running) (hx0 : s0.readReg64 .x0 = exp) (hx1 : s0.readReg64 .x1 = new) (hx2 : s0.readReg64 .x2 = ptr) (halign : MemWidth.isAligned .X64 ptr = true)
    (hnext : ∀ sf : State, sf.pc = s0.readReg64 .x30 → sf.status = .Running → sf.sp = s0.sp → sf.readReg64 .x0 = v0 → CalleeSavedPreserved s0 sf → HbNonVmFields s0 sf →
      SepWP P target_pc sf ((ptr ↦₆₄ (if v0 == exp then new else v0)) ∗ (L.haveLseAtomicsAddr ↦₈ haveLse) ∗ F) post oom) :
    SepWP P target_pc s0 ((ptr ↦₆₄ v0) ∗ (L.haveLseAtomicsAddr ↦₈ haveLse) ∗ F) post oom := by
  have_instrs hc 0 12; wp_steps 3; wp_if hcbz
  · wp_step; refine SepWP.step_cas_llsc_retry64 (pc := L.cas8RelaxAddr + 24#64) (ea := ptr) (v0 := v0) (exp := exp) (new := new)
      (by hb_wp_simp) (by hb_wp_simp) hf_6
      (by rw [show L.cas8RelaxAddr + 24#64 + 4#64 = L.cas8RelaxAddr + 28#64 by bv_lin]; exact hf_7)
      (by rw [show L.cas8RelaxAddr + 24#64 + 8#64 = L.cas8RelaxAddr + 32#64 by bv_lin]; exact hf_8)
      (by rw [show L.cas8RelaxAddr + 24#64 + 12#64 = L.cas8RelaxAddr + 36#64 by bv_lin]; exact hf_9)
      (by rw [show L.cas8RelaxAddr + 24#64 + 16#64 = L.cas8RelaxAddr + 40#64 by bv_lin]; exact hf_10)
      (by decide) rfl (by hb_wp_simp) halign (by hb_wp_simp) (by hb_wp_simp) rfl fun m' => ?_
    have hf11' : P.fetch (L.cas8RelaxAddr + 24#64 + 20#64) = some (.ret (.gpr 30#5)) := by
      rw [show L.cas8RelaxAddr + 24#64 + 20#64 = L.cas8RelaxAddr + 44#64 by bv_lin]; exact hf_11
    by_cases heq : v0 == exp <;> simp only [heq, Bool.false_eq_true, ↓reduceIte] at hnext ⊢ <;> wp_step <;>
      exact hnext _ (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) (by hb_nv_rfl s0)
  · refine SepWP.step_cas64 (pc := L.cas8RelaxAddr + 12#64) (ea := ptr) (v0 := v0) (exp := exp) (new := new)
      (by hb_wp_simp) (by hb_wp_simp) hf_3 rfl (by hb_wp_simp) halign (by hb_wp_simp) (by hb_wp_simp) rfl fun m' => ?_
    wp_step; exact hnext _ (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) (by hb_nv_rfl s0)

/-- Step 8-byte `memcpy(dst, src, 8)` (`L.memcpyAddr`) preserving `HbNonVmFields`. -/
theorem step_hb_memcpy8 {P : Program} {L : StdBinaryLayout} (hc : hasInstrs P L.memcpyAddr hbMemcpyInstrs)
    {target_pc ret_pc dst src v : BitVec 64} {s0 : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s0.mem ⊨ Pre ∗ R → s0.mem ⊨ (memRegion dst 8 ∗ (src ↦₆₄ v)) ∗ (F ∗ R))
    (hpc : s0.pc = L.memcpyAddr) (hrun : s0.status = .Running)
    (hlr : s0.readReg64 .lr = ret_pc) (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src) (hx2 : s0.readReg64 .x2 = 8#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      sf.readReg64 .x0 = dst → HbNonVmFields s0 sf →
      SepWP P target_pc sf (((dst ↦₆₄ v) ∗ (src ↦₆₄ v)) ∗ F) post oom) :
    SepWP P target_pc s0 Pre post oom := by
  refine SepWP.weaken_pre_frame (P' := (memRegion dst 8 ∗ (src ↦₆₄ v)) ∗ F) (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  wp_conv_pre => rw [memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_left]
  refine SepWP.exists_elim fun w0 => ?_
  have_instrs hc 0 8; have_instrs hc 13 6; clear hc
  have hhi128 : ConditionHolds .HI (subsPState64 8#64 128#64) = false := by unfold subsPState64 ConditionHolds; dsimp [AddWithCarry64]; decide
  have hhi32 : ConditionHolds .HI (subsPState64 8#64 32#64) = false := by unfold subsPState64 ConditionHolds; dsimp [AddWithCarry64]; decide
  have hcc16 : ConditionHolds .CC (subsPState64 8#64 16#64) = true := by unfold subsPState64 ConditionHolds; dsimp [AddWithCarry64]; decide
  have hsrc8 : src + 8#64 + 0xfffffffffffffff8#64 = src := by bv_lin
  have hdst8 : dst + 8#64 + 0xfffffffffffffff8#64 = dst := by bv_lin
  wp_steps 14
  exact hnext _ (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
    (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])
    (by hb_wp_simp) (by hb_nv_rfl s0)

private theorem step_hb_getauxval_scan_opt {P : Program} {L : StdBinaryLayout} (hc : hasInstrs P L.getauxvalAddr (getauxvalInstrs L))
    (he : P.hasCode L.errnoLocationAddr [0xd53bd040#32, 0xd1029000#32, 0xd65f03c0#32]) {target_pc tag tp : BitVec 64} (htag0 : tag ≠ 0#64)
    {post : State → SepProp → Prop} {oom : State → SepProp} (entries : List (BitVec 64 × BitVec 64)) (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64) :
    ∀ (ptr : BitVec 64) (errno0 : BitVec 32) (s : State) (F : SepProp),
      s.pc = L.getauxvalAddr + 0x1c#64 → s.status = .Running → s.readReg64 (.gpr 0#5) = tag → s.readReg64 (.gpr 1#5) = ptr →
      s.tpidrEl0 = tp → MemWidth.isAligned .W32 (tp - 164#64) = true →
      (∀ (sf : State) (errno1 : BitVec 32), sf.pc = L.getauxvalAddr + 0x54#64 → sf.status = .Running → sf.sp = s.sp →
        sf.readReg64 (.gpr 19#5) = ((entries.find? (·.1 == tag)).map Prod.snd).getD 0#64 →
        CalleeSavedPreserved (s.writeReg64 (.gpr 19#5) (((entries.find? (·.1 == tag)).map Prod.snd).getD 0#64)) sf → HbNonVmFields s sf →
        SepWP P target_pc sf ((ptr ↦ₛ encodeAuxvBytes entries) ∗ ((tp - 164#64) ↦₃₂ errno1) ∗ F) post oom) →
      SepWP P target_pc s ((ptr ↦ₛ encodeAuxvBytes entries) ∗ ((tp - 164#64) ↦₃₂ errno0) ∗ F) post oom := by
  induction entries with
  | nil =>
    intro ptr errno0 s F hpc hrun hx0 hx1 htp healign hnext; have_instrs hc 7 6; have_instrs hc 18 3
    rw [hbPointsToBytes_encodeAuxvBytes_nil]; wp_steps 3
    refine hb_step_bl_to (pc := L.getauxvalAddr + 72#64) (dst := L.errnoLocationAddr) (by hb_wp_simp) (by hb_wp_simp) hf_18 ?_
    rw [show L.getauxvalAddr + 72#64 + 4#64 = L.getauxvalAddr + 76#64 by bv_lin]; wp_steps 3; clear he; wp_steps 2; rw [← hbPointsToBytes_encodeAuxvBytes_nil]
    exact hnext _ 2#32 (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) (by hb_nv_rfl s)
  | cons kv rest ih =>
    rcases kv with ⟨t, v⟩; intro ptr errno0 s F hpc hrun hx0 hx1 htp healign hnext
    have ht0 : t ≠ 0#64 := hnonull t v (List.mem_cons_self ..); have_instrs hc 7 6; have_instrs hc 16 2
    rw [hbPointsToBytes_encodeAuxvBytes_cons]; wp_steps 3; wp_if hcbz
    · exact absurd hcbz ht0
    · wp_step; wp_if hbeq
      · subst hbeq; wp_steps 2; rw [← hbPointsToBytes_encodeAuxvBytes_cons]
        have hfind_eq : ((List.find? (fun x => x.1 == t) ((t, v) :: rest)).map Prod.snd).getD 0#64 = v := by simp
        rw [hfind_eq] at hnext
        exact hnext _ errno0 (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) (by hb_nv_rfl s)
      · have hne_beq : (t == tag) = false := beq_eq_false_iff_ne.mpr hbeq
        have hfind_ne : ((List.find? (fun x => x.1 == tag) ((t, v) :: rest)).map Prod.snd).getD 0#64 =
            ((List.find? (fun x => x.1 == tag) rest).map Prod.snd).getD 0#64 := by simp [hne_beq]
        wp_steps 2
        have hassoc : (((ptr ↦₆₄ t) ∗ ((ptr + 8#64) ↦₆₄ v) ∗ ((ptr + 16#64) ↦ₛ encodeAuxvBytes rest)) ∗ ((tp - 164#64) ↦₃₂ errno0) ∗ F) =
          ((ptr + 16#64) ↦ₛ encodeAuxvBytes rest) ∗ ((tp - 164#64) ↦₃₂ errno0) ∗ ((ptr ↦₆₄ t) ∗ ((ptr + 8#64) ↦₆₄ v) ∗ F) := by apply Entails.antisymm <;> sep_entail
        rw [hassoc]
        refine ih (fun t' v' hm => hnonull t' v' (List.mem_cons_of_mem _ hm)) (ptr + 16#64) errno0 _ _
          (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by simp [wp_norm, arm64_norm, htp]) healign
          fun sf errno1 hpc_f hrun_f hsp_f hx19_f hcs_f hnv_f => ?_
        have hassoc2 : (((ptr + 16#64) ↦ₛ encodeAuxvBytes rest) ∗ ((tp - 164#64) ↦₃₂ errno1) ∗ ((ptr ↦₆₄ t) ∗ ((ptr + 8#64) ↦₆₄ v) ∗ F)) =
          (ptr ↦ₛ encodeAuxvBytes ((t, v) :: rest)) ∗ ((tp - 164#64) ↦₃₂ errno1) ∗ F := by
          rw [hbPointsToBytes_encodeAuxvBytes_cons]; apply Entails.antisymm <;> sep_entail
        rw [hassoc2]; rw [hfind_ne] at hnext
        exact hnext sf errno1 hpc_f hrun_f (by simpa [wp_norm, arm64_norm] using hsp_f) hx19_f
          (CalleeSavedPreserved.trans (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f) (by simpa using hnv_f)

private theorem step_hb_getauxval_opt {P : Program} {L : StdBinaryLayout} (hc : hasInstrs P L.getauxvalAddr (getauxvalInstrs L))
    (he : P.hasCode L.errnoLocationAddr [0xd53bd040#32, 0xd1029000#32, 0xd65f03c0#32])
    {target_pc ret_pc tag auxvAddr : BitVec 64} {entries : List (BitVec 64 × BitVec 64)} {errno0 : BitVec 32} {s0 : State} {Pre F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s0.mem ⊨ Pre ∗ R →
      s0.mem ⊨ (((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ (muslErrnoAddr s0 ↦₃₂ errno0) ∗ stackAt s0.sp 0x20) ∗ (F ∗ R))
    (hpc : s0.pc = L.getauxvalAddr) (hrun : s0.status = .Running) (hsp_align : s0.spAligned = true) (hlr : s0.readReg64 .x30 = ret_pc)
    (hx0 : s0.readReg64 .x0 = tag) (htag0 : tag ≠ 0#64) (htag17 : tag ≠ 0x17#64) (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64)
    (healign : MemWidth.isAligned .W32 (muslErrnoAddr s0) = true)
    (hnext : ∀ (sf : State) (errno1 : BitVec 32), sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp → sf.spAligned = true →
      sf.readReg64 .x0 = ((entries.find? (·.1 == tag)).map Prod.snd).getD 0#64 → CalleeSavedPreserved s0 sf → HbNonVmFields s0 sf →
      SepWP P target_pc sf ((((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ (muslErrnoAddr sf ↦₃₂ errno1) ∗ stackAt s0.sp 0x20) ∗ F) post oom) :
    SepWP P target_pc s0 Pre post oom := by
  refine SepWP.weaken_pre_frame (P' := (((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ (muslErrnoAddr s0 ↦₃₂ errno0) ∗ stackAt s0.sp 0x20) ∗ F)
    (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have_instrs hc 0 7; have_instrs hc 21 4
  have hsp_sub_al : ((s0.sp + 0xffffffffffffffe0#64) &&& 0xf#64 == 0#64) = true := by simpa [BitVec.sub_eq_add_neg] using s0.spAligned_sub 0x20#64 hsp_align
  wp_conv_pre => rw [stackAt_eq_cells s0.sp 4]
  simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun w0 => SepWP.exists_elim fun w1 => SepWP.exists_elim fun w2 => SepWP.exists_elim fun w3 => ?_
  wp_steps 5; wp_if hbeq17
  · exact absurd (by simpa [wp_norm, arm64_norm, hx0] using hbeq17) htag17
  · wp_steps 2; unfold muslErrnoAddr at healign ⊢
    refine SepWP.weaken_pre_frame (P' := (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ ((s0.tpidrEl0 - 164#64) ↦₃₂ errno0) ∗ ?_) (fun R hm => by revert hm; sep_frame) ?_
    refine step_hb_getauxval_scan_opt hc he htag0 entries hnonull _ _ _ _
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, hx0]) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) healign
      fun sf errno1 hpc_f hrun_f hsp_f hx19_f hcs_f hnv_f => ?_
    have hsp_sf : sf.sp = s0.sp - 32#64 := by simpa [wp_norm, arm64_norm, bv_lin_norm] using hsp_f
    have hsp_al_cur : (sf.sp &&& 15#64 == 0#64) = true := by rw [hsp_sf]; simpa [State.spAligned, BitVec.sub_eq_add_neg] using s0.spAligned_sub 0x20#64 hsp_align
    have hc0 : s0.sp - 32#64 = sf.sp := hsp_sf.symm
    have hc1 : s0.sp - 24#64 = sf.sp + 8#64 := by rw [hsp_sf]; bv_lin
    have hc2 : s0.sp - 16#64 = sf.sp + 16#64 := by rw [hsp_sf]; bv_lin
    have hsp_end : sf.sp + 32#64 = s0.sp := by rw [hsp_sf]; bv_lin
    have htp_sf : s0.tpidrEl0 = sf.tpidrEl0 := by have h := hnv_f.2.2.1; simp only [wp_norm, arm64_norm] at h; exact h.symm
    clear he hsp_f hsp_sf; wp_conv_pre => rw [hc0, hc1, hc2, htp_sf]
    wp_steps 4; unfold muslErrnoAddr at hnext
    refine SepWP.weaken_pre_frame (P' := (((L.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ ((sf.tpidrEl0 - 164#64) ↦₃₂ errno1) ∗ stackAt s0.sp 0x20) ∗ F)
      (fun R hm => by rw [← hc2, ← hc1, ← hc0] at hm; rw [stackAt_eq_cells s0.sp 4]; fold_stack_cells) ?_
    refine hnext _ errno1 (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_f]) (by simp [wp_norm, arm64_norm])
      (by simpa [State.spAligned, wp_norm, arm64_norm, hsp_end] using hsp_align) (by simp [wp_norm, arm64_norm]) ?_ (by simpa using hnv_f)
    rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs_f with ⟨_, g20, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩
    simp only [wp_norm, arm64_norm] at g20 g21 g22 g23 g24 g25 g26 g27 g28 gv
    rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, g20, g21, g22, g23, g24, g25, g26, g27, g28, gv]

/-! ## `poll` and `sysconf(_SC_PAGESIZE)` -/

private theorem hb_step_str64_perm {prog : Program} {target_pc pc ea val : BitVec 64} {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .X64 rt addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val) (hstore : SepStore64 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP; intro R hm; let m' := s.mem.write64 ea val; have hm' := hstore.store hm; have hcan := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .X64 rt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; have hn := hnext m' (Memory.perm_write64 s.mem ea val); unfold SepWP at hn; exact hn R hm'

private theorem hb_step_stp64_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64} {s : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2) (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2) (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP; intro R hm; let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 := hstore1.store hm; have hm2 := hstore2.store hm1; have hcan1 := hstore1.writable hm; have hcan2 := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m2 := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]; have hn := hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1)); unfold SepWP at hn; exact hn R hm2

private theorem cond_hi_adds4096_false {v : BitVec 64} (hlt : v.toNat < 2 ^ 64 - 4096) :
    ConditionHolds CondCode.HI (addsPState64 v 4096#64) = false := by
  unfold addsPState64 ConditionHolds; dsimp [AddWithCarry64]; simp only [Bool.and_eq_false_iff, BitVec.msb_eq_decide, decide_eq_false_iff_not]; left; bv_omega

private theorem step_hb_syscallRet_nonneg {P : Program} {L : StdBinaryLayout} {target_pc ret_pc x0v : BitVec 64}
    (hcode : P.hasCode L.syscallRetAddr syscallRetNonnegWords) {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ stackAt s.sp 0x20 ∗ (F ∗ R))
    (hpc : s.pc = L.syscallRetAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = x0v) (hlt : x0v.toNat < 2 ^ 64 - 4096)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = x0v → HbNonVmFields s sf → VmFieldsPreserved s sf →
      SepWP P target_pc sf (stackAt s.sp 0x20 ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame (P' := stackAt s.sp 0x20 ∗ F) (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have hhi := cond_hi_adds4096_false hlt
  have hsp_sub_al : ((s.sp - 32#64) &&& 0xf#64 == 0#64) = true := by simpa using s.spAligned_sub 0x20#64 hsp_align
  rw [stackAt_eq_cells s.sp 4]; unfold_stack_cells 4
  have hf0 : P.fetch L.syscallRetAddr = some (.stp .W64 .x29 .lr (.PreIndex .sp 0xffffffffffffffe0#64)) := Program.fetch_of_hasCode_decodeAt 0 hcode (by bv_lin) (by decide)
  have hf3 : P.fetch (L.syscallRetAddr + 12#64) = some (.str .X64 (.gpr 19#5) (.Offset .sp 16#64)) := Program.fetch_of_hasCode_decodeAt 3 hcode (by bv_lin) (by decide)
  refine hb_step_stp64_perm (ea2 := s.sp - 24#64) hpc hrun hf0
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_align])
    (show evalAddrMode s (.PreIndex .sp 0xffffffffffffffe0#64) = (s.sp - 32#64, some (.sp, s.sp - 32#64)) by simp [evalAddrMode, arm64_norm, bv_lin_norm])
    (by bv_lin) rfl rfl (by wp_sep_access) (by wp_sep_access) fun m1 hm1 => ?_
  wp_steps 2
  refine hb_step_str64_perm (ea := s.sp - 16#64) (wb := none) (val := s.readReg64 (.gpr 19#5))
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf3
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, wp_norm, arm64_norm] using hsp_sub_al)
    (by simp [evalAddrMode, wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm]) (by wp_sep_access) fun m2 hm2 => ?_
  wp_steps 5
  refine SepWP.weaken_pre_frame (P' := stackAt s.sp 0x20 ∗ F) (fun R hm => by rw [stackAt_eq_cells s.sp 4] at *; fold_stack_cells) ?_
  refine hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by simp [wp_norm, arm64_norm, bv_lin_norm])
    (by simpa [State.spAligned, wp_norm, arm64_norm, bv_lin_norm] using hsp_align) (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hx0]) (by hb_nv_rfl s) ⟨rfl, rfl, rfl, fun a => ?_⟩
  simp only [wp_norm, arm64_norm]; exact (congrFun hm2 a).trans (congrFun hm1 a)

/-- Step `poll(ufds, 3, 0)` (`L.pollAddr`) when stdio fds `0, 1, 2` are open, returning `x0 = 0#64`. -/
theorem step_hb_poll_stdio3 {P : Program} {L : StdBinaryLayout} {target_pc ret_pc : BitVec 64}
    (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc) (hsccp : P.hasCode L.sccpAddr sccpWords)
    (hcp : hasInstrs P L.syscallCpAddr (syscallCpInstrs L)) (hret : P.hasCode L.syscallRetAddr syscallRetNonnegWords)
    (hpoll : hasInstrs P L.pollAddr (pollInstrs L)) {s : State} {ufds : BitVec 64} {Pre F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ (((ufds ↦₆₄ 0#64) ∗ ((ufds + 8#64) ↦₆₄ 1#64) ∗ ((ufds + 16#64) ↦₆₄ 2#64)) ∗ stackAt s.sp 0x40) ∗ (F ∗ R))
    (hpc : s.pc = L.pollAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hsp_lo : 0x40 ≤ s.sp.toNat)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = ufds) (hx1 : s.readReg64 .x1 = 3#64) (hx2 : s.readReg32 .x2 = 0#32)
    (hufds_fit : ufds.toNat + 24 ≤ 2 ^ 64) (heval : evalPpollBytes s.fs stdioPollfdBytes 0 = some (stdioPollfdBytes, 0))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → HbNonVmFields s sf →
      SepWP P target_pc sf ((((ufds ↦₆₄ 0#64) ∗ ((ufds + 8#64) ↦₆₄ 1#64) ∗ ((ufds + 16#64) ↦₆₄ 2#64)) ∗ stackAt s.sp 0x40) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame (P' := (((ufds ↦₆₄ 0#64) ∗ ((ufds + 8#64) ↦₆₄ 1#64) ∗ ((ufds + 16#64) ↦₆₄ 2#64)) ∗ stackAt s.sp 0x40) ∗ F)
    (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have_instrs hpoll 0 29
  have hsp_sub_align : ((s.sp + 0xffffffffffffffe0#64) &&& 0xf#64 == 0#64) = true := by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x20#64 hsp_align
  rw [State.readReg32, Reg.x2] at hx2; rw [sepConj_assoc, stdioPollfds_eq_bytes ufds, stackAt_split_cells s.sp 0x20 4 (by decide)]
  simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 4 (refine SepWP.exists_elim fun _ => ?_); wp_steps 25
  refine hb_step_bl_to (pc := L.pollAddr + 100#64) (dst := L.syscallCpAddr) (by hb_wp_simp) (by hb_wp_simp) hf_25 ?_
  have htsp8 : (s.sp - 8#64) = (s.sp - 16#64) + 8#64 := by bv_lin
  wp_conv_pre => rw [htsp8]
  refine hb_step_b_to (pc := L.syscallCpAddr) (dst := L.sccpAddr) (by hb_wp_simp) (by hb_wp_simp) (by simpa [syscallCpInstrs] using hcp 0 (Nat.zero_lt_succ 0)) ?_
  wp_steps 7
  refine SepWP.weaken_pre_frame (P' := (ufds ↦ₛ stdioPollfdBytes) ∗ ((((s.sp - 16#64) ↦₆₄ 0#64) ∗ (((s.sp - 16#64) + 8#64) ↦₆₄ 0#64)) ∗ ?_))
    (fun R hm => by revert hm; sep_frame) ?_
  have heval_svc_ppoll : ∀ st : State, st.readReg64 .x8 = 73#64 → P.evalInst (.system false 0#16) st = execPpoll st := fun st hx8 => by
    rcases hsvc with h | h
    · rw [_root_.Arm64.Program.evalInst_svc0, h, evalSvc_standard]
      simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable, hx8]
    · rw [_root_.Arm64.Program.evalInst_svc0, h, evalSvc_nonVmSvc]
      simp [nonVmSvc, nonVmSyscallTable, Syscall.dispatch, Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable, hx8]
  refine SepWP.step_svc_ppoll (pc := L.sccpAddr + 28#64) (ufds := ufds) (tsp := s.sp - 16#64) (nfds := 3) (count := 0)
    (bs₀ := stdioPollfdBytes) (bs' := stdioPollfdBytes) (by hb_wp_simp) (by hb_wp_simp)
    (Program.fetch_of_hasCode_decodeAt 7 hsccp rfl (by decide))
    (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
    (by bv_omega) (by bv_omega) (by decide) hufds_fit (by decide)
    (by simpa [wp_norm, arm64_norm] using heval) (fun m' => ?_) (heval_svc_ppoll _ (by hb_wp_simp))
  wp_steps 1
  refine hb_step_bl_to (pc := L.pollAddr + 104#64) (dst := L.syscallRetAddr) (by hb_wp_simp) (by hb_wp_simp) hf_26 ?_
  rw [show L.pollAddr + 104#64 + 4#64 = L.pollAddr + 108#64 by bv_lin]
  refine step_hb_syscallRet_nonneg hret (ret_pc := L.pollAddr + 108#64) (x0v := 0#64) (F := ?_)
    (fun R hm => by simp only [wp_norm, arm64_norm, bv_lin_norm] at hm ⊢; revert hm; sep_frame)
    rfl (by simp [wp_norm, arm64_norm, hrun])
    (by simpa [State.spAligned, wp_norm, arm64_norm, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x20#64 hsp_align)
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by decide)
    fun s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hx0_2 hnv2 _ => ?_
  have hsp2_eq : s2.sp = s.sp - 32#64 := by simpa [wp_norm, arm64_norm, bv_lin_norm] using hsp2
  have h32 : s.sp - 32 = s2.sp := by simpa [BitVec.ofNat_eq_ofNat] using hsp2_eq.symm
  have h24 : s.sp - 24 = s2.sp + 8 := by rw [hsp2_eq]; bv_lin
  have hsp_end : s2.sp + 32#64 = s.sp := by rw [hsp2_eq]; bv_lin
  have hsp_al2_raw : (s2.sp &&& 15#64 == 0#64) = true := hsp_al2
  clear hsccp hret hsp2 hsp2_eq
  wp_conv_pre => simp only [wp_norm, arm64_norm, bv_lin_norm, BitVec.ofNat_eq_ofNat]; rw [h32, h24]
  wp_steps 2
  refine SepWP.weaken_pre_frame (P' := (((ufds ↦₆₄ 0#64) ∗ ((ufds + 8#64) ↦₆₄ 1#64) ∗ ((ufds + 16#64) ↦₆₄ 2#64)) ∗ stackAt s.sp 0x40) ∗ F)
    (fun R hm => by
      simp only [State.mem_setPC, State.mem_writeReg64]; simp only [wp_norm, arm64_norm, bv_lin_norm, BitVec.ofNat_eq_ofNat] at hm
      rw [← h24, ← h32] at hm; rw [stdioPollfds_eq_bytes ufds, stackAt_split_cells s.sp 0x20 4 (by decide)]; fold_stack_cells) ?_
  have hnv02 : HbNonVmFields s s2 := by
    unfold HbNonVmFields at hnv2 ⊢; rcases hnv2 with ⟨hfs, htr, htp, hsa, hsas⟩
    simp only [wp_norm, arm64_norm] at hfs htr htp hsa hsas ⊢; exact ⟨hfs, htr, htp, hsa, hsas⟩
  refine hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun2])
    (by simp [wp_norm, arm64_norm]) (by simpa [State.spAligned, wp_norm, arm64_norm, hsp_end] using hsp_align)
    ?_ (by simp [wp_norm, arm64_norm, hx0_2]) (hnv02.trans (by hb_nv_rfl s2))
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs2 with ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩
  simp only [wp_norm, arm64_norm] at g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 gv
  rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, gv]

/-- Step `sysconf(30)` (`_SC_PAGESIZE`) with `adr x0, L.sysconfValuesAddr` at `+0x1c`, returning `4096#64`. -/
theorem step_hb_sysconf_pagesize {P : Program} {L : StdBinaryLayout} {target_pc ret_pc : BitVec 64}
    (hsys : hasInstrs P L.sysconfAddr ((sysconfPagesizeInstrs L).take 6 ++
      [decodeWord 0xd503201f#32, .adr false .x0 (L.sysconfValuesAddr - (L.sysconfAddr + 0x1c#64))] ++ (sysconfPagesizeInstrs L).drop 8))
    (hepi : P.hasCode (L.sysconfAddr + 0xd8#64) sysconfEpilogueWords)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ (((L.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ stackAt s.sp 0x190) ∗ (F ∗ R))
    (hpc : s.pc = L.sysconfAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = 30#64)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf → sf.readReg64 .x0 = 4096#64 → HbNonVmFields s sf →
      SepWP P target_pc sf ((((L.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ stackAt s.sp 0x190) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame (P' := (((L.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ stackAt s.sp 0x190) ∗ F)
    (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have_instrs hsys 0 29
  have hsp_sub_align : ((s.sp + 0xfffffffffffffe70#64) &&& 0xf#64 == 0#64) = true := by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x190#64 hsp_align
  have hge : ConditionHolds CondCode.GE (addsPState32 0xffffff04#32 1#32) = false := by unfold addsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide
  have hlt : ConditionHolds CondCode.LT (addsPState32 0xffffff04#32 256#32) = false := by unfold addsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide
  have he0 : P.fetch (L.sysconfAddr + 216#64) = some (.ldp .W64 false .x29 .lr (.PostIndex .sp 400#64)) := Program.fetch_of_hasCode_decodeAt 0 hepi (by simp only [wp_norm]) (by decide)
  have he1 : P.fetch (L.sysconfAddr + 220#64) = some (.ret .lr) := Program.fetch_of_hasCode_decodeAt 1 hepi (by simp only [wp_norm]) (by decide)
  clear hepi
  wp_conv_pre => rw [stackAt_split_bottom s.sp 0x170 32 (by decide), memRegion_cells (s.sp - 0x190#64) 4 (by decide)]
  simp (disch := decide) only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 4 (refine SepWP.exists_elim fun _ => ?_); wp_steps 31
  refine SepWP.weaken_pre_frame (P' := (((L.sysconfValuesAddr + 60#64) ↦₁₆ᵣ 0xff04#16) ∗ ((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ stackAt s.sp 0x190) ∗ F)
    (fun R hm => by
      rw [stackAt_split_bottom s.sp 0x170 32 (by decide), memRegion_cells (s.sp - 0x190#64) 4 (by decide)]
      simp (disch := decide) only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left]; sep_entail) ?_
  exact hnext _ (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, bv_lin_norm] using hsp_align)
    (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) (by hb_wp_simp) (by hb_nv_rfl s)

/-! ## Signal dispositions and alternate signal stack -/

private theorem hb_evalSvc_sigaltstack {P : Program} {s : State} (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc) (hx8 : s.readReg64 .x8 = 132#64) :
    P.evalInst (.system false 0#16) s = execSigaltstack s := by
  rcases hsvc with h | h
  · rw [_root_.Arm64.Program.evalInst_svc0, h, evalSvc_standard]
    simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, hx8]
  · rw [_root_.Arm64.Program.evalInst_svc0, h, evalSvc_nonVmSvc]
    simp [nonVmSvc, nonVmSyscallTable, Syscall.dispatch, Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.signalsTable, hx8]

private theorem hb_evalSvc_rt_sigaction {P : Program} {s : State} (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc) (hx8 : s.readReg64 .x8 = 134#64) :
    P.evalInst (.system false 0#16) s = execRtSigaction s := by
  rcases hsvc with h | h
  · rw [_root_.Arm64.Program.evalInst_svc0, h, evalSvc_standard]
    simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, hx8]
  · rw [_root_.Arm64.Program.evalInst_svc0, h, evalSvc_nonVmSvc]
    simp [nonVmSvc, nonVmSyscallTable, Syscall.dispatch, Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.signalsTable, hx8]

private theorem hb_evalSvc_rt_sigprocmask {P : Program} {s : State} (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc) (hx8 : s.readReg64 .x8 = 135#64) :
    P.evalInst (.system false 0#16) s = execRtSigprocmask s := by
  rcases hsvc with h | h
  · rw [_root_.Arm64.Program.evalInst_svc0, h, evalSvc_standard]
    simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, hx8]
  · rw [_root_.Arm64.Program.evalInst_svc0, h, evalSvc_nonVmSvc]
    simp [nonVmSvc, nonVmSyscallTable, Syscall.dispatch, Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.signalsTable, hx8]

private theorem step_svc_rt_sigprocmask_unblock {P : Program} {target_pc pc setAddr maskVal : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : P.fetch pc = some (.system false 0#16)) (hx8 : s.readReg64 .x8 = 135#64) (hx0 : s.readReg32 .x0 = 1#32)
    (hx1 : s.readReg64 .x1 = setAddr) (hx2 : s.readReg64 .x2 = 0#64) (hx3 : s.readReg64 .x3 = 8#64)
    (hset_ne : setAddr ≠ 0#64) (hset_fit : setAddr.toNat + 8 ≤ 2 ^ 64)
    (hnext : SepWP P target_pc ((s.writeReg64 .x0 0#64).setPC (pc + 4#64)) ((setAddr ↦₆₄ maskVal) ∗ F) post oom) :
    SepWP P target_pc s ((setAddr ↦₆₄ maskVal) ∗ F) post oom := by
  unfold SepWP; intro R hm
  have hm' : s.mem ⊨ (setAddr ↦₆₄ maskVal) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcr : s.mem.canRead setAddr 8 = true := (IsBlock.pointsTo64 setAddr maskVal).canRead (by decide) hm'
  have hall : s.mem.allPerm (·.r) setAddr 8 = true := Memory.allPerm_r_of_canRead hcr
  have hne_b : (setAddr != 0#64) = true := bne_iff_ne.mpr hset_ne
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch); rw [hb_evalSvc_rt_sigprocmask hsvc hx8]
  have hev : execRtSigprocmask s = (s.writeReg64 .x0 0#64).setPC (pc + 4#64) := by
    simp [execRtSigprocmask, hx0, hx1, hx2, hx3, hne_b, hset_fit, hcr, hall, State.advancePC, State.setPC, State.writeReg64, hpc]
  rw [hev]; unfold SepWP at hnext; exact hnext R hm

private theorem hb_step_stxr32_either {prog : Program} {target_pc pc ea : BitVec 64} {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {v0 val : BitVec 32} {rel : Bool} {rs rn rt : Reg} (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stxr .W32 rel rs rn rt)) (hrs : rs = .x2) (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea) (halign : MemWidth.isAligned .W32 ea = true) (hval : s.readReg32 rt = val)
    (hok : s.exclWillFail = false → ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((s.stepExclOracle.writeReg .W32 .x2 0#64).setPC (pc + 4#64)).setMem m') ((ea ↦₃₂ val) ∗ F) post oom)
    (hfail : s.exclWillFail = true → SepWP prog target_pc ((s.stepExclOracle.writeReg .W32 .x2 1#64).setPC (pc + 4#64)) ((ea ↦₃₂ v0) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post oom := by
  subst hrs; apply SepWP.of_reaches_pc; intro R hm
  have hm' : s.mem ⊨ (ea ↦₃₂ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcw := (IsBlock.pointsTo32 ea v0).canWrite (by decide) hm'; have htrunc : (s.readReg64 rt).truncate 32 = val := hval
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch); cases hf : s.exclWillFail
  · have hstep : prog.evalInst (.stxr .W32 rel .x2 rn rt) s = ((s.stepExclOracle.writeReg .W32 .x2 0#64).setPC (pc + 4#64)).setMem (s.mem.write32 ea val) := by
      simp only [Program.evalInst, execInstWithSvc, hsp, haddr, halign, hf, htrunc, MemWidth.bytes, hcw, Memory.writeSized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
    rw [hstep]; refine SepWP.to_reaches_pc (hok hf _ (Memory.perm_write32 s.mem ea val)) ?_
    rw [sepConj_assoc]; exact (IsBlock.pointsTo32 ea v0).write32 hm' val
  · have hstep : prog.evalInst (.stxr .W32 rel .x2 rn rt) s = (s.stepExclOracle.writeReg .W32 .x2 1#64).setPC (pc + 4#64) := by
      simp only [Program.evalInst, execInstWithSvc, hsp, haddr, halign, hf, MemWidth.bytes, hcw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC, State.setPC, hpc]
    rw [hstep]; exact SepWP.to_reaches_pc (hfail hf) (by simpa [State.stepExclOracle] using hm)

private theorem hb_exclFails_tail_lt {s : State} {k : Nat} (hk : s.exclFails.length < k + 1) (hf : s.exclWillFail = true) : s.exclFails.tail.length < k := by
  cases h : s.exclFails with
  | nil => simp [State.exclWillFail_eq_headD, h] at hf
  | cons _ tl => simp [h] at hk ⊢; omega

private theorem cond_ls_subs6143_false {v : BitVec 64} (hlo : 6144 ≤ v.toNat) : ConditionHolds CondCode.LS (subsPState64 v 6143#64) = false := by
  unfold subsPState64 ConditionHolds; dsimp [AddWithCarry64]; simp only [Bool.not_eq_false', Bool.and_eq_true, BitVec.msb_eq_decide, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne]; exact ⟨by bv_omega, by bv_omega⟩

private theorem cond_ls_subs1_false {v : BitVec 64} (hlo : 1 < v.toNat) : ConditionHolds CondCode.LS (subsPState64 v 1#64) = false := by
  unfold subsPState64 ConditionHolds; dsimp [AddWithCarry64]; simp only [Bool.not_eq_false', Bool.and_eq_true, BitVec.msb_eq_decide, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne]; exact ⟨by bv_omega, by bv_omega⟩

@[local simp] private theorem calleeSavedVRegs_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) : calleeSavedVRegs (s.setSigAction sig act) = calleeSavedVRegs s := rfl
@[local simp] private theorem calleeSavedVRegs_setSigAltStack (s : State) (sas : SigAltStack) : calleeSavedVRegs (s.setSigAltStack sas) = calleeSavedVRegs s := rfl

private theorem step_hb_sigaltstack_probe {P : Program} {L : StdBinaryLayout} {sasAddr target_pc ret_pc : BitVec 64}
    (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc)
    (hsas_code : hasInstrs P sasAddr (decodeWords [0xa9bf7bfd#32, 0x910003fd#32, 0xb4000100#32, 0xb9400802#32,
      0x370800a2#32, 0xf9400804#32, 0xd282ffe3#32, 0xeb03009f#32, 0x540000e9#32, 0x37000182#32, 0xd2801088#32, 0xd4000001#32] ++
      [.bl (L.syscallRetAddr - (sasAddr + 0x30#64))] ++ decodeWords [0xa8c17bfd#32, 0xd65f03c0#32]))
    (hret : P.hasCode L.syscallRetAddr syscallRetNonnegWords) {s : State} {uoss v0 v1 v2 : BitVec 64} {Pre F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ (((uoss ↦₆₄ v0) ∗ ((uoss + 8#64) ↦₆₄ v1) ∗ ((uoss + 16#64) ↦₆₄ v2)) ∗ stackAt s.sp 0x30) ∗ (F ∗ R))
    (hpc : s.pc = sasAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = 0#64) (hx1 : s.readReg64 .x1 = uoss)
    (huoss_ne : uoss ≠ 0#64) (huoss_fit : uoss.toNat + 24 ≤ 2 ^ 64) (hsas0 : s.sigAltStack = {})
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → HbNonVmFields s sf →
      SepWP P target_pc sf ((((uoss ↦₆₄ 0#64) ∗ ((uoss + 8#64) ↦₃₂ 2#32) ∗ ((uoss + 12#64) ↦₃₂ 0#32) ∗ ((uoss + 16#64) ↦₆₄ 0#64)) ∗ stackAt s.sp 0x30) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  have hret' := hret
  refine SepWP.weaken_pre_frame (P' := (((uoss ↦₆₄ v0) ∗ ((uoss + 8#64) ↦₆₄ v1) ∗ ((uoss + 16#64) ↦₆₄ v2)) ∗ stackAt s.sp 0x30) ∗ F)
    (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have_instrs hsas_code 0 15
  have hsp_sub_al : ((s.sp + 0xfffffffffffffff0#64) &&& 0xf#64 == 0#64) = true := by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x10#64 hsp_align
  have hu_f : (uoss == 0#64) = false := beq_false_of_ne huoss_ne
  have hbytes : ((uoss ↦₆₄ v0) ∗ ((uoss + 8#64) ↦₆₄ v1) ∗ ((uoss + 16#64) ↦₆₄ v2)) = (uoss ↦ₛ (unpack64 v0 ++ (unpack64 v1 ++ unpack64 v2))) := by
    rw [pointsToBytes_append, pointsToBytes_append]; simp only [unpack64_length, ← pointsTo64_eq_pointsToBytes]
    rw [show uoss + 8#64 + 8#64 = uoss + 16#64 by bv_lin]
  wp_conv_pre => rw [hbytes, stackAt_split_cells s.sp 0x20 2 (by decide)]
  unfold_stack_cells 2; clear hret; wp_steps 4
  refine SepWP.weaken_pre_frame (P' := stackTAt 0#64 0#64 0#32 0#32 0#64 ∗ (optOldStackTAt uoss (unpack64 v0 ++ (unpack64 v1 ++ unpack64 v2)) ∗ ?_))
    (fun R hm => by dsimp only [stackTAt, optOldStackTAt]; rw [hu_f]; simp only [beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, emp_sepConj]; revert hm; sep_frame) ?_
  refine SepWP.step_svc_sigaltstack (pc := sasAddr + 44#64) (uss := 0#64) (ssSp := 0#64) (ssSize := 0#64) (uoss := uoss) (ssFlags := 0#32) (pad := 0#32)
    (oldBs₀ := unpack64 v0 ++ (unpack64 v1 ++ unpack64 v2))
    (by hb_wp_simp) (by hb_wp_simp) hf_11 (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
    (Or.inl rfl) (Or.inr ⟨huoss_fit, by simp [unpack64_length]⟩) (fun m' => ?_) (hb_evalSvc_sigaltstack hsvc (by hb_wp_simp))
  dsimp only []
  wp_conv_pre =>
    dsimp only [stackTAt, optOldStackTAt]
    simp only [wp_norm, arm64_norm, hsas0, hu_f, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, emp_sepConj, pointsToBytes_sigAltStack_toBytes, SigAltStack.flags_default, SS_DISABLE]
  refine hb_step_bl_to (pc := sasAddr + 48#64) (dst := L.syscallRetAddr) (by hb_wp_simp) (by hb_wp_simp) hf_12 ?_
  rw [show sasAddr + 48#64 + 4#64 = sasAddr + 52#64 by bv_lin]
  refine step_hb_syscallRet_nonneg hret' (ret_pc := sasAddr + 52#64) (x0v := 0#64) (F := ?_)
    (fun R hm => by simp only [wp_norm, arm64_norm, bv_lin_norm] at hm ⊢; revert hm; sep_frame)
    rfl (by simp [wp_norm, arm64_norm, hrun])
    (by simpa [State.spAligned, wp_norm, arm64_norm, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x10#64 hsp_align)
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by decide)
    fun s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hx0_2 hnv2 _ => ?_
  have hsp2_eq : s2.sp = s.sp - 16#64 := by simpa [wp_norm, arm64_norm, bv_lin_norm] using hsp2
  have h16 : s.sp - 16 = s2.sp := by simpa [BitVec.ofNat_eq_ofNat] using hsp2_eq.symm
  have h08 : s.sp - 8 = s2.sp + 8 := by rw [hsp2_eq]; bv_lin
  have hsp_end : s2.sp + 16#64 = s.sp := by rw [hsp2_eq]; bv_lin
  have hsp_al2_raw : (s2.sp &&& 15#64 == 0#64) = true := hsp_al2
  clear hret' hsp2 hsp2_eq; wp_conv_pre => simp only [wp_norm, arm64_norm, bv_lin_norm, BitVec.ofNat_eq_ofNat]; rw [h16, h08]
  wp_steps 2
  refine SepWP.weaken_pre_frame (P' := (((uoss ↦₆₄ 0#64) ∗ ((uoss + 8#64) ↦₃₂ 2#32) ∗ ((uoss + 12#64) ↦₃₂ 0#32) ∗ ((uoss + 16#64) ↦₆₄ 0#64)) ∗ stackAt s.sp 0x30) ∗ F)
    (fun R hm => by
      simp only [State.mem_setPC, State.mem_writeReg64]; simp only [wp_norm, arm64_norm, bv_lin_norm, BitVec.ofNat_eq_ofNat] at hm
      rw [← h08, ← h16] at hm; rw [stackAt_split_cells s.sp 0x20 2 (by decide)]; fold_stack_cells) ?_
  have hnv02 : HbNonVmFields s s2 := by
    unfold HbNonVmFields at hnv2 ⊢; rcases hnv2 with ⟨hfs, htr, htp, hsa, hsas⟩
    simp only [wp_norm, arm64_norm] at hfs htr htp hsa hsas ⊢; exact ⟨hfs, htr, htp, hsa, hsas⟩
  refine hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun2])
    (by simp [wp_norm, arm64_norm]) (by simpa [State.spAligned, wp_norm, arm64_norm, hsp_end] using hsp_align)
    ?_ (by simp [wp_norm, arm64_norm, hx0_2]) (hnv02.trans (by hb_nv_rfl s2))
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs2 with ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩
  simp only [wp_norm, arm64_norm] at g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 gv
  rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, gv]

private theorem hb_step_cut_pre {P : Program} {t : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (k : ∀ s', s' = s → SepWP P t s' Pre post oom) : SepWP P t s Pre post oom := k s rfl

private theorem step_hb_sigaltstack_install {P : Program} {L : StdBinaryLayout} {sasAddr target_pc ret_pc : BitVec 64}
    (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc)
    (hsas_code : hasInstrs P sasAddr (decodeWords [0xa9bf7bfd#32, 0x910003fd#32, 0xb4000100#32, 0xb9400802#32,
      0x370800a2#32, 0xf9400804#32, 0xd282ffe3#32, 0xeb03009f#32, 0x540000e9#32, 0x37000182#32, 0xd2801088#32, 0xd4000001#32] ++
      [.bl (L.syscallRetAddr - (sasAddr + 0x30#64))] ++ decodeWords [0xa8c17bfd#32, 0xd65f03c0#32]))
    (hret : P.hasCode L.syscallRetAddr syscallRetNonnegWords) {s : State} {uss ssSp ssSize : BitVec 64} {pad : BitVec 32} {Pre F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ (((uss ↦₆₄ ssSp) ∗ ((uss + 8#64) ↦₃₂ 0#32) ∗ ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize)) ∗ stackAt s.sp 0x30) ∗ (F ∗ R))
    (hpc : s.pc = sasAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = uss) (hx1 : s.readReg64 .x1 = 0#64)
    (huss_ne : uss ≠ 0#64) (huss_fit : uss.toNat + 24 ≤ 2 ^ 64) (hsz_lo : 6144 ≤ ssSize.toNat) (hsas0 : s.sigAltStack = {})
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → HbNonVmFields (s.setSigAltStack { sp := ssSp, size := ssSize, ssFlags := 0#32 }) sf →
      SepWP P target_pc sf ((((uss ↦₆₄ ssSp) ∗ ((uss + 8#64) ↦₃₂ 0#32) ∗ ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize)) ∗ stackAt s.sp 0x30) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  have hret' := hret
  refine SepWP.weaken_pre_frame (P' := (((uss ↦₆₄ ssSp) ∗ ((uss + 8#64) ↦₃₂ 0#32) ∗ ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize)) ∗ stackAt s.sp 0x30) ∗ F)
    (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have_instrs hsas_code 0 15
  have hsp_sub_al : ((s.sp + 0xfffffffffffffff0#64) &&& 0xf#64 == 0#64) = true := by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x10#64 hsp_align
  have hu_f : (uss == 0#64) = false := beq_false_of_ne huss_ne
  have hls : ConditionHolds .LS (subsPState64 ssSize 6143#64) = false := cond_ls_subs6143_false hsz_lo
  wp_conv_pre => rw [stackAt_split_cells s.sp 0x20 2 (by decide)]
  unfold_stack_cells 2; clear hret; wp_steps 11
  refine hb_step_cut_pre fun s1 hs1 => ?_
  have ⟨hpc1, hrun1, hsp1, hx0_1, hx1_1, hx8_1, hsas1⟩ :
      s1.pc = sasAddr + 44#64 ∧ s1.status = .Running ∧ s1.sp = s.sp - 16#64 ∧
      s1.readReg64 .x0 = uss ∧ s1.readReg64 .x1 = 0#64 ∧ s1.readReg64 .x8 = 132#64 ∧ s1.sigAltStack = {} := by
    rw [hs1]; refine ⟨by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by simpa [wp_norm, arm64_norm] using hsas0⟩
  have hcs1 : CalleeSavedPreserved ((s.writeReg64 .sp (s.sp - 16#64)).writeReg64 (.gpr 29#5) (s.sp - 16#64)) s1 := by
    rw [hs1]; rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, bv_lin_norm]
  have hnv1 : HbNonVmFields s s1 := by rw [hs1]; hb_nv_rfl s
  clear hs1
  refine SepWP.weaken_pre_frame (P' := stackTAt uss ssSp 0#32 pad ssSize ∗ (optOldStackTAt 0#64 [] ∗ ?_))
    (fun R hm => by dsimp only [stackTAt, optOldStackTAt]; rw [hu_f]; simp only [beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, emp_sepConj]; revert hm; sep_frame) ?_
  refine SepWP.step_svc_sigaltstack (pc := sasAddr + 44#64) (uss := uss) (ssSp := ssSp) (ssSize := ssSize) (uoss := 0#64) (ssFlags := 0#32) (pad := pad) (oldBs₀ := [])
    hpc1 hrun1 hf_11 hx8_1 hx0_1 hx1_1
    (Or.inr ⟨huss_fit, by simp [wp_norm, arm64_norm, hsas1, SigAltStack.onSigStack_default], Or.inr ⟨Or.inl (by decide), by unfold MINSIGSTKSZ; omega⟩⟩)
    (Or.inl rfl) (fun m' => ?_) (hb_evalSvc_sigaltstack hsvc hx8_1)
  dsimp only []
  wp_conv_pre => dsimp only [stackTAt, optOldStackTAt]; rw [hu_f]; simp only [beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, emp_sepConj]
  conv => arg 3; rw [hu_f]; simp only [Bool.false_eq_true, ↓reduceIte,
    show ((0#32 &&& ~~~SS_AUTODISARM) == SS_DISABLE) = false by decide,
    show ((0#32 &&& SS_AUTODISARM) != 0#32) = false by decide]
  refine hb_step_bl_to (pc := sasAddr + 48#64) (dst := L.syscallRetAddr) (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun1]) hf_12 ?_
  rw [show sasAddr + 48#64 + 4#64 = sasAddr + 52#64 by bv_lin]
  refine step_hb_syscallRet_nonneg hret' (ret_pc := sasAddr + 52#64) (x0v := 0#64) (F := ?_)
    (fun R hm => by simp only [wp_norm, arm64_norm, bv_lin_norm] at hm ⊢; revert hm; sep_frame)
    rfl (by simp [wp_norm, arm64_norm, hrun1])
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp1, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x10#64 hsp_align)
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by decide)
    fun s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hx0_2 hnv2 _ => ?_
  have hsp2_eq : s2.sp = s.sp - 16#64 := by simpa [wp_norm, arm64_norm, hsp1] using hsp2
  have h16 : s.sp - 16 = s2.sp := by simpa [BitVec.ofNat_eq_ofNat] using hsp2_eq.symm
  have h08 : s.sp - 8 = s2.sp + 8 := by rw [hsp2_eq]; bv_lin
  have hsp_end : s2.sp + 16#64 = s.sp := by rw [hsp2_eq]; bv_lin
  have hsp_al2_raw : (s2.sp &&& 15#64 == 0#64) = true := hsp_al2
  clear hret' hsp2 hsp2_eq; wp_conv_pre => simp only [wp_norm, arm64_norm, bv_lin_norm, BitVec.ofNat_eq_ofNat]; rw [h16, h08]
  wp_steps 2
  refine SepWP.weaken_pre_frame (P' := (((uss ↦₆₄ ssSp) ∗ ((uss + 8#64) ↦₃₂ 0#32) ∗ ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize)) ∗ stackAt s.sp 0x30) ∗ F)
    (fun R hm => by
      simp only [State.mem_setPC, State.mem_writeReg64]; simp only [wp_norm, arm64_norm, bv_lin_norm, BitVec.ofNat_eq_ofNat] at hm
      rw [← h08, ← h16] at hm; rw [stackAt_split_cells s.sp 0x20 2 (by decide)]; fold_stack_cells) ?_
  have hnv02 : HbNonVmFields (s.setSigAltStack { sp := ssSp, size := ssSize, ssFlags := 0#32 }) s2 := by
    unfold HbNonVmFields at hnv1 hnv2 ⊢
    rcases hnv1 with ⟨hfs1, htr1, htp1, hsa1, _⟩
    rcases hnv2 with ⟨hfs2, htr2, htp2, hsa2, hsas2⟩
    simp only [wp_norm, arm64_norm, State.setSigAltStack] at hfs2 htr2 htp2 hsa2 hsas2 ⊢
    exact ⟨hfs2.trans hfs1, htr2.trans htr1, htp2.trans htp1, hsa2.trans hsa1, hsas2⟩
  refine hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun2])
    (by simp [wp_norm, arm64_norm]) (by simpa [State.spAligned, wp_norm, arm64_norm, hsp_end] using hsp_align)
    ?_ (by simp [wp_norm, arm64_norm, hx0_2]) (hnv02.trans (by hb_nv_rfl s2))
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with ⟨g19_1, g20_1, g21_1, g22_1, g23_1, g24_1, g25_1, g26_1, g27_1, g28_1, _, gv_1⟩
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs2 with ⟨g19_2, g20_2, g21_2, g22_2, g23_2, g24_2, g25_2, g26_2, g27_2, g28_2, _, gv_2⟩
  simp only [wp_norm, arm64_norm] at g19_1 g20_1 g21_1 g22_1 g23_1 g24_1 g25_1 g26_1 g27_1 g28_1 gv_1 g19_2 g20_2 g21_2 g22_2 g23_2 g24_2 g25_2 g26_2 g27_2 g28_2 gv_2
  rw [CalleeSavedPreserved.iff_regs]
  simp [wp_norm, arm64_norm, g19_1, g20_1, g21_1, g22_1, g23_1, g24_1, g25_1, g26_1, g27_1, g28_1, gv_1, g19_2, g20_2, g21_2, g22_2, g23_2, g24_2, g25_2, g26_2, g27_2, g28_2, gv_2]

private theorem fourCells_eq_bytes (a v0 v1 v2 v3 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3)) =
      (a ↦ₛ (unpack64 v0 ++ unpack64 v1 ++ unpack64 v2 ++ unpack64 v3)) := by
  rw [List.append_assoc, List.append_assoc, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [unpack64_length, ← pointsTo64_eq_pointsToBytes]
  rw [show a + 8#64 + 8#64 = a + 16#64 by bv_lin, show a + 16#64 + 8#64 = a + 24#64 by bv_lin]

def hbCustomSigAction (C : HbCliLayout) (S : HbStartupLayout) : SigAction :=
  { handler := S.signalHandlerAddr, flags := 0x0c000004#64, restorer := C.std.restoreRtAddr, mask := 0#64 }

def applyOptSig (actOpt : Option (BitVec 32 × SigAction)) (st : State) : State :=
  match actOpt with | none => st | some (sg, a) => st.setSigAction sg a

theorem hbNonVm_applyOptSig {s0 s1 : State} {actOpt : Option (BitVec 32 × SigAction)}
    (h : HbNonVmFields s0 s1) : HbNonVmFields (applyOptSig actOpt s0) (applyOptSig actOpt s1) := by
  cases actOpt with
  | none => exact h
  | some p => exact ⟨h.1, h.2.1, h.2.2.1, by dsimp [applyOptSig, State.setSigAction]; rw [h.2.2.2.1], h.2.2.2.2⟩

/-- Shared `sigaction` fast-path wrapper (`L.sigactionAddr`, `sig ∈ {13, 11, 7}`) around `__libc_sigaction`. -/
theorem step_hb_sigaction_wrap {P : Program} {L : StdBinaryLayout} {target_pc ret_pc sig act oact : BitVec 64}
    (hsig_fast : hasInstrs P L.sigactionAddr (sigactionFastInstrs L))
    {actOpt : Option (BitVec 32 × SigAction)} {s : State} {Pin : SepProp} {Pout : BitVec 64 → SepProp}
    {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ (Pin ∗ stackAt s.sp 0xe0) ∗ (F ∗ R))
    (hpc : s.pc = L.sigactionAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = sig) (hx1 : s.readReg64 .x1 = act) (hx2 : s.readReg64 .x2 = oact)
    (hsig_mem : sig = 13#64 ∨ sig = 11#64 ∨ sig = 7#64)
    (hinner : ∀ (s0 : State) (G : SepProp),
      s0.pc = L.libcSigactionAddr → s0.status = .Running → s0.sp = s.sp - 80#64 → s0.spAligned = true →
      s0.readReg64 .lr = L.sigactionAddr + 48#64 → s0.readReg64 .x0 = sig → s0.readReg64 .x1 = act → s0.readReg64 .x2 = oact →
      HbNonVmFields s s0 →
      (∀ (s1 : State) (w : BitVec 64), s1.pc = L.sigactionAddr + 48#64 → s1.status = .Running → s1.sp = s0.sp → s1.spAligned = true →
        CalleeSavedPreserved s0 s1 → s1.readReg64 .x0 = 0#64 → HbNonVmFields (applyOptSig actOpt s0) s1 →
        SepWP P target_pc s1 ((Pout w ∗ stackAt s0.sp 0x90) ∗ G) post oom) →
      SepWP P target_pc s0 ((Pin ∗ stackAt s0.sp 0x90) ∗ G) post oom)
    (hnext : ∀ (sf : State) (w : BitVec 64), sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → HbNonVmFields (applyOptSig actOpt s) sf →
      SepWP P target_pc sf ((Pout w ∗ stackAt s.sp 0xe0) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame (P' := (Pin ∗ stackAt s.sp 0xe0) ∗ F) (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have_instrs hsig_fast 0 17
  have hsp_sub_al : ((s.sp + 0xffffffffffffffb0#64) &&& 0xf#64 == 0#64) = true := by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x50#64 hsp_align
  wp_conv_pre => rw [stackAt_split_cells s.sp 0x90 10 (by decide), cells_split_sub s.sp 80 48 4 6, ← memRegion_cells (s.sp - BitVec.ofNat 64 48) 6 (by decide)]
  unfold_stack_cells 4
  have hls1_13 : ConditionHolds .LS (subsPState32 12#32 63#32) = true := by unfold subsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide
  have hls2_13 : ConditionHolds .LS (subsPState32 0xffffffed#32 2#32) = false := by unfold subsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide
  have heq6_13 : ConditionHolds .EQ (subsPState32 13#32 6#32) = false := by unfold subsPState32 ConditionHolds; dsimp [AddWithCarry32]
  have hls1_11 : ConditionHolds .LS (subsPState32 10#32 63#32) = true := by unfold subsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide
  have hls2_11 : ConditionHolds .LS (subsPState32 0xffffffeb#32 2#32) = false := by unfold subsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide
  have heq6_11 : ConditionHolds .EQ (subsPState32 11#32 6#32) = false := by unfold subsPState32 ConditionHolds; dsimp [AddWithCarry32]
  have hls1_7  : ConditionHolds .LS (subsPState32 6#32 63#32) = true := by unfold subsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide
  have hls2_7  : ConditionHolds .LS (subsPState32 0xffffffe7#32 2#32) = false := by unfold subsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide
  have heq6_7  : ConditionHolds .EQ (subsPState32 7#32 6#32) = false := by unfold subsPState32 ConditionHolds; dsimp [AddWithCarry32]
  suffices hbody : ∀ {s0 : State},
      s0.pc = L.libcSigactionAddr → s0.status = .Running → s0.sp = s.sp - 80#64 → s0.spAligned = true →
      s0.readReg64 .lr = L.sigactionAddr + 48#64 → s0.readReg64 .x0 = sig → s0.readReg64 .x1 = act → s0.readReg64 .x2 = oact →
      CalleeSavedPreserved (((s.writeReg64 .sp (s.sp - 80#64)).writeReg64 (.gpr 29#5) (s.sp - 80#64)).writeReg64 (.gpr 19#5) sig) s0 →
      HbNonVmFields s s0 →
      SepWP P target_pc s0 ((Pin ∗ (stackAt (s.sp - 80#64) 0x90 ∗
        ((((s.sp - 80#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 72#64) ↦₆₄ ret_pc) ∗
          ((s.sp - 64#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗ ((s.sp - 56#64) ↦₆₄ s.readReg64 (.gpr 20#5))) ∗
         memRegion (s.sp - 48#64) 48))) ∗ F) post oom by
    rcases hsig_mem with rfl | rfl | rfl <;> (
      wp_steps 11
      refine hb_step_bl_to (pc := L.sigactionAddr + 44#64) (dst := L.libcSigactionAddr) (by hb_wp_simp) (by hb_wp_simp) hf_11 ?_
      refine hbody (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
        (by simpa [State.spAligned, wp_norm, arm64_norm, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x50#64 hsp_align)
        (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
        (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, bv_lin_norm])
        (by hb_nv_rfl s))
  intro s0 hpc0 hrun0 hsp0 hsp_al0 hlr0 hx0_0 hx1_0 hx2_0 hcs0 hnv0
  refine SepWP.weaken_pre_frame (P' := (Pin ∗ stackAt s0.sp 0x90) ∗ ?_)
    (fun R hm => by rw [hsp0]; revert hm; sep_frame) ?_
  refine hinner s0 _ hpc0 hrun0 hsp0 hsp_al0 hlr0 hx0_0 hx1_0 hx2_0 hnv0 fun s1 w hpc1 hrun1 hsp1 hsp_al1 hcs1 hx0_1 hnv1 => ?_
  have hsp1_eq : s1.sp = s.sp - 80#64 := hsp1.trans hsp0
  have hc0 : s.sp - 80#64 = s1.sp := hsp1_eq.symm
  have hc1 : s.sp - 72#64 = s1.sp + 8#64 := by rw [hsp1_eq]; bv_lin
  have hc2 : s.sp - 64#64 = s1.sp + 16#64 := by rw [hsp1_eq]; bv_lin
  have hc3 : s.sp - 56#64 = s1.sp + 24#64 := by rw [hsp1_eq]; bv_lin
  have hsp_end : s1.sp + 80#64 = s.sp := by rw [hsp1_eq]; bv_lin
  have hsp_al1_raw : (s1.sp &&& 15#64 == 0#64) = true := hsp_al1
  have hsp_add_al : ((s1.sp + 80#64) &&& 15#64 == 0#64) = true := by simp only [beq_iff_eq] at hsp_al1_raw ⊢; bv_bits
  clear hsp1 hsp1_eq; wp_conv_pre => rw [hc0, hc1, hc2, hc3]
  wp_steps 5
  refine SepWP.weaken_pre_frame (P' := (Pout w ∗ stackAt s.sp 0xe0) ∗ F)
    (fun R hm => by
      simp only [State.mem_setPC, State.mem_writeReg64]
      rw [← hc3, ← hc2, ← hc1, ← hc0, hsp0] at hm
      simp only [wp_norm, arm64_norm] at hm
      rw [stackAt_split_cells s.sp 0x90 10 (by decide), cells_split_sub s.sp 80 48 4 6, ← memRegion_cells (s.sp - BitVec.ofNat 64 48) 6 (by decide)]
      fold_stack_cells) ?_
  refine hnext _ w (by hb_wp_simp) (by simp [wp_norm, arm64_norm, hrun1]) (by hb_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp_end] using hsp_align) ?_ (by hb_wp_simp)
    ((hbNonVm_applyOptSig hnv0).trans (hnv1.trans (by hb_nv_rfl s1)))
  rcases (CalleeSavedPreserved.iff_regs _ _).mp (hcs0.trans hcs1) with ⟨_, _, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩
  simp only [wp_norm, arm64_norm] at g21 g22 g23 g24 g25 g26 g27 g28 gv
  rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, g21, g22, g23, g24, g25, g26, g27, g28, gv]

@[local simp] private theorem getSigAction_w64 (s : State) (r : Reg) (v : BitVec 64) (sg : BitVec 32) : (s.writeReg64 r v).getSigAction sg = s.getSigAction sg := rfl
@[local simp] private theorem getSigAction_w32 (s : State) (r : Reg) (v : BitVec 32) (sg : BitVec 32) : (s.writeReg32 r v).getSigAction sg = s.getSigAction sg := by simp [State.writeReg32]
@[local simp] private theorem getSigAction_ps (s : State) (p : PState) (sg : BitVec 32) : (s.setPState p).getSigAction sg = s.getSigAction sg := rfl
@[local simp] private theorem getSigAction_pc (s : State) (p : BitVec 64) (sg : BitVec 32) : (s.setPC p).getSigAction sg = s.getSigAction sg := rfl
@[local simp] private theorem getSigAction_mem (s : State) (m : Memory) (sg : BitVec 32) : (s.setMem m).getSigAction sg = s.getSigAction sg := rfl

local macro "peelS " k:num : tactic => `(tactic| iterate $k (refine peel_instrS (by simp only [wp_norm]; rfl) fun _ => ?_))
local macro "peel1 " h:ident : tactic => `(tactic| refine peel_instrS (by simp only [wp_norm]; rfl) fun $h => ?_)
theorem hb_step_cut {P : Program} {t : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (k : ∀ s', s' = s → SepWP P t s' Pre post oom) : SepWP P t s Pre post oom := k s rfl

set_option maxHeartbeats 400000 in
private theorem step_hb_libcSigaction_ign {P : Program} {L : StdBinaryLayout} {target_pc ret_pc : BitVec 64}
    (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc) (hhead : P.hasCode L.libcSigactionAddr libcSigactionHeadWords)
    (htail : hasInstrs P (L.libcSigactionAddr + 0xfc#64) (libcSigactionIgnTailInstrs L))
    (hret : P.hasCode L.syscallRetAddr syscallRetNonnegWords) (hmemcpy : hasInstrs P L.memcpyAddr hbMemcpyInstrs)
    {s : State} {act oact v0 v1 v17 : BitVec 64} {G : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = L.libcSigactionAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hsp_lo : 0x90 ≤ s.sp.toNat)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = 13#64) (hx1 : s.readReg64 .x1 = act) (hx2 : s.readReg64 .x2 = oact)
    (hact_ne : act ≠ 0#64) (hoact_ne : oact ≠ 0#64) (hsig0 : s.getSigAction 13#32 = {})
    (hnext : ∀ (sf : State) (v17' : BitVec 64), sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → HbNonVmFields (s.setSigAction 13#32 (sigpipeIgnAction L)) sf →
      SepWP P target_pc sf (((((act ↦₆₄ 1#64) ∗ ((act + 8#64) ↦₆₄ 0#64) ∗ ((act + 0x88#64) ↦₆₄ 0x10000000#64)) ∗
        ((oact ↦₆₄ 0#64) ∗ ((oact + 8#64) ↦₆₄ 0#64) ∗ ((oact + 0x88#64) ↦₆₄ v17'))) ∗ stackAt s.sp 0x90) ∗ G) post oom) :
    SepWP P target_pc s (((((act ↦₆₄ 1#64) ∗ ((act + 8#64) ↦₆₄ 0#64) ∗ ((act + 0x88#64) ↦₆₄ 0x10000000#64)) ∗
      ((oact ↦₆₄ v0) ∗ ((oact + 8#64) ↦₆₄ v1) ∗ ((oact + 0x88#64) ↦₆₄ v17))) ∗ stackAt s.sp 0x90) ∗ G) post oom := by
  have hret' := hret
  refine SepWP.weaken_pre_frame
    (P' := (((act ↦₆₄ 1#64) ∗ ((act + 8#64) ↦₆₄ 0#64) ∗ ((act + 0x88#64) ↦₆₄ 0x10000000#64)) ∗
      ((oact ↦₆₄ v0) ∗ memRegion (oact + 8#64) 8 ∗ ((oact + 0x88#64) ↦₆₄ v17)) ∗ stackAt s.sp 0x90) ∗ G)
    (fun R hm => by rw [memRegion_eight]; revert hm; sep_entail) ?_
  have hp := htail; dsimp only [libcSigactionIgnTailInstrs] at hp; generalize hb : L.libcSigactionAddr + 0xfc#64 = b at hp; revert hp
  refine peel_instr0 fun _ => ?_; peelS 14; peel1 hf15; peelS 7; peel1 hf23; peelS 5; peel1 hf29; peelS 11; peel1 hf41; peelS 1; intro _
  have hsp_sub_al : ((s.sp + 0xffffffffffffff90#64) &&& 0xf#64 == 0#64) = true := by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x70#64 hsp_align
  have hact_f : (act == 0#64) = false := beq_false_of_ne hact_ne
  wp_conv_pre => rw [stackAt_split_cells s.sp 0x20 14 (by decide), cells_split_sub s.sp 112 40 9 5, cells_split_sub s.sp 40 32 1 4, ← memRegion_cells (s.sp - BitVec.ofNat 64 40) 1 (by decide)]; simp only [Nat.reduceMul]; simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun w10 => SepWP.exists_elim fun w11 => SepWP.exists_elim fun w12 => SepWP.exists_elim fun w13 => ?_; iterate 9 (refine SepWP.exists_elim fun _ => ?_)
  clear hret; wp_steps 12; clear hhead; wp_steps 15
  refine hb_step_bl_to (pc := b + 60#64) (dst := L.memcpyAddr) (by hb_wp_simp) (by hb_wp_simp) hf15 ?_
  refine hb_step_cut fun s0 hs0 => ?_
  have ⟨hpc0, hrun0, hsp0, hsp_al0, hlr0, hx0_0, hx1_0, hx2_0, hx19_0, hx20_0, hx21_0⟩ :
      s0.pc = L.memcpyAddr ∧ s0.status = .Running ∧ s0.sp = s.sp - 112#64 ∧ s0.spAligned = true ∧
      s0.readReg64 .lr = L.libcSigactionAddr + 316#64 ∧ s0.readReg64 .x0 = s.sp - 40#64 ∧ s0.readReg64 .x1 = act + 8#64 ∧
      s0.readReg64 .x2 = 8#64 ∧ s0.readReg64 .x19 = s.sp - 64#64 ∧ s0.readReg64 .x20 = oact ∧ s0.readReg64 .x21 = 13#64 := by
    rw [hs0]; refine ⟨by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, ?_, by rw [← hb]; hb_wp_simp,
      by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp⟩
    simpa [State.spAligned, wp_norm, arm64_norm, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x70#64 hsp_align
  have hcs0 : CalleeSavedPreserved (((((s.writeReg64 .sp (s.sp - 112#64)).writeReg64 (.gpr 29#5) (s.sp - 112#64)).writeReg64 (.gpr 19#5) (s.sp - 64#64)).writeReg64 (.gpr 20#5) oact).writeReg64 (.gpr 21#5) 13#64) s0 := by
    rw [hs0]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, bv_lin_norm]
  have hnv0 : HbNonVmFields s s0 := by rw [hs0]; hb_nv_rfl s
  clear hs0 hf15 hpc hlr hx0 hx1 hx2 hsp_sub_al hact_f
  refine step_hb_memcpy8 hmemcpy (ret_pc := L.libcSigactionAddr + 316#64) (dst := s.sp - 40#64) (src := act + 8#64) (v := 0#64) (F := ?_)
    (fun R hm => by simp only [wp_norm, arm64_norm] at hm ⊢; revert hm; sep_frame)
    hpc0 hrun0 hlr0 hx0_0 hx1_0 hx2_0 fun s1 hpc1 hrun1 hsp1 hcs1 _ hnv1 => ?_
  have hsp1_eq : s1.sp = s.sp - 112#64 := hsp1.trans hsp0
  have hnv01 : HbNonVmFields s s1 := hnv0.trans hnv1
  have hsig1 : s1.getSigAction 13#32 = {} := by rw [State.getSigAction, hnv01.2.2.2.1, ← State.getSigAction, hsig0]
  have hx19_1 : s1.readReg64 .x19 = s.sp - 64#64 := hcs1.1.trans hx19_0
  have hx20_1 : s1.readReg64 .x20 = oact := hcs1.2.1.trans hx20_0
  have hx21_1 : s1.readReg64 .x21 = 13#64 := hcs1.2.2.1.trans hx21_0
  have hpc1_b : s1.pc = b + 64#64 := by rw [hpc1, ← hb]; bv_lin
  have hsp_al1 : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_al0
  clear hpc1
  have ho_bne : (oact != 0#64) = true := bne_iff_ne.mpr hoact_ne
  have hk_f : ((s.sp - 64#64) == 0#64) = false := beq_false_of_ne (by bv_omega)
  have ho_f : ((s1.sp + 80#64) == 0#64) = false := beq_false_of_ne (by rw [hsp1_eq]; bv_omega)
  have ka1 : (s.sp - 64#64) + 8#64 = s.sp - 56#64 := by bv_lin
  have ka2 : (s.sp - 64#64) + 16#64 = s.sp - 48#64 := by bv_lin
  have ka3 : (s.sp - 64#64) + 24#64 = s.sp - 40#64 := by bv_lin
  have ko0 : s1.sp + 80#64 = s.sp - 32#64 := by rw [hsp1_eq]; bv_lin
  have ko1 : s1.sp + 80#64 + 8#64 = s.sp - 24#64 := by rw [hsp1_eq]; bv_lin
  have ko2 : s1.sp + 80#64 + 16#64 = s.sp - 16#64 := by rw [hsp1_eq]; bv_lin
  have ko3 : s1.sp + 80#64 + 24#64 = s.sp - 8#64 := by rw [hsp1_eq]; bv_lin
  have oa1 : s1.sp + 80#64 + 8#64 = s1.sp + 88#64 := by bv_lin
  have oa2 : s1.sp + 80#64 + 16#64 = s1.sp + 96#64 := by bv_lin
  have oa3 : s1.sp + 80#64 + 24#64 = s1.sp + 104#64 := by bv_lin
  wp_steps 7
  refine SepWP.weaken_pre_frame
    (P' := kSigActionAt (s.sp - 64#64) 1#64 0x14000000#64 L.restoreRtAddr 0#64 ∗
      (optOldSigActionAt (s1.sp + 80#64) (unpack64 w10 ++ unpack64 w11 ++ unpack64 w12 ++ unpack64 w13) ∗ ?_))
    (fun R hm => by
      dsimp only [kSigActionAt, optOldSigActionAt]; rw [hk_f, ho_f]
      simp only [Bool.false_eq_true, ↓reduceIte, ← fourCells_eq_bytes]; rw [ka1, ka2, ka3, ko1, ko2, ko3, ko0]; revert hm; sep_frame) ?_
  refine SepWP.step_svc_rt_sigaction (pc := b + 92#64) (signum := 13#32) (act := s.sp - 64#64)
    (handler := 1#64) (flags := 0x14000000#64) (restorer := L.restoreRtAddr) (mask := 0#64)
    (oldact := s1.sp + 80#64) (oldBs₀ := unpack64 w10 ++ unpack64 w11 ++ unpack64 w12 ++ unpack64 w13)
    (by hb_wp_simp) (by simp [wp_norm, arm64_norm, hrun1]) hf23 (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
    (by simp [wp_norm, arm64_norm, bv_lin_norm, hsp1_eq]) (by hb_wp_simp) (by decide) (by decide)
    (Or.inr ⟨by decide, by decide, by bv_omega, Or.inr rfl⟩) (Or.inr ⟨by rw [hsp1_eq]; bv_omega, by simp [unpack64_length]⟩)
    (fun m' => ?_) (hb_evalSvc_rt_sigaction hsvc (by hb_wp_simp))
  dsimp only []
  have htoBytes_emp : ({} : SigAction).toBytes = unpack64 0#64 ++ unpack64 0#64 ++ unpack64 0#64 ++ unpack64 0#64 := rfl
  wp_conv_pre =>
    dsimp only [kSigActionAt, optOldSigActionAt]
    simp only [getSigAction_w64, getSigAction_ps, getSigAction_pc, hsig1, hk_f, ho_f, Bool.false_eq_true, ↓reduceIte]
    rw [htoBytes_emp, ← fourCells_eq_bytes, ka1, ka2, ka3, oa1, oa2, oa3]
  conv => arg 3; rw [hk_f]; simp only [Bool.false_eq_true, ↓reduceIte, show (0#64 &&& ~~~SIG_UNBLOCKABLE_MASK) = 0#64 from rfl]
  clear hf23; wp_steps 11
  refine hb_step_bl_to (pc := b + 164#64) (dst := L.memcpyAddr) (by hb_wp_simp) (by simp [wp_norm, arm64_norm, hrun1]) hf41 ?_
  refine hb_step_cut fun s2 hs2 => ?_
  have ⟨hpc2, hrun2, hsp2, hsp_al2, hlr2, hx0_2, hx1_2, hx2_2, hx19_2⟩ :
      s2.pc = L.memcpyAddr ∧ s2.status = .Running ∧ s2.sp = s1.sp ∧ s2.spAligned = true ∧
      s2.readReg64 .lr = L.libcSigactionAddr + 420#64 ∧ s2.readReg64 .x0 = oact + 8#64 ∧ s2.readReg64 .x1 = s1.sp + 104#64 ∧
      s2.readReg64 .x2 = 8#64 ∧ s2.readReg64 .x19 = 0#64 := by
    rw [hs2]; refine ⟨by hb_wp_simp, by simp [wp_norm, arm64_norm, hrun1], by hb_wp_simp,
      by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al1, by rw [← hb]; hb_wp_simp,
      by hb_wp_simp, by simp [wp_norm, arm64_norm, bv_lin_norm, hsp1_eq], by hb_wp_simp, by hb_wp_simp⟩
  have hcs2 : CalleeSavedPreserved (s1.writeReg64 (.gpr 19#5) 0#64) s2 := by
    rw [hs2]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]
  have hnv12 : HbNonVmFields (s1.setSigAction 13#32 (sigpipeIgnAction L)) s2 := by rw [hs2]; hb_nv_rfl _
  clear hs2 hf41
  refine step_hb_memcpy8 hmemcpy (ret_pc := L.libcSigactionAddr + 420#64) (dst := oact + 8#64) (src := s1.sp + 104#64) (v := 0#64) (F := ?_)
    (fun R hm => by simp only [wp_norm, arm64_norm] at hm ⊢; revert hm; sep_frame)
    hpc2 hrun2 hlr2 hx0_2 hx1_2 hx2_2 fun s3 hpc3 hrun3 hsp3 hcs3 _ hnv23 => ?_
  have hsp3_eq : s3.sp = s.sp - 112#64 := hsp3.trans (hsp2.trans hsp1_eq)
  have hx19_3 : s3.readReg64 .x19 = 0#64 := hcs3.1.trans hx19_2
  have hpc3_b : s3.pc = b + 168#64 := by rw [hpc3, ← hb]; bv_lin
  clear hpc3; wp_steps 2
  refine hb_step_bl_to (pc := b + 116#64) (dst := L.syscallRetAddr) (by hb_wp_simp) (by simp [wp_norm, arm64_norm, hrun3]) hf29 ?_
  refine hb_step_cut fun s3' hs3' => ?_
  have hsp3' : s3'.sp = s.sp - 112#64 := by rw [hs3']; simpa [wp_norm, arm64_norm] using hsp3_eq
  refine step_hb_syscallRet_nonneg hret' (ret_pc := b + 120#64) (x0v := 0#64) (F := ?_)
    (fun R hm => by rw [hsp3']; revert hm; sep_frame)
    (by rw [hs3']; hb_wp_simp) (by rw [hs3']; simp [wp_norm, arm64_norm, hrun3])
    (by rw [State.spAligned, hsp3']; simpa [State.spAligned, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x70#64 hsp_align)
    (by rw [hs3']; hb_wp_simp) (by rw [hs3']; hb_wp_simp) (by decide)
    fun s4 hpc4 hrun4 hsp4 hsp_al4 hcs4_raw hx0_4 hnv4_raw _ => ?_
  have hcs4 : CalleeSavedPreserved s3 s4 := by rw [hs3'] at hcs4_raw; simpa [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm] using hcs4_raw
  have hnv34 : HbNonVmFields s3 s4 := by rw [hs3'] at hnv4_raw; simpa [hbNonVm_w64_l, hbNonVm_pc_l] using hnv4_raw
  have hsp4_eq : s4.sp = s.sp - 112#64 := hsp4.trans hsp3'
  clear hs3' hsp4 hret' hf29 hmemcpy
  have hsp_al4_raw : (s4.sp &&& 15#64 == 0#64) = true := hsp_al4
  have hsp_add_al : ((s4.sp + 112#64) &&& 15#64 == 0#64) = true := by simp only [beq_iff_eq] at hsp_al4_raw ⊢; bv_bits
  have e0 : s.sp - 112#64 = s4.sp := hsp4_eq.symm
  have e1 : s.sp - 104#64 = s4.sp + 8#64 := by rw [hsp4_eq]; bv_lin
  have e2 : s.sp - 96#64 = s4.sp + 16#64 := by rw [hsp4_eq]; bv_lin
  have e3 : s.sp - 88#64 = s4.sp + 24#64 := by rw [hsp4_eq]; bv_lin
  have e4 : s.sp - 80#64 = s4.sp + 32#64 := by rw [hsp4_eq]; bv_lin
  have hsp_end : s4.sp + 112#64 = s.sp := by rw [hsp4_eq]; bv_lin
  clear hsp4_eq; wp_conv_pre => rw [e0, e1, e2, e3, e4]
  wp_steps 4
  refine SepWP.weaken_pre_frame
    (P' := ((((act ↦₆₄ 1#64) ∗ ((act + 8#64) ↦₆₄ 0#64) ∗ ((act + 0x88#64) ↦₆₄ 0x10000000#64)) ∗
      ((oact ↦₆₄ 0#64) ∗ ((oact + 8#64) ↦₆₄ 0#64) ∗ ((oact + 0x88#64) ↦₆₄ _))) ∗ stackAt s.sp 0x90) ∗ G)
    (fun R hm => by
      simp only [State.mem_setPC, State.mem_writeReg64] at hm ⊢
      rw [← e4, ← e3, ← e2, ← e1, ← e0, ← oa1, ← oa2, ← oa3, ko1, ko2, ko3, ko0, hsp3'] at hm
      rw [stackAt_split_cells s.sp 0x20 14 (by decide)]; fold_stack_cells) ?_
  have hnv_sig : HbNonVmFields (s.setSigAction 13#32 (sigpipeIgnAction L)) (s1.setSigAction 13#32 (sigpipeIgnAction L)) :=
    hbNonVm_applyOptSig (actOpt := some (13#32, sigpipeIgnAction L)) hnv01
  refine hnext _ _ (by hb_wp_simp) (by simp [wp_norm, arm64_norm, hrun4]) (by hb_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp_end] using hsp_align)
    (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm] at hcs0 hcs1 hcs2 hcs3 hcs4 ⊢; simp [hcs0, hcs1, hcs2, hcs3, hcs4])
    (by simp [wp_norm, arm64_norm, hx0_4])
    (hnv_sig.trans (hnv12.trans (hnv23.trans (hnv34.trans (by hb_nv_rfl s4)))))

set_option maxHeartbeats 400000 in
/-- Step `signal(13, SIG_IGN)` (`L.signalAddr` with symbolic `bl L.sigactionAddr` at `+0x44`). -/
theorem step_hb_signal_sigpipe_ign {P : Program} {L : StdBinaryLayout} {target_pc ret_pc : BitVec 64}
    (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc)
    (hsig_code : hasInstrs P L.signalAddr (decodeWords (signalWords.take 17) ++ [.bl (L.sigactionAddr - (L.signalAddr + 0x44#64))] ++ decodeWords (signalWords.drop 18)))
    (hsig_fast : hasInstrs P L.sigactionAddr (sigactionFastInstrs L)) (hhead : P.hasCode L.libcSigactionAddr libcSigactionHeadWords)
    (htail : hasInstrs P (L.libcSigactionAddr + 0xfc#64) (libcSigactionIgnTailInstrs L))
    (hret : P.hasCode L.syscallRetAddr syscallRetNonnegWords) (hmemcpy : hasInstrs P L.memcpyAddr hbMemcpyInstrs)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ stackAt s.sp 0x220 ∗ (F ∗ R))
    (hpc : s.pc = L.signalAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hsp_lo : 0x220 ≤ s.sp.toNat)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = 13#64) (hx1 : s.readReg64 .x1 = 1#64) (hsig0 : s.getSigAction 13#32 = {})
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → HbNonVmFields (s.setSigAction 13#32 (sigpipeIgnAction L)) sf →
      SepWP P target_pc sf (stackAt s.sp 0x220 ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame (P' := stackAt s.sp 0x220 ∗ F) (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have_instrs hsig_code 0 23
  have hsp_sub_al : ((s.sp + 0xfffffffffffffec0#64) &&& 0xf#64 == 0#64) = true := by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x140#64 hsp_align
  wp_conv_pre => rw [stackAt_split_cells s.sp 0xe0 40 (by decide), cells_split_sub s.sp 320 288 4 36, cells_split_sub s.sp 288 168 15 21, cells_split_sub s.sp 168 160 1 20, cells_split_sub s.sp 160 152 1 19, ← memRegion_cells (s.sp - BitVec.ofNat 64 288) 15 (by decide), ← memRegion_cells (s.sp - BitVec.ofNat 64 160) 1 (by decide)]
  have hhead' := hhead; have hret' := hret; unfold_stack_cells 24; clear hhead hret; wp_steps 17
  refine hb_step_bl_to (pc := L.signalAddr + 68#64) (dst := L.sigactionAddr) (by hb_wp_simp) (by hb_wp_simp) hf_17 ?_
  refine hb_step_cut fun s0 hs0 => ?_
  have ⟨hpc0, hrun0, hsp0, hsp_al0, hlr0, hx0_0, hx1_0, hx2_0⟩ :
      s0.pc = L.sigactionAddr ∧ s0.status = .Running ∧ s0.sp = s.sp - 320#64 ∧ s0.spAligned = true ∧
      s0.readReg64 .lr = L.signalAddr + 72#64 ∧ s0.readReg64 .x0 = 13#64 ∧ s0.readReg64 .x1 = s.sp - 152#64 ∧ s0.readReg64 .x2 = s.sp - 304#64 := by
    rw [hs0]; refine ⟨by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, ?_,
      by rw [show L.signalAddr + 68#64 + 4#64 = L.signalAddr + 72#64 by bv_lin]; hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp⟩
    simpa [State.spAligned, wp_norm, arm64_norm, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x140#64 hsp_align
  have hcs0 : CalleeSavedPreserved ((s.writeReg64 .sp (s.sp - 320#64)).writeReg64 (.gpr 29#5) (s.sp - 320#64)) s0 := by
    rw [hs0]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, bv_lin_norm]
  have hnv0 : HbNonVmFields s s0 := by rw [hs0]; hb_nv_rfl s
  clear hs0 hf_17 hpc hlr hx0 hx1 hsp_sub_al
  have ha1 : (s.sp - 152#64) + 8#64 = s.sp - 144#64 := by bv_lin
  have ha2 : (s.sp - 152#64) + 0x88#64 = s.sp - 16#64 := by bv_lin
  have ho1 : (s.sp - 304#64) + 8#64 = s.sp - 296#64 := by bv_lin
  have ho2 : (s.sp - 304#64) + 0x88#64 = s.sp - 168#64 := by bv_lin
  refine step_hb_sigaction_wrap hsig_fast (ret_pc := L.signalAddr + 72#64) (sig := 13#64) (act := s.sp - 152#64) (oact := s.sp - 304#64)
    (actOpt := some (13#32, sigpipeIgnAction L))
    (Pin := ((s.sp - 152#64) ↦₆₄ 1#64) ∗ (((s.sp - 152#64) + 8#64) ↦₆₄ 0#64) ∗ (((s.sp - 152#64) + 0x88#64) ↦₆₄ 0x10000000#64) ∗
      (((s.sp - 304#64) ↦₆₄ _) ∗ (((s.sp - 304#64) + 8#64) ↦₆₄ _) ∗ (((s.sp - 304#64) + 0x88#64) ↦₆₄ _)))
    (Pout := fun w => (((s.sp - 152#64) ↦₆₄ 1#64) ∗ (((s.sp - 152#64) + 8#64) ↦₆₄ 0#64) ∗ (((s.sp - 152#64) + 0x88#64) ↦₆₄ 0x10000000#64)) ∗
      (((s.sp - 304#64) ↦₆₄ 0#64) ∗ (((s.sp - 304#64) + 8#64) ↦₆₄ 0#64) ∗ (((s.sp - 304#64) + 0x88#64) ↦₆₄ w)))
    (F := ?_) (fun R hm => by rw [ha1, ha2, ho1, ho2, hsp0]; revert hm; sep_frame)
    hpc0 hrun0 hsp_al0 hlr0 hx0_0 hx1_0 hx2_0 (Or.inl rfl)
    (fun s0' G hpc0' hrun0' hsp0' hsp_al0' hlr0' hx0_0' hx1_0' hx2_0' hnv0' hk => by
      have hnv_s0' : HbNonVmFields s s0' := hnv0.trans hnv0'
      have hsig_s0' : s0'.getSigAction 13#32 = {} := by rw [State.getSigAction, hnv_s0'.2.2.2.1, ← State.getSigAction, hsig0]
      refine SepWP.weaken_pre_frame (fun R hm => by ac_nf at hm ⊢)
        (step_hb_libcSigaction_ign hsvc hhead' htail hret' hmemcpy hpc0' hrun0' hsp_al0' (by rw [hsp0', hsp0]; bv_omega)
          hlr0' hx0_0' hx1_0' hx2_0' (by bv_omega) (by bv_omega) hsig_s0' hk))
    fun s1 v17' hpc1 hrun1 hsp1 hsp_al1 hcs1 hx0_1 hnv1 => ?_
  clear hhead' hret' hmemcpy
  have hsp1_eq : s1.sp = s.sp - 320#64 := hsp1.trans hsp0
  have hc0 : s.sp - 320#64 = s1.sp := hsp1_eq.symm
  have hc1 : s.sp - 312#64 = s1.sp + 8#64 := by rw [hsp1_eq]; bv_lin
  have hc2 : s.sp - 304#64 = s1.sp + 16#64 := by rw [hsp1_eq]; bv_lin
  have hsp_end : s1.sp + 320#64 = s.sp := by rw [hsp1_eq]; bv_lin
  have hsp_al1_raw : (s1.sp &&& 15#64 == 0#64) = true := hsp_al1
  have hsp_add_al : ((s1.sp + 320#64) &&& 15#64 == 0#64) = true := by simp only [beq_iff_eq] at hsp_al1_raw ⊢; bv_bits
  have hge0 : ConditionHolds .GE (subsPState32 0#32 0#32) = true := by unfold subsPState32 ConditionHolds; dsimp [AddWithCarry32]; decide
  clear hsp1 hsp1_eq; wp_conv_pre => rw [ha1, ha2, ho1, ho2, hc0, hc1, hc2]
  wp_steps 5
  refine SepWP.weaken_pre_frame (P' := stackAt s.sp 0x220 ∗ F)
    (fun R hm => by
      simp only [State.mem_setPC, State.mem_setPState, State.mem_writeReg64] at hm ⊢
      rw [← hc2, ← hc1, ← hc0, hsp0] at hm
      rw [stackAt_split_cells s.sp 0xe0 40 (by decide), cells_split_sub s.sp 320 288 4 36, cells_split_sub s.sp 288 168 15 21, cells_split_sub s.sp 168 160 1 20, cells_split_sub s.sp 160 152 1 19, ← memRegion_cells (s.sp - BitVec.ofNat 64 288) 15 (by decide), ← memRegion_cells (s.sp - BitVec.ofNat 64 160) 1 (by decide)]
      fold_stack_cells) ?_
  have hnv_sig : HbNonVmFields (s.setSigAction 13#32 (sigpipeIgnAction L)) (s0.setSigAction 13#32 (sigpipeIgnAction L)) :=
    hbNonVm_applyOptSig (actOpt := some (13#32, sigpipeIgnAction L)) hnv0
  refine hnext _ (by hb_wp_simp) (by simp [wp_norm, arm64_norm, hrun1]) (by hb_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp_end] using hsp_align)
    (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm] at hcs0 hcs1 ⊢; simp [hcs0, hcs1])
    (by hb_wp_simp) (hnv_sig.trans (hnv1.trans (by hb_nv_rfl s1)))

set_option maxHeartbeats 400000 in
/-- Step `__libc_sigaction(sig, 0, oact)` (`sig ∈ {11, 7}`, `oact ≠ 0`) when `s.getSigAction (sig.truncate 32) = {}`. -/
theorem step_hb_libcSigaction_probe {P : Program} {L : StdBinaryLayout} {target_pc ret_pc sig : BitVec 64}
    (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc) (hhead : P.hasCode L.libcSigactionAddr libcSigactionHeadWords)
    (htail : hasInstrs P (L.libcSigactionAddr + 0xfc#64) (libcSigactionIgnTailInstrs L))
    (hret : P.hasCode L.syscallRetAddr syscallRetNonnegWords) (hmemcpy : hasInstrs P L.memcpyAddr hbMemcpyInstrs)
    {s : State} {oact v0 v1 v17 : BitVec 64} {G : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = L.libcSigactionAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hsp_lo : 0x90 ≤ s.sp.toNat)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = sig) (hx1 : s.readReg64 .x1 = 0#64) (hx2 : s.readReg64 .x2 = oact)
    (hsig_mem : sig = 11#64 ∨ sig = 7#64) (hoact_ne : oact ≠ 0#64) (hsig0 : s.getSigAction (sig.truncate 32) = {})
    (hnext : ∀ (sf : State) (v17' : BitVec 64), sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → HbNonVmFields s sf →
      SepWP P target_pc sf ((((oact ↦₆₄ 0#64) ∗ ((oact + 8#64) ↦₆₄ 0#64) ∗ ((oact + 0x88#64) ↦₆₄ v17')) ∗ stackAt s.sp 0x90) ∗ G) post oom) :
    SepWP P target_pc s ((((oact ↦₆₄ v0) ∗ ((oact + 8#64) ↦₆₄ v1) ∗ ((oact + 0x88#64) ↦₆₄ v17)) ∗ stackAt s.sp 0x90) ∗ G) post oom := by
  have hret' := hret
  refine SepWP.weaken_pre_frame
    (P' := (((oact ↦₆₄ v0) ∗ memRegion (oact + 8#64) 8 ∗ ((oact + 0x88#64) ↦₆₄ v17)) ∗ stackAt s.sp 0x90) ∗ G)
    (fun R hm => by rw [memRegion_eight]; revert hm; sep_entail) ?_
  have hp := htail; dsimp only [libcSigactionIgnTailInstrs] at hp; generalize hb : L.libcSigactionAddr + 0xfc#64 = b at hp; revert hp
  refine peel_instr0 fun _ => ?_; peelS 22; peel1 hf23; peelS 5; peel1 hf29; peelS 11; peel1 hf41; peelS 1; intro _
  have hsp_sub_al : ((s.sp + 0xffffffffffffff90#64) &&& 0xf#64 == 0#64) = true := by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x70#64 hsp_align
  have hsxtw : (sig >>> 0 &&& 0xffffffff#64 ||| (if sig.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&& 0xffffffff00000000#64) = sig := by
    rcases hsig_mem with rfl | rfl <;> decide
  have hlo : 1 ≤ (sig.truncate 32).toNat := by rcases hsig_mem with rfl | rfl <;> decide
  have hhi : (sig.truncate 32).toNat ≤ 64 := by rcases hsig_mem with rfl | rfl <;> decide
  have ho_bne : (oact != 0#64) = true := bne_iff_ne.mpr hoact_ne
  wp_conv_pre => rw [stackAt_split_cells s.sp 0x20 14 (by decide), cells_split_sub s.sp 112 32 10 4]; simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun w10 => SepWP.exists_elim fun w11 => SepWP.exists_elim fun w12 => SepWP.exists_elim fun w13 => ?_
  iterate 10 (refine SepWP.exists_elim fun _ => ?_)
  clear hret; wp_steps 9; clear hhead
  have hpc_b17 : L.libcSigactionAddr + 320#64 = b + 68#64 := by rw [← hb]; bv_lin
  conv => arg 3; rw [hpc_b17]
  wp_steps 6
  have ho_f : ((s.sp - 32#64) == 0#64) = false := beq_false_of_ne (by bv_omega)
  have ko1 : (s.sp - 32#64) + 8#64 = s.sp - 24#64 := by bv_lin
  have ko2 : (s.sp - 32#64) + 16#64 = s.sp - 16#64 := by bv_lin
  have ko3 : (s.sp - 32#64) + 24#64 = s.sp - 8#64 := by bv_lin
  refine SepWP.weaken_pre_frame
    (P' := kSigActionAt 0#64 0#64 0#64 0#64 0#64 ∗
      (optOldSigActionAt (s.sp - 32#64) (unpack64 w10 ++ unpack64 w11 ++ unpack64 w12 ++ unpack64 w13) ∗ ?_))
    (fun R hm => by
      dsimp only [kSigActionAt, optOldSigActionAt]; rw [ho_f]
      simp only [beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, emp_sepConj, ← fourCells_eq_bytes]
      rw [ko1, ko2, ko3]; revert hm; sep_frame) ?_
  refine SepWP.step_svc_rt_sigaction (pc := b + 92#64) (signum := sig.truncate 32) (act := 0#64)
    (handler := 0#64) (flags := 0#64) (restorer := 0#64) (mask := 0#64)
    (oldact := s.sp - 32#64) (oldBs₀ := unpack64 w10 ++ unpack64 w11 ++ unpack64 w12 ++ unpack64 w13)
    (by hb_wp_simp) (by hb_wp_simp) hf23 (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
    (by hb_wp_simp) (by hb_wp_simp) hlo hhi (Or.inl rfl)
    (Or.inr ⟨by bv_omega, by simp [unpack64_length]⟩) (fun m' => ?_)
    (hb_evalSvc_rt_sigaction hsvc (by hb_wp_simp))
  dsimp only []
  have htoBytes_emp : ({} : SigAction).toBytes = unpack64 0#64 ++ unpack64 0#64 ++ unpack64 0#64 ++ unpack64 0#64 := rfl
  wp_conv_pre =>
    dsimp only [kSigActionAt, optOldSigActionAt]
    simp only [getSigAction_w64, getSigAction_ps, getSigAction_pc, getSigAction_mem, hsig0, ho_f, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
    rw [htoBytes_emp, ← fourCells_eq_bytes, ko1, ko2, ko3]
  conv => arg 3; simp only [beq_self_eq_true, ↓reduceIte]
  clear hf23; wp_steps 11
  refine hb_step_bl_to (pc := b + 164#64) (dst := L.memcpyAddr) (by hb_wp_simp) (by hb_wp_simp) hf41 ?_
  refine hb_step_cut fun s2 hs2 => ?_
  have ⟨hpc2, hrun2, hsp2, hsp_al2, hlr2, hx0_2, hx1_2, hx2_2, hx19_2⟩ :
      s2.pc = L.memcpyAddr ∧ s2.status = .Running ∧ s2.sp = s.sp - 112#64 ∧ s2.spAligned = true ∧
      s2.readReg64 .lr = L.libcSigactionAddr + 420#64 ∧ s2.readReg64 .x0 = oact + 8#64 ∧ s2.readReg64 .x1 = s.sp - 8#64 ∧
      s2.readReg64 .x2 = 8#64 ∧ s2.readReg64 .x19 = 0#64 := by
    rw [hs2]; refine ⟨by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, ?_, by rw [← hb]; hb_wp_simp,
      by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp⟩
    simpa [State.spAligned, wp_norm, arm64_norm, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x70#64 hsp_align
  have hcs2 : CalleeSavedPreserved ((((s.writeReg64 .sp (s.sp - 112#64)).writeReg64 (.gpr 29#5) (s.sp - 112#64)).writeReg64 (.gpr 19#5) 0#64).writeReg64 (.gpr 20#5) oact |>.writeReg64 (.gpr 21#5) sig) s2 := by
    rw [hs2]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, bv_lin_norm]
  have hnv2 : HbNonVmFields s s2 := by rw [hs2]; hb_nv_rfl s
  clear hs2 hf41 hpc hlr hx0 hx1 hx2 hsp_sub_al hsxtw
  refine step_hb_memcpy8 hmemcpy (ret_pc := L.libcSigactionAddr + 420#64) (dst := oact + 8#64) (src := s.sp - 8#64) (v := 0#64) (F := ?_)
    (fun R hm => by simp only [wp_norm, arm64_norm] at hm ⊢; revert hm; sep_frame)
    hpc2 hrun2 hlr2 hx0_2 hx1_2 hx2_2 fun s3 hpc3 hrun3 hsp3 hcs3 _ hnv23 => ?_
  have hsp3_eq : s3.sp = s.sp - 112#64 := hsp3.trans hsp2
  have hx19_3 : s3.readReg64 .x19 = 0#64 := hcs3.1.trans hx19_2
  have hpc3_b : s3.pc = b + 168#64 := by rw [hpc3, ← hb]; bv_lin
  clear hpc3; wp_steps 2
  refine hb_step_bl_to (pc := b + 116#64) (dst := L.syscallRetAddr) (by hb_wp_simp) (by simp [wp_norm, arm64_norm, hrun3]) hf29 ?_
  refine hb_step_cut fun s3' hs3' => ?_
  have hsp3' : s3'.sp = s.sp - 112#64 := by rw [hs3']; simpa [wp_norm, arm64_norm] using hsp3_eq
  refine step_hb_syscallRet_nonneg hret' (ret_pc := b + 120#64) (x0v := 0#64) (F := ?_)
    (fun R hm => by rw [hsp3']; revert hm; sep_frame)
    (by rw [hs3']; hb_wp_simp) (by rw [hs3']; simp [wp_norm, arm64_norm, hrun3])
    (by rw [State.spAligned, hsp3']; simpa [State.spAligned, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x70#64 hsp_align)
    (by rw [hs3']; hb_wp_simp) (by rw [hs3']; hb_wp_simp) (by decide)
    fun s4 hpc4 hrun4 hsp4 hsp_al4 hcs4_raw hx0_4 hnv4_raw _ => ?_
  have hcs4 : CalleeSavedPreserved s3 s4 := by rw [hs3'] at hcs4_raw; simpa [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm] using hcs4_raw
  have hnv34 : HbNonVmFields s3 s4 := by rw [hs3'] at hnv4_raw; simpa [hbNonVm_w64_l, hbNonVm_pc_l] using hnv4_raw
  have hsp4_eq : s4.sp = s.sp - 112#64 := hsp4.trans hsp3'
  clear hs3' hsp4 hret' hf29 hmemcpy
  have hsp_al4_raw : (s4.sp &&& 15#64 == 0#64) = true := hsp_al4
  have hsp_add_al : ((s4.sp + 112#64) &&& 15#64 == 0#64) = true := by simp only [beq_iff_eq] at hsp_al4_raw ⊢; bv_bits
  have e0 : s.sp - 112#64 = s4.sp := hsp4_eq.symm
  have e1 : s.sp - 104#64 = s4.sp + 8#64 := by rw [hsp4_eq]; bv_lin
  have e2 : s.sp - 96#64 = s4.sp + 16#64 := by rw [hsp4_eq]; bv_lin
  have e3 : s.sp - 88#64 = s4.sp + 24#64 := by rw [hsp4_eq]; bv_lin
  have e4 : s.sp - 80#64 = s4.sp + 32#64 := by rw [hsp4_eq]; bv_lin
  have hsp_end : s4.sp + 112#64 = s.sp := by rw [hsp4_eq]; bv_lin
  clear hsp4_eq; wp_conv_pre => rw [e0, e1, e2, e3, e4]
  wp_steps 4
  refine SepWP.weaken_pre_frame
    (P' := (((oact ↦₆₄ 0#64) ∗ ((oact + 8#64) ↦₆₄ 0#64) ∗ ((oact + 0x88#64) ↦₆₄ _)) ∗ stackAt s.sp 0x90) ∗ G)
    (fun R hm => by
      simp only [State.mem_setPC, State.mem_writeReg64] at hm ⊢
      rw [← e4, ← e3, ← e2, ← e1, ← e0, hsp3'] at hm
      rw [stackAt_split_cells s.sp 0x20 14 (by decide)]; fold_stack_cells) ?_
  refine hnext _ _ (by hb_wp_simp) (by simp [wp_norm, arm64_norm, hrun4]) (by hb_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp_end] using hsp_align)
    (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm] at hcs2 hcs3 hcs4 ⊢; simp [hcs2, hcs3, hcs4])
    (by simp [wp_norm, arm64_norm, hx0_4])
    (hnv2.trans (hnv23.trans (hnv34.trans (by hb_nv_rfl s4))))

private theorem step_hb_handlerSet_llsc {P : Program} {sm hsAddr target_pc : BitVec 64} {hsLo mask32 : BitVec 32}
    (hf20 : P.fetch (sm + 80#64) = some (.ldxr .W32 true (.gpr 0#5) (.gpr 3#5)))
    (hf21 : P.fetch (sm + 84#64) = some (.logicalShift .W32 .ORR (.gpr 3#5) (.gpr 5#5) (.gpr 3#5) .LSL 0))
    (hf22 : P.fetch (sm + 88#64) = some (.stxr .W32 true (.gpr 2#5) (.gpr 0#5) (.gpr 3#5)))
    (hf23 : P.fetch (sm + 92#64) = some (.cbz .W32 true (.gpr 2#5) 0xfffffffffffffff4#64))
    (halign : MemWidth.isAligned .W32 hsAddr = true)
    {post : State → SepProp → Prop} {oom : State → SepProp} :
    ∀ (k : Nat) (s : State) (F : SepProp),
      s.exclFails.length < k → s.pc = sm + 80#64 → s.status = .Running →
      s.readReg64 (.gpr 0#5) = hsAddr → s.readReg64 (.gpr 5#5) = mask32.zeroExtend 64 →
      (∀ sf : State, sf.pc = sm + 96#64 → sf.status = .Running → sf.sp = s.sp →
        sf.readReg64 (.gpr 1#5) = s.readReg64 (.gpr 1#5) → sf.readReg64 (.gpr 4#5) = s.readReg64 (.gpr 4#5) →
        CalleeSavedPreserved s sf → HbNonVmFields s sf →
        SepWP P target_pc sf ((hsAddr ↦₃₂ (mask32 ||| hsLo)) ∗ F) post oom) →
      SepWP P target_pc s ((hsAddr ↦₃₂ hsLo) ∗ F) post oom := by
  intro k; induction k with
  | zero => intro _ _ hk; exact absurd hk (Nat.not_lt_zero _)
  | succ k ih =>
    intro s F hk hpc hrun hx0 hx5 hnext
    wp_steps 2
    refine hb_step_stxr32_either (pc := sm + 88#64) (ea := hsAddr) (v0 := hsLo) (val := mask32 ||| hsLo)
      (by hb_wp_simp) (by hb_wp_simp) hf22 rfl rfl (by hb_wp_simp) halign (by hb_wp_simp)
      (fun _ m' _ => ?_) (fun hf => ?_)
    · wp_step
      exact hnext _ (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
        (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, State.stepExclOracle, wp_norm, arm64_norm])
        (by hb_nv_rfl s)
    · wp_step
      refine ih _ F (hb_exclFails_tail_lt hk (by simpa [wp_norm, arm64_norm] using hf))
        (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
        fun sf hpc_f hrun_f hsp_f hx1_f hx4_f hcs_f hnv_f => ?_
      exact hnext sf hpc_f hrun_f (by simpa [State.stepExclOracle, wp_norm, arm64_norm] using hsp_f)
        (by simpa [State.stepExclOracle, wp_norm, arm64_norm] using hx1_f)
        (by simpa [State.stepExclOracle, wp_norm, arm64_norm] using hx4_f)
        (CalleeSavedPreserved.trans (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, State.stepExclOracle, wp_norm, arm64_norm]) hcs_f)
        ((by hb_nv_rfl s : HbNonVmFields s _).trans hnv_f)

@[local simp] private theorem cond_ne_subs0 : ConditionHolds .NE (subsPState64 0#64 0#64) = false := by
  unfold subsPState64 ConditionHolds; dsimp [AddWithCarry64]; decide

local macro "iAdrp " rd:term:arg pc:term:arg t:term:arg : term => `(Instr.adr true $rd (adrpOff $pc $t))
local macro "iAdr " rd:term:arg pc:term:arg t:term:arg : term => `(Instr.adr false $rd (($t) - ($pc)))
local macro "iAddLo12 " rd:term:arg rn:term:arg t:term:arg : term => `(Instr.addSubImm .W64 .ADD $rd $rn (($t).truncate 12) false)
local macro "iLdr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term => `(Instr.ldr .W64 .X64 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStr64Lo12 " rt:term:arg rn:term:arg t:term:arg : term => `(Instr.str .X64 $rt (.Offset $rn (pageLo12 $t)))
local macro "iLdr32Lo12 " rt:term:arg rn:term:arg t:term:arg : term => `(Instr.ldr .W32 .W32 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStr32Lo12 " rt:term:arg rn:term:arg t:term:arg : term => `(Instr.str .W32 $rt (.Offset $rn (pageLo12 $t)))
local macro "iLdr8Lo12 " rt:term:arg rn:term:arg t:term:arg : term => `(Instr.ldr .W32 .B8 false $rt (.Offset $rn (pageLo12 $t)))
local macro "iStr8Lo12 " rt:term:arg rn:term:arg t:term:arg : term => `(Instr.str .B8 $rt (.Offset $rn (pageLo12 $t)))
local macro "iBl " pc:term:arg t:term:arg : term => `(Instr.bl (($t) - ($pc)))
local macro "iB " pc:term:arg t:term:arg : term => `(Instr.b (($t) - ($pc)))

abbrev libcSigactionMidInstrs (L : StdBinaryLayout) (S : HbStartupLayout) : List Instr :=
  let sm := L.libcSigactionAddr + 0x30#64
  decodeWords [0x51000401#32, 0xd2800022#32, 0xd503201f#32] ++ [iAdr .x0 (sm + 0x0c#64) S.handlerSetAddr] ++
  decodeWords [0x93437c23#32, 0x9ac12041#32, 0x927de462#32, 0x8b020000#32, 0x35000161#32, 0xeb4183ff#32, 0xd360fc21#32, 0x540001c1#32] ++
  [iAdrp .x0 (sm + 0x30#64) (L.libcAddr + 1#64), iLdr8Lo12 .x0 .x0 (L.libcAddr + 1#64)] ++
  decodeWords [0x34000220#32, 0xb9408880#32, 0x36e003a0#32, 0xf9400086#32, 0x14000022#32, 0x2a0103e5#32, 0x885ffc03#32, 0x2a0300a3#32,
               0x8802fc03#32, 0x35ffffa2#32, 0x17fffff1#32, 0x91001000#32, 0x885ffc03#32, 0x2a030023#32, 0x8802fc03#32, 0x35ffffa2#32, 0x17ffffee#32] ++
  [iAdrp .x5 (sm + 0x7c#64) S.unmaskDoneAddr, iLdr32Lo12 .x0 .x5 S.unmaskDoneAddr] ++
  decodeWords [0x35fffdc0#32, 0xd2c00066#32, 0x910143e1#32, 0xd28010e8#32, 0xd2800020#32, 0xd2800002#32, 0xd2800103#32, 0xf9002be6#32, 0xd4000001#32, 0x52800020#32] ++
  [iStr32Lo12 .x0 .x5 S.unmaskDoneAddr, decodeWord 0x17ffffe3#32, decodeWord 0xd5033bbf#32, iAdrp .x0 (sm + 0xb8#64) S.eintrValidFlagAddr,
   decodeWord 0x52800021#32, iStr32Lo12 .x1 .x0 S.eintrValidFlagAddr, decodeWord 0xd5033bbf#32, decodeWord 0xf9400086#32]

theorem hb_step_entail {P : Program} {t : BitVec 64} {s : State} {Pre Pre' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hwp : SepWP P t s Pre' post oom) (h : ∀ R, s.mem ⊨ Pre ∗ R → s.mem ⊨ Pre' ∗ R) : SepWP P t s Pre post oom :=
  SepWP.weaken_pre_frame h hwp

set_option maxHeartbeats 400000 in
private theorem step_hb_libcSigaction_mid {P : Program} {L : StdBinaryLayout} {S : HbStartupLayout} {target_pc sig act w10 : BitVec 64}
    {hsLo unmask0 eintr0 : BitVec 32} (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc)
    (hmid : hasInstrs P (L.libcSigactionAddr + 0x30#64) (libcSigactionMidInstrs L S))
    (hal_hs : MemWidth.isAligned .W32 S.handlerSetAddr = true)
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = L.libcSigactionAddr + 48#64) (hrun : s.status = .Running) (hsp_al : s.spAligned = true) (hsp_ne : s.sp + 80#64 ≠ 0#64)
    (hx0 : s.readReg64 (.gpr 0#5) = sig) (hx4 : s.readReg64 (.gpr 4#5) = act)
    (hsig_mem : sig = 11#64 ∨ sig = 7#64) (hunmask : unmask0 = 0#32 ∨ unmask0 = 1#32)
    (hnext : ∀ (sf : State) (w10' : BitVec 64),
      sf.pc = L.libcSigactionAddr + 0xfc#64 → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      sf.readReg64 (.gpr 4#5) = act → sf.readReg64 (.gpr 6#5) = S.signalHandlerAddr →
      CalleeSavedPreserved s sf → HbNonVmFields s sf →
      SepWP P target_pc sf ((((act ↦₆₄ S.signalHandlerAddr) ∗ ((act + 0x88#64) ↦₆₄ 0x08000004#64)) ∗
        ((L.libcAddr + 1#64) ↦₈ 0#8) ∗ (S.handlerSetAddr ↦₃₂ ((if sig == 11#64 then 0x400#32 else 0x40#32) ||| hsLo)) ∗
        (S.unmaskDoneAddr ↦₃₂ 1#32) ∗ (S.eintrValidFlagAddr ↦₃₂ 1#32) ∗ ((s.sp + 80#64) ↦₆₄ w10')) ∗ F) post oom) :
    SepWP P target_pc s ((((act ↦₆₄ S.signalHandlerAddr) ∗ ((act + 0x88#64) ↦₆₄ 0x08000004#64)) ∗
      ((L.libcAddr + 1#64) ↦₈ 0#8) ∗ (S.handlerSetAddr ↦₃₂ hsLo) ∗
      (S.unmaskDoneAddr ↦₃₂ unmask0) ∗ (S.eintrValidFlagAddr ↦₃₂ eintr0) ∗ ((s.sp + 80#64) ↦₆₄ w10)) ∗ F) post oom := by
  have hp := hmid; clear hmid; dsimp only [libcSigactionMidInstrs] at hp
  generalize hsm : L.libcSigactionAddr + 0x30#64 = sm at hp hpc
  have_instrs hp 0 17; have_instrs hp 19 6; have_instrs hp 31 20; clear hp
  let mask32 : BitVec 32 := if sig == 11#64 then 0x400#32 else 0x40#32
  suffices hbody : ∀ {s0 : State},
      s0.pc = sm + 80#64 → s0.status = .Running → s0.sp = s.sp →
      s0.readReg64 (.gpr 0#5) = S.handlerSetAddr → s0.readReg64 (.gpr 1#5) = mask32.zeroExtend 64 →
      s0.readReg64 (.gpr 4#5) = act → s0.readReg64 (.gpr 5#5) = mask32.zeroExtend 64 →
      CalleeSavedPreserved s s0 → HbNonVmFields s s0 →
      SepWP P target_pc s0 ((((act ↦₆₄ S.signalHandlerAddr) ∗ ((act + 0x88#64) ↦₆₄ 0x08000004#64)) ∗
        ((L.libcAddr + 1#64) ↦₈ 0#8) ∗ (S.handlerSetAddr ↦₃₂ hsLo) ∗
        (S.unmaskDoneAddr ↦₃₂ unmask0) ∗ (S.eintrValidFlagAddr ↦₃₂ eintr0) ∗ ((s.sp + 80#64) ↦₆₄ w10)) ∗ F) post oom by
    rcases hsig_mem with rfl | rfl <;> (
      wp_steps 10
      refine hbody (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
        (by dsimp [mask32]; hb_wp_simp) (by hb_wp_simp) (by dsimp [mask32]; hb_wp_simp)
        (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])
        (by hb_nv_rfl s))
  intro s0 hpc0 hrun0 hsp0 hx0_0 hx1_0 hx4_0 hx5_0 hcs0 hnv0
  refine SepWP.weaken_pre_frame (P' := (S.handlerSetAddr ↦₃₂ hsLo) ∗ ?_) (fun R hm => by revert hm; sep_frame) ?_
  refine step_hb_handlerSet_llsc (sm := sm) hf_20 hf_21 hf_22 hf_23
    hal_hs (s0.exclFails.length + 1) s0 _ (Nat.lt_succ_self _) hpc0 hrun0 hx0_0 hx5_0
    fun s1 hpc1 hrun1 hsp1 hx1_1 hx4_1 hcs1 hnv1 => ?_
  have hsp1_eq : s1.sp = s.sp := hsp1.trans hsp0
  have hx1_eq : s1.readReg64 (.gpr 1#5) = mask32.zeroExtend 64 := hx1_1.trans hx1_0
  have hx4_eq : s1.readReg64 (.gpr 4#5) = act := hx4_1.trans hx4_0
  have hlsr1 : mask32.zeroExtend 64 >>> 32 = 0#64 := by dsimp [mask32]; rcases hsig_mem with rfl | rfl <;> decide
  have hsp_al1 : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1_eq]; exact hsp_al
  clear hx1_1 hx4_1 hpc0 hx0_0 hx1_0 hx4_0 hx5_0
  rcases hunmask with rfl | rfl
  · wp_steps 17
    rw [← hsp1_eq]
    refine SepWP.weaken_pre_frame (P' := ((s1.sp + 80#64) ↦₆₄ 0x300000000#64) ∗ ?_) (fun R hm => by revert hm; sep_frame) ?_
    refine step_svc_rt_sigprocmask_unblock hsvc (pc := sm + 164#64) (setAddr := s1.sp + 80#64) (maskVal := 0x300000000#64)
      (by hb_wp_simp) (by simp [wp_norm, arm64_norm, hrun1]) hf_41 (by hb_wp_simp) (by hb_wp_simp)
      (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by rw [hsp1_eq]; exact hsp_ne)
      (by
        have h1 : s1.sp.toNat &&& 15 = 0 := by
          simpa [BitVec.toNat_and] using congrArg BitVec.toNat (beq_iff_eq.mp hsp_al1)
        have hmod16 : s1.sp.toNat % 16 = 0 :=
          (Nat.and_two_pow_sub_one_eq_mod s1.sp.toNat 4).symm.trans h1
        have := s1.sp.isLt
        simp [BitVec.toNat_add]; omega) ?_
    wp_steps 11
    refine hb_step_entail (hnext _ 0x300000000#64 (by hb_wp_simp; rw [← hsm]; bv_lin) (by simp [wp_norm, arm64_norm, hrun1]) (by simp [wp_norm, arm64_norm, hsp1_eq])
      (by simpa [State.spAligned, wp_norm, arm64_norm, hsp1_eq] using hsp_al) (by hb_wp_simp) (by hb_wp_simp)
      (hcs0.trans (hcs1.trans (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])))
      (hnv0.trans (hnv1.trans (by hb_nv_rfl s1)))) (fun R hm => by rw [hsp1_eq] at hm; revert hm; sep_entail)
  · wp_steps 18
    refine hb_step_entail (hnext _ w10 (by hb_wp_simp; rw [← hsm]; bv_lin) (by simp [wp_norm, arm64_norm, hrun1]) (by simp [wp_norm, arm64_norm, hsp1_eq])
      (by simpa [State.spAligned, wp_norm, arm64_norm, hsp1_eq] using hsp_al) (by hb_wp_simp) (by hb_wp_simp)
      (hcs0.trans (hcs1.trans (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])))
      (hnv0.trans (hnv1.trans (by hb_nv_rfl s1)))) (fun R hm => by revert hm; sep_entail)

set_option maxHeartbeats 400000 in
/-- Step `__libc_sigaction(sig, act, 0)` (`sig ∈ {11, 7}`, `handler = S.signalHandlerAddr`), installing `hbCustomSigAction C S`. -/
theorem step_hb_libcSigaction_custom {P : Program} {C : HbCliLayout} {S : HbStartupLayout} {target_pc ret_pc sig act : BitVec 64}
    {hsLo unmask0 eintr0 : BitVec 32} (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc)
    (hhead : P.hasCode C.std.libcSigactionAddr libcSigactionHeadWords)
    (hmid : hasInstrs P (C.std.libcSigactionAddr + 0x30#64) (libcSigactionMidInstrs C.std S))
    (htail : hasInstrs P (C.std.libcSigactionAddr + 0xfc#64) (libcSigactionIgnTailInstrs C.std))
    (hret : P.hasCode C.std.syscallRetAddr syscallRetNonnegWords) (hmemcpy : hasInstrs P C.std.memcpyAddr hbMemcpyInstrs)
    (hal_hs : MemWidth.isAligned .W32 S.handlerSetAddr = true)
    (hhandler_gt1 : 1 < S.signalHandlerAddr.toNat)
    {s : State} {G : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = C.std.libcSigactionAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hsp_lo : 0x90 ≤ s.sp.toNat)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = sig) (hx1 : s.readReg64 .x1 = act) (hx2 : s.readReg64 .x2 = 0#64)
    (hsig_mem : sig = 11#64 ∨ sig = 7#64) (hact_ne : act ≠ 0#64) (hunmask : unmask0 = 0#32 ∨ unmask0 = 1#32)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → HbNonVmFields (s.setSigAction (sig.truncate 32) (hbCustomSigAction C S)) sf →
      SepWP P target_pc sf (((((act ↦₆₄ S.signalHandlerAddr) ∗ ((act + 8#64) ↦₆₄ 0#64) ∗ ((act + 0x88#64) ↦₆₄ 0x08000004#64)) ∗
        ((C.std.libcAddr + 1#64) ↦₈ 0#8) ∗ (S.handlerSetAddr ↦₃₂ ((if sig == 11#64 then 0x400#32 else 0x40#32) ||| hsLo)) ∗
        (S.unmaskDoneAddr ↦₃₂ 1#32) ∗ (S.eintrValidFlagAddr ↦₃₂ 1#32)) ∗ stackAt s.sp 0x90) ∗ G) post oom) :
    SepWP P target_pc s (((((act ↦₆₄ S.signalHandlerAddr) ∗ ((act + 8#64) ↦₆₄ 0#64) ∗ ((act + 0x88#64) ↦₆₄ 0x08000004#64)) ∗
      ((C.std.libcAddr + 1#64) ↦₈ 0#8) ∗ (S.handlerSetAddr ↦₃₂ hsLo) ∗
      (S.unmaskDoneAddr ↦₃₂ unmask0) ∗ (S.eintrValidFlagAddr ↦₃₂ eintr0)) ∗ stackAt s.sp 0x90) ∗ G) post oom := by
  have hret' := hret
  have hp := htail; dsimp only [libcSigactionIgnTailInstrs] at hp; generalize hb : C.std.libcSigactionAddr + 0xfc#64 = b at hp; revert hp
  refine peel_instr0 fun _ => ?_; peelS 14; peel1 hf15; peelS 7; peel1 hf23; peelS 5; peel1 hf29; peelS 4; intro _
  have hsp_sub_al : ((s.sp + 0xffffffffffffff90#64) &&& 0xf#64 == 0#64) = true := by simpa [BitVec.sub_eq_add_neg] using s.spAligned_sub 0x70#64 hsp_align
  have hact_f : (act == 0#64) = false := beq_false_of_ne hact_ne
  have hsxtw : (sig >>> 0 &&& 0xffffffff#64 ||| (if sig.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&& 0xffffffff00000000#64) = sig := by
    rcases hsig_mem with rfl | rfl <;> decide
  have hls1 : ConditionHolds .LS (subsPState64 S.signalHandlerAddr 1#64) = false := cond_ls_subs1_false hhandler_gt1
  have hlo : 1 ≤ (sig.truncate 32).toNat := by rcases hsig_mem with rfl | rfl <;> decide
  have hhi : (sig.truncate 32).toNat ≤ 64 := by rcases hsig_mem with rfl | rfl <;> decide
  wp_conv_pre => rw [stackAt_split_cells s.sp 0x20 14 (by decide), cells_split_sub s.sp 112 40 9 5, cells_split_sub s.sp 40 32 1 4, ← memRegion_cells (s.sp - BitVec.ofNat 64 40) 1 (by decide)]; simp only [Nat.reduceMul]; simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun w10 => SepWP.exists_elim fun w11 => SepWP.exists_elim fun w12 => SepWP.exists_elim fun w13 => ?_; iterate 9 (refine SepWP.exists_elim fun _ => ?_)
  clear hret; wp_steps 12; clear hhead
  refine hb_step_cut fun s0 hs0 => ?_
  have ⟨hpc0, hrun0, hsp0, hsp_al0, hx0_0, hx4_0, hx20_0, hx21_0⟩ :
      s0.pc = C.std.libcSigactionAddr + 48#64 ∧ s0.status = .Running ∧ s0.sp = s.sp - 112#64 ∧ s0.spAligned = true ∧
      s0.readReg64 (.gpr 0#5) = sig ∧ s0.readReg64 (.gpr 4#5) = act ∧ s0.readReg64 .x20 = 0#64 ∧ s0.readReg64 .x21 = sig := by
    rw [hs0]; refine ⟨by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, ?_, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp, by hb_wp_simp⟩
    simpa [State.spAligned, wp_norm, arm64_norm, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x70#64 hsp_align
  have hcs0 : CalleeSavedPreserved ((((s.writeReg64 .sp (s.sp - 112#64)).writeReg64 (.gpr 29#5) (s.sp - 112#64)).writeReg64 (.gpr 20#5) 0#64).writeReg64 (.gpr 21#5) sig) s0 := by
    rw [hs0]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, bv_lin_norm]
  have hnv0 : HbNonVmFields s s0 := by rw [hs0]; hb_nv_rfl s
  clear hs0 hpc hlr hx0 hx1 hx2 hsp_sub_al hact_f hsxtw hls1
  have hsp0_80 : s0.sp + 80#64 = s.sp - 32#64 := by rw [hsp0]; bv_lin
  refine SepWP.weaken_pre_frame
    (P' := ((((act ↦₆₄ S.signalHandlerAddr) ∗ ((act + 0x88#64) ↦₆₄ 0x08000004#64)) ∗
      ((C.std.libcAddr + 1#64) ↦₈ 0#8) ∗ (S.handlerSetAddr ↦₃₂ hsLo) ∗
      (S.unmaskDoneAddr ↦₃₂ unmask0) ∗ (S.eintrValidFlagAddr ↦₃₂ eintr0) ∗ ((s0.sp + 80#64) ↦₆₄ w10)) ∗ ?_))
    (fun R hm => by rw [hsp0_80]; revert hm; sep_frame) ?_
  refine step_hb_libcSigaction_mid hsvc hmid hal_hs hpc0 hrun0 hsp_al0 (by rw [hsp0_80]; bv_omega)
    hx0_0 hx4_0 hsig_mem hunmask fun s1 w10' hpc1 hrun1 hsp1 hsp_al1 hx4_1 hx6_1 hcs1 hnv1 => ?_
  clear hmid hpc0 hx0_0 hx4_0
  have hsp1_eq : s1.sp = s.sp - 112#64 := hsp1.trans hsp0
  have hpc1_b : s1.pc = b := hpc1.trans hb
  have hx4_1' : s1.readReg64 .x4 = act := hx4_1
  have hx6_1' : s1.readReg64 .x6 = S.signalHandlerAddr := hx6_1
  have hx20_1 : s1.readReg64 .x20 = 0#64 := hcs1.2.1.trans hx20_0
  have hx21_1 : s1.readReg64 .x21 = sig := hcs1.2.2.1.trans hx21_0
  have hsp_al1_raw : (s1.sp &&& 15#64 == 0#64) = true := hsp_al1
  clear hpc1 hx4_1 hx6_1
  wp_steps 15
  refine hb_step_bl_to (pc := b + 60#64) (dst := C.std.memcpyAddr) (by hb_wp_simp) (by simp [wp_norm, arm64_norm, hrun1]) hf15 ?_
  refine hb_step_cut fun s2 hs2 => ?_
  have ⟨hpc2, hrun2, hsp2, hsp_al2, hlr2, hx0_2, hx1_2, hx2_2, hx19_2, hx20_2, hx21_2⟩ :
      s2.pc = C.std.memcpyAddr ∧ s2.status = .Running ∧ s2.sp = s.sp - 112#64 ∧ s2.spAligned = true ∧
      s2.readReg64 .lr = C.std.libcSigactionAddr + 316#64 ∧ s2.readReg64 .x0 = s.sp - 40#64 ∧ s2.readReg64 .x1 = act + 8#64 ∧
      s2.readReg64 .x2 = 8#64 ∧ s2.readReg64 .x19 = s.sp - 64#64 ∧ s2.readReg64 .x20 = 0#64 ∧ s2.readReg64 .x21 = sig := by
    rw [hs2]; refine ⟨by hb_wp_simp, by simp [wp_norm, arm64_norm, hrun1],
      by simp [wp_norm, arm64_norm, bv_lin_norm, hsp1_eq],
      by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al1, by rw [← hb]; hb_wp_simp,
      by simp [wp_norm, arm64_norm, bv_lin_norm], by hb_wp_simp, by hb_wp_simp,
      by simp [wp_norm, arm64_norm, bv_lin_norm], by hb_wp_simp, by hb_wp_simp⟩
  have hcs2 : CalleeSavedPreserved (s1.writeReg64 (.gpr 19#5) (s.sp - 64#64)) s2 := by
    rw [hs2]; simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, bv_lin_norm]
  have hnv12 : HbNonVmFields s1 s2 := by rw [hs2]; hb_nv_rfl s1
  clear hs2 hf15
  refine step_hb_memcpy8 hmemcpy (ret_pc := C.std.libcSigactionAddr + 316#64) (dst := s.sp - 40#64) (src := act + 8#64) (v := 0#64) (F := ?_)
    (fun R hm => by simp only [wp_norm, arm64_norm] at hm ⊢; revert hm; sep_frame)
    hpc2 hrun2 hlr2 hx0_2 hx1_2 hx2_2 fun s3 hpc3 hrun3 hsp3 hcs3 _ hnv23 => ?_
  have hsp3_eq : s3.sp = s.sp - 112#64 := hsp3.trans hsp2
  have hx19_3 : s3.readReg64 .x19 = s.sp - 64#64 := hcs3.1.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = 0#64 := hcs3.2.1.trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = sig := hcs3.2.2.1.trans hx21_2
  have hpc3_b : s3.pc = b + 64#64 := by rw [hpc3, ← hb]; bv_lin
  clear hpc3
  have hk_f : ((s.sp - 64#64) == 0#64) = false := beq_false_of_ne (by bv_omega)
  have ka0 : s1.sp + 48#64 = s.sp - 64#64 := by rw [hsp1_eq]; bv_lin
  have ka1 : (s.sp - 64#64) + 8#64 = s1.sp + 56#64 := by rw [hsp1_eq]; bv_lin
  have ka2 : (s.sp - 64#64) + 16#64 = s1.sp + 64#64 := by rw [hsp1_eq]; bv_lin
  have ka3 : (s.sp - 64#64) + 24#64 = s.sp - 40#64 := by bv_lin
  wp_steps 7
  refine SepWP.weaken_pre_frame
    (P' := kSigActionAt (s.sp - 64#64) S.signalHandlerAddr 0x0c000004#64 C.std.restoreRtAddr 0#64 ∗
      (optOldSigActionAt 0#64 [] ∗ ?_))
    (fun R hm => by
      dsimp only [kSigActionAt, optOldSigActionAt]; rw [hk_f]
      simp only [beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
      rw [ka1, ka2, ka3, ← ka0]; revert hm; sep_frame) ?_
  refine SepWP.step_svc_rt_sigaction_any (pc := b + 92#64) (signum := sig.truncate 32) (act := s.sp - 64#64)
    (handler := S.signalHandlerAddr) (flags := 0x0c000004#64) (restorer := C.std.restoreRtAddr) (mask := 0#64)
    (oldact := 0#64) (oldBs₀ := [])
    (by hb_wp_simp) (by simp [wp_norm, arm64_norm, hrun3]) hf23 (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
    (by hb_wp_simp) (by hb_wp_simp) hlo hhi
    (Or.inr ⟨by rcases hsig_mem with rfl | rfl <;> decide, by rcases hsig_mem with rfl | rfl <;> decide,
      by bv_omega, Or.inr (Or.inr (hsig_mem.imp (by rintro rfl; rfl) (by rintro rfl; rfl)))⟩)
    (Or.inl rfl) (fun m' => ?_) (hb_evalSvc_rt_sigaction hsvc (by hb_wp_simp))
  dsimp only []
  wp_conv_pre =>
    dsimp only [kSigActionAt, optOldSigActionAt]; rw [hk_f]
    simp only [beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, emp_sepConj, ← fourCells_eq_bytes]
  conv => arg 3; rw [hk_f]; simp only [Bool.false_eq_true, ↓reduceIte, show (0#64 &&& ~~~SIG_UNBLOCKABLE_MASK) = 0#64 from rfl]
  clear hf23
  have heq_ofBits4 : ConditionHolds .EQ (PState.ofBits4 0#4) = false := by decide
  wp_steps 5
  refine hb_step_bl_to (pc := b + 116#64) (dst := C.std.syscallRetAddr) (by hb_wp_simp) (by simp [wp_norm, arm64_norm, hrun3]) hf29 ?_
  refine hb_step_cut fun s3' hs3' => ?_
  have hsp3' : s3'.sp = s.sp - 112#64 := by rw [hs3']; simpa [wp_norm, arm64_norm] using hsp3_eq
  refine step_hb_syscallRet_nonneg hret' (ret_pc := b + 120#64) (x0v := 0#64) (F := ?_)
    (fun R hm => by rw [hsp3']; revert hm; sep_frame)
    (by rw [hs3']; hb_wp_simp) (by rw [hs3']; simp [wp_norm, arm64_norm, hrun3])
    (by rw [State.spAligned, hsp3']; simpa [State.spAligned, BitVec.sub_eq_add_neg] using s.spAligned_sub 0x70#64 hsp_align)
    (by rw [hs3']; hb_wp_simp) (by rw [hs3']; hb_wp_simp) (by decide)
    fun s4 hpc4 hrun4 hsp4 hsp_al4 hcs4_raw hx0_4 hnv4_raw _ => ?_
  have hcs4 : CalleeSavedPreserved (s3.writeReg64 (.gpr 19#5) 0#64) s4 := by
    rw [hs3'] at hcs4_raw; simpa [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm] using hcs4_raw
  have hnv34 : HbNonVmFields (s3.setSigAction (sig.truncate 32) (hbCustomSigAction C S)) s4 := by
    rw [hs3'] at hnv4_raw; exact (by hb_nv_rfl _ : HbNonVmFields (s3.setSigAction (sig.truncate 32) (hbCustomSigAction C S)) _).trans hnv4_raw
  have hsp4_eq : s4.sp = s.sp - 112#64 := hsp4.trans hsp3'
  clear hs3' hsp4 hret' hf29 hmemcpy
  have hsp_al4_raw : (s4.sp &&& 15#64 == 0#64) = true := hsp_al4
  have hsp_add_al : ((s4.sp + 112#64) &&& 15#64 == 0#64) = true := by simp only [beq_iff_eq] at hsp_al4_raw ⊢; bv_bits
  have e0 : s.sp - 112#64 = s4.sp := hsp4_eq.symm
  have e1 : s.sp - 104#64 = s4.sp + 8#64 := by rw [hsp4_eq]; bv_lin
  have e2 : s.sp - 96#64 = s4.sp + 16#64 := by rw [hsp4_eq]; bv_lin
  have e3 : s.sp - 88#64 = s4.sp + 24#64 := by rw [hsp4_eq]; bv_lin
  have e4 : s.sp - 80#64 = s4.sp + 32#64 := by rw [hsp4_eq]; bv_lin
  have hsp_end : s4.sp + 112#64 = s.sp := by rw [hsp4_eq]; bv_lin
  have ka1' : (s.sp - 64#64) + 8#64 = s.sp - 56#64 := by bv_lin
  have ka2' : (s.sp - 64#64) + 16#64 = s.sp - 48#64 := by bv_lin
  clear hsp4_eq; wp_conv_pre => rw [e0, e1, e2, e3, e4]
  wp_steps 4
  refine SepWP.weaken_pre_frame
    (P' := ((((act ↦₆₄ S.signalHandlerAddr) ∗ ((act + 8#64) ↦₆₄ 0#64) ∗ ((act + 0x88#64) ↦₆₄ 0x08000004#64)) ∗
      ((C.std.libcAddr + 1#64) ↦₈ 0#8) ∗ (S.handlerSetAddr ↦₃₂ ((if sig == 11#64 then 0x400#32 else 0x40#32) ||| hsLo)) ∗
      (S.unmaskDoneAddr ↦₃₂ 1#32) ∗ (S.eintrValidFlagAddr ↦₃₂ 1#32)) ∗ stackAt s.sp 0x90) ∗ G)
    (fun R hm => by
      simp only [State.mem_setPC, State.mem_writeReg64] at hm ⊢
      rw [← e4, ← e3, ← e2, ← e1, ← e0, ka1', ka2', ka3, hsp0_80, hsp3'] at hm
      rw [stackAt_split_cells s.sp 0x20 14 (by decide)]; fold_stack_cells) ?_
  have hnv03 : HbNonVmFields s s3 := hnv0.trans (hnv1.trans (hnv12.trans hnv23))
  have hnv_sig : HbNonVmFields (s.setSigAction (sig.truncate 32) (hbCustomSigAction C S))
      (s3.setSigAction (sig.truncate 32) (hbCustomSigAction C S)) :=
    hbNonVm_applyOptSig (actOpt := some (sig.truncate 32, hbCustomSigAction C S)) hnv03
  refine hnext _ (by hb_wp_simp) (by simp [wp_norm, arm64_norm, hrun4]) (by hb_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp_end] using hsp_align)
    (by simp (config := { decide := true }) [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm] at hcs0 hcs1 hcs2 hcs3 hcs4 ⊢;
        simp [hcs0, hcs1, hcs2, hcs3, hcs4])
    (by simp [wp_norm, arm64_norm, hx0_4])
    (hnv_sig.trans (hnv34.trans (by hb_nv_rfl s4)))

/-! ## Alternate signal stack allocation (`mmap`, `mprotect`, `make_handler`) -/

private theorem hb_evalSvc_mmap {P : Program} {s : State} (hsvc : P.svc = Syscall.standard) (hx8 : s.readReg64 .x8 = 222#64) :
    P.evalInst (.system false 0#16) s = execMmap s := by
  rw [_root_.Arm64.Program.evalInst_svc0, hsvc, evalSvc_standard]
  simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.allocTable, hx8]

private theorem hb_evalSvc_mprotect {P : Program} {s : State} (hsvc : P.svc = Syscall.standard) (hx8 : s.readReg64 .x8 = 226#64) :
    P.evalInst (.system false 0#16) s = execMprotect s := by
  rw [_root_.Arm64.Program.evalInst_svc0, hsvc, evalSvc_standard]
  simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.allocTable, hx8]

private theorem step_svc_mprotect_protNone {P : Program} {target_pc pc addr : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsvc : P.svc = Syscall.standard) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : P.fetch pc = some (.system false 0#16)) (hx8 : s.readReg64 .x8 = 226#64)
    (hx0 : s.readReg64 .x0 = addr) (hx1 : s.readReg64 .x1 = 4096#64) (hx2 : s.readReg64 .x2 = 0#64)
    (halign : addr.toNat % 4096 = 0) (hva : addr.toNat + 4096 ≤ 2 ^ 48)
    (hnext : SepWP P target_pc (((s.setMem (s.mem.setPermNonFrozen addr 4096 Perm.protNone)).writeReg64 .x0 0#64).setPC (pc + 4#64))
      (memRegionProtNone addr 4096 ∗ F) post oom) :
    SepWP P target_pc s (memRegion addr 4096 ∗ F) post oom := by
  unfold SepWP; intro R hm
  have hm' : s.mem ⊨ memRegion addr 4096 ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hnf : s.mem.allPerm (fun p => !p.frozen) addr 4096 = true := Satisfies.allPerm_not_frozen_of_memRegion hm'
  have hmap : s.mem.allPerm (·.mapped) addr 4096 = true := Satisfies.allPerm_mapped_of_memRegion hm'
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch); rw [hb_evalSvc_mprotect hsvc hx8]
  have hev : execMprotect s = ((s.setMem (s.mem.setPermNonFrozen addr 4096 Perm.protNone)).writeReg64 .x0 0#64).setPC (pc + 4#64) := by
    simp [execMprotect, MMAP_PROT_NONE, PAGE_SIZE, hx0, hx1, hx2, halign, hva, hnf, hmap, State.advancePC, State.setPC, State.writeReg64, State.setMem, hpc]
  rw [hev]; unfold SepWP at hnext
  exact hnext R (by rw [sepConj_assoc]; exact Satisfies.setPermProtNone_of_memRegion hm')

abbrev mprotectWrapperInstrs (L : StdBinaryLayout) (S : HbStartupLayout) : List Instr :=
  [decodeWord 0xa9bf7bfd#32, iAdrp .x4 (S.mprotectWrapperAddr + 0x04#64) (L.libcAddr + 0x30#64),
   decodeWord 0xaa0003e3#32, decodeWord 0x910003fd#32, iLdr64Lo12 .x4 .x4 (L.libcAddr + 0x30#64)] ++
  decodeWords [0xd2801c48#32, 0x93407c42#32, 0xd1000480#32, 0xcb0403e4#32, 0x8b010001#32,
               0x8a040060#32, 0x8b010063#32, 0x8a040061#32, 0xcb000021#32, 0xd4000001#32] ++
  [iBl (S.mprotectWrapperAddr + 0x3c#64) L.syscallRetAddr] ++ decodeWords [0xa8c17bfd#32, 0xd65f03c0#32]

/-- Step `mprotect(altBase, 4096, PROT_NONE)` (`S.mprotectWrapperAddr`), demoting `memRegion altBase 4096` to `memRegionProtNone altBase 4096`. -/
theorem step_hb_mprotect_none {P : Program} {L : StdBinaryLayout} {S : HbStartupLayout} {target_pc ret_pc altBase : BitVec 64}
    (hsvc : P.svc = Syscall.standard) (hmprot : hasInstrs P S.mprotectWrapperAddr (mprotectWrapperInstrs L S))
    (hret : P.hasCode L.syscallRetAddr syscallRetNonnegWords)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ (((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ memRegion altBase 4096 ∗ stackAt s.sp 0x30) ∗ (F ∗ R))
    (hpc : s.pc = S.mprotectWrapperAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = altBase) (hx1 : s.readReg64 .x1 = 4096#64) (hx2 : s.readReg64 .x2 = 0#64)
    (halign : altBase.toNat % 4096 = 0) (hva : altBase.toNat + 4096 ≤ 2 ^ 48)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = 0#64 → HbNonVmFields s sf →
      sf.physMemAvail = s.physMemAvail → sf.brk = s.brk → sf.brkStart = s.brkStart →
      (∀ a, sf.mem.perm a = (s.mem.setPermNonFrozen altBase 4096 Perm.protNone).perm a) →
      SepWP P target_pc sf ((((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ memRegionProtNone altBase 4096 ∗ stackAt s.sp 0x30) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame (P' := (((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ memRegion altBase 4096 ∗ stackAt s.sp 0x30) ∗ F)
    (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have hret' := hret; have_instrs hmprot 0 18
  have hsp_sub_al : ((s.sp - 16#64) &&& 0xf#64 == 0#64) = true := by simpa using s.spAligned_sub 0x10#64 hsp_align
  wp_conv_pre => rw [stackAt_split_cells s.sp 0x20 2 (by decide)]
  unfold_stack_cells 2
  have hf0 : P.fetch S.mprotectWrapperAddr = some (.stp .W64 .x29 .lr (.PreIndex .sp 0xfffffffffffffff0#64)) := hf_0
  refine hb_step_stp64_perm (ea2 := s.sp - 8#64) hpc hrun hf0
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_align])
    (show evalAddrMode s (.PreIndex .sp 0xfffffffffffffff0#64) = (s.sp - 16#64, some (.sp, s.sp - 16#64)) by simp [evalAddrMode, arm64_norm, bv_lin_norm])
    (by bv_lin) rfl rfl (by wp_sep_access) (by wp_sep_access) fun m1 hm1 => ?_
  clear hret; wp_steps 13
  have hand0 : altBase &&& -4096#64 = altBase := by show altBase &&& 0xfffffffffffff000#64 = altBase; bv_bits
  have hand1 : (altBase + 8191#64 &&& -4096#64) - altBase = 4096#64 := by show (altBase + 8191#64 &&& 0xfffffffffffff000#64) - altBase = 4096#64; bv_bits
  refine hb_step_entail (Pre' := memRegion altBase 4096 ∗ (((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗
      (stackAt (s.sp - 16#64) 0x20 ∗ (((s.sp - 16#64) ↦₆₄ s.readReg64 .x29) ∗ ((s.sp - 8#64) ↦₆₄ ret_pc))) ∗ F)) ?_
    (fun R hm => by revert hm; sep_entail)
  refine step_svc_mprotect_protNone hsvc (pc := S.mprotectWrapperAddr + 56#64) (addr := altBase)
    (by hb_wp_simp) (by hb_wp_simp) hf_14 (by hb_wp_simp)
    (by simp only [wp_norm, arm64_norm, hand0])
    (by simp only [wp_norm, arm64_norm, hand0, hand1])
    (by hb_wp_simp) halign hva ?_
  refine hb_step_bl_to (pc := S.mprotectWrapperAddr + 60#64) (dst := L.syscallRetAddr) (by hb_wp_simp) (by hb_wp_simp) hf_15 ?_
  refine step_hb_syscallRet_nonneg hret' (ret_pc := S.mprotectWrapperAddr + 64#64) (x0v := 0#64) (F := ?_)
    (fun R hm => by simp only [wp_norm, arm64_norm] at hm ⊢; revert hm; sep_frame)
    (by hb_wp_simp) (by hb_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm] using s.spAligned_sub 0x10#64 hsp_align)
    (by hb_wp_simp) (by hb_wp_simp) (by decide)
    fun s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hx0_2 hnv2 hvm2 => ?_
  have hsp2_eq : s2.sp = s.sp - 16#64 := by simpa [wp_norm, arm64_norm] using hsp2
  have h16 : s.sp - 16#64 = s2.sp := hsp2_eq.symm
  have h08 : s.sp - 8#64 = s2.sp + 8#64 := by rw [hsp2_eq]; bv_lin
  have hsp_end : s2.sp + 16#64 = s.sp := by rw [hsp2_eq]; bv_lin
  have hsp_al2_raw : (s2.sp &&& 15#64 == 0#64) = true := hsp_al2
  clear hret' hsp2 hsp2_eq; wp_conv_pre => rw [h16, h08]
  wp_steps 2
  refine SepWP.weaken_pre_frame (P' := (((L.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ memRegionProtNone altBase 4096 ∗ stackAt s.sp 0x30) ∗ F)
    (fun R hm => by
      simp only [State.mem_setPC, State.mem_writeReg64] at hm ⊢
      rw [← h08, ← h16] at hm; rw [stackAt_split_cells s.sp 0x20 2 (by decide)]; fold_stack_cells) ?_
  have hnv02 : HbNonVmFields s s2 := (by hb_nv_rfl s : HbNonVmFields s _).trans hnv2
  refine hnext _ (by hb_wp_simp) (by simp [wp_norm, arm64_norm, hrun2]) (by hb_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, hsp_end] using hsp_align)
    ?_ (by simp [wp_norm, arm64_norm, hx0_2]) (hnv02.trans (by hb_nv_rfl s2))
    (by simpa [wp_norm, arm64_norm] using hvm2.physMemAvail_eq)
    (by simpa [wp_norm, arm64_norm] using hvm2.brk_eq)
    (by simpa [wp_norm, arm64_norm] using hvm2.brkStart_eq)
    fun a => ?_
  · rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs2 with ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩
    simp only [wp_norm, arm64_norm] at g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 gv
    rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, gv]
  · simp only [wp_norm, arm64_norm]
    rw [hvm2.perm_eq a]
    simp only [wp_norm, arm64_norm, Memory.perm_setPermNonFrozen, hm1]

@[local simp] private theorem hbNonVm_or_r (a b : State) : HbNonVmFields a b.nextOracle ↔ HbNonVmFields a b := Iff.rfl
@[local simp] private theorem hbNonVm_phys_r (a b : State) (n : Nat) : HbNonVmFields a (b.setPhysMemAvail n) ↔ HbNonVmFields a b := Iff.rfl

private theorem canMap_congr {m1 m2 : Memory} (h : ∀ a, m1.perm a = m2.perm a) (b : BitVec 64) (n : Nat) :
    m1.canMap b n = m2.canMap b n := by
  unfold Memory.canMap; rw [Bool.eq_iff_iff, Memory.allPerm_iff, Memory.allPerm_iff]; simp only [h]

private theorem cond_ne_adds1_true {v : BitVec 64} (hlt : v.toNat < 2 ^ 64 - 1) :
    ConditionHolds .NE (addsPState64 v 1#64) = true := by
  unfold addsPState64 ConditionHolds; dsimp [AddWithCarry64]
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne]; bv_omega

private theorem cond_eq_adds1_false {v : BitVec 64} (hlt : v.toNat < 2 ^ 64 - 1) :
    ConditionHolds .EQ (addsPState64 v 1#64) = false := by
  unfold addsPState64 ConditionHolds; dsimp [AddWithCarry64]
  simp only [beq_eq_false_iff_ne]; bv_omega

private theorem step_svc_mmap_anon_stack {P : Program} {target_pc pc reqLen : BitVec 64} {size : Nat}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsvc : P.svc = Syscall.standard) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : P.fetch pc = some (.system false 0#16)) (hx8 : s.readReg64 .x8 = 222#64)
    (_hx0 : s.readReg64 .x0 = 0#64) (hx1 : s.readReg64 .x1 = reqLen)
    (hx2 : s.readReg64 .x2 = 3#64) (hx3 : s.readReg64 .x3 = 131106#64) (hx5 : s.readReg64 .x5 = 0#64)
    (hlen0 : reqLen ≠ 0#64) (hsz_eq : Arm64.pageAlignUp reqLen.toNat = size)
    (hpos : 0 < size) (hal : size % 4096 = 0) (hphys : size ≤ s.physMemAvail)
    (hgap : ∃ gap : BitVec 64, 65536 ≤ gap.toNat ∧ gap.toNat % 4096 = 0 ∧ gap.toNat + size ≤ 2 ^ 48 ∧ s.mem.canMap gap size = true)
    (hnext : ∀ altBase : BitVec 64, 4096 ≤ altBase.toNat → altBase.toNat % 4096 = 0 →
      altBase.toNat + size ≤ 2 ^ 48 → s.mem.canMap altBase size = true →
      SepWP P target_pc (((((s.setMem (s.mem.mapZero altBase size)).setPhysMemAvail
        (s.physMemAvail - size)).nextOracle).writeReg64 .x0 altBase).setPC (pc + 4#64))
        (memRegion altBase size ∗ memMapped altBase size ∗ F) post oom) :
    SepWP P target_pc s F post oom := by
  refine SepWP.of_reaches_pc fun R hm => ?_
  have hpage : Arm64.pageAlignUp (s.readReg64 .x1).toNat = size := by rw [hx1, hsz_eq]
  have hlen0' : s.readReg64 .x1 ≠ 0#64 := by rw [hx1]; exact hlen0
  rcases hgap with ⟨gap, hmin, hgapAl, hfit_gap, hmap_gap⟩
  obtain ⟨altBase, hsan⟩ := sanitizeMmapAddr_exists_of_gap (s.oracle.mmap s.oracleIdx) hpos
    (by unfold PAGE_SIZE; exact hal) (by unfold MMAP_MIN_ADDR; exact hmin)
    (by unfold PAGE_SIZE; exact hgapAl) (by unfold USER_VA_LIMIT; exact hfit_gap) hmap_gap
  obtain ⟨hne, hbaseAl, hbaseFit, hbaseMap⟩ := sanitizeMmapAddr_spec hsan
  have hbase4k : 4096 ≤ altBase.toNat := by
    have hgt0 : 0 < altBase.toNat := Nat.pos_of_ne_zero fun h => hne (BitVec.eq_of_toNat_eq (by simpa using h))
    unfold PAGE_SIZE at hbaseAl; omega
  have hexec := execMmap_anon_sanitized_ok s hx2 (Or.inr hx3) hx5 hlen0' (by rw [hpage]; exact hsan) (by rw [hpage]; exact hphys)
  rw [hpage] at hexec
  have hadv : ((((s.setMem (s.mem.mapZero altBase size)).setPhysMemAvail (s.physMemAvail - size)).nextOracle).writeReg64 .x0 altBase).advancePC =
      ((((s.setMem (s.mem.mapZero altBase size)).setPhysMemAvail (s.physMemAvail - size)).nextOracle).writeReg64 .x0 altBase).setPC (pc + 4#64) := by
    simp [State.advancePC, State.setPC, hpc]
  apply reaches_pc_step hrun (hpc ▸ hfetch)
  rw [hb_evalSvc_mmap hsvc hx8, hexec, hadv]
  refine SepWP.to_reaches_pc (hnext altBase hbase4k (by simpa [PAGE_SIZE] using hbaseAl) (by simpa [USER_VA_LIMIT] using hbaseFit) hbaseMap) ?_
  rw [sepConj_assoc, sepConj_assoc]; exact Satisfies.mapZero_mapped hm hbaseMap

abbrev mmapWrapperInstrs (L : StdBinaryLayout) (S : HbStartupLayout) : List Instr :=
  decodeWords [0xa9bc7bfd#32, 0xf2402cbf#32, 0x910003fd#32, 0x54000381#32,
               0xa90153f3#32, 0xaa0003f4#32, 0xb27ff7e0#32, 0xeb00003f#32,
               0x540003a8#32, 0xa9025bf5#32, 0x2a0303f3#32, 0x2a0203f6#32,
               0x2a0403f5#32, 0x372003b3#32, 0x93407ec2#32, 0x93407ea4#32,
               0xaa1403e0#32, 0x93407e63#32, 0xd2801bc8#32, 0xd4000001#32,
               0xf100029f#32, 0xba410800#32, 0x540000a1#32, 0x121c0673#32,
               0x92800160#32, 0x7100827f#32, 0xda9f0000#32, 0xa94153f3#32,
               0xa9425bf5#32, 0xa8c47bfd#32] ++ [iB (S.mmapWrapperAddr + 0x78#64) L.syscallRetAddr]

/-- Step `mmap(0, reqLen, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_STACK, -1, 0)` (`S.mmapWrapperAddr`). -/
theorem step_hb_mmap_anon_zero {P : Program} {L : StdBinaryLayout} {S : HbStartupLayout} {target_pc ret_pc reqLen : BitVec 64} {size : Nat}
    (hsvc : P.svc = Syscall.standard) (hmmap : hasInstrs P S.mmapWrapperAddr (mmapWrapperInstrs L S))
    (hret : P.hasCode L.syscallRetAddr syscallRetNonnegWords)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R → s.mem ⊨ stackAt s.sp 0x40 ∗ (F ∗ R))
    (hpc : s.pc = S.mmapWrapperAddr) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = 0#64) (hx1 : s.readReg64 .x1 = reqLen)
    (hx2 : s.readReg64 .x2 = 3#64) (hx3 : s.readReg64 .x3 = 131106#64)
    (_hx4 : s.readReg32 .x4 = 0xffffffff#32) (hx5 : s.readReg64 .x5 = 0#64)
    (hlen0 : reqLen ≠ 0#64) (hreq_hi : reqLen.toNat ≤ 528384)
    (hsz_eq : Arm64.pageAlignUp reqLen.toNat = size) (hpos : 0 < size) (hal : size % 4096 = 0)
    (hsz_hi : size ≤ 528384) (hphys : size ≤ s.physMemAvail)
    (hgap : ∃ gap : BitVec 64, 65536 ≤ gap.toNat ∧ gap.toNat % 4096 = 0 ∧ gap.toNat + size ≤ 2 ^ 48 ∧ s.mem.canMap gap size = true)
    (hnext : ∀ (sf : State) (altBase : BitVec 64),
      4096 ≤ altBase.toNat → altBase.toNat % 4096 = 0 → altBase.toNat + size ≤ 2 ^ 48 → s.mem.canMap altBase size = true →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = altBase → HbNonVmFields s sf →
      sf.physMemAvail = s.physMemAvail - size → sf.brk = s.brk → sf.brkStart = s.brkStart →
      (∀ a, sf.mem.perm a = (s.mem.mapZero altBase size).perm a) →
      SepWP P target_pc sf ((memRegion altBase size ∗ memMapped altBase size ∗ stackAt s.sp 0x40) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.weaken_pre_frame (P' := stackAt s.sp 0x40 ∗ F) (fun R hm => by have h := hpre R hm; ac_nf at h ⊢) ?_
  have hret' := hret; have_instrs hmmap 0 31
  have hsp_sub_al : ((s.sp - 64#64) &&& 0xf#64 == 0#64) = true := by simpa using s.spAligned_sub 0x40#64 hsp_align
  have hult_max : BitVec.ult 9223372036854775806#64 reqLen = false := by
    change decide (9223372036854775806 < reqLen.toNat) = false
    rw [decide_eq_false_iff_not]; omega
  rw [stackAt_eq_cells s.sp 8]; unfold_stack_cells 8
  refine hb_step_stp64_perm (ea2 := s.sp - 56#64) hpc hrun hf_0
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_align])
    (show evalAddrMode s (.PreIndex .sp 0xffffffffffffffc0#64) = (s.sp - 64#64, some (.sp, s.sp - 64#64)) by simp [evalAddrMode, arm64_norm, bv_lin_norm])
    (by bv_lin) rfl rfl (by wp_sep_access) (by wp_sep_access) fun m1 hm1 => ?_
  clear hret; wp_steps 3
  refine hb_step_stp64_perm (ea := s.sp - 48#64) (ea2 := s.sp - 40#64) (wb := none)
    (by hb_wp_simp) (by hb_wp_simp) hf_4
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, wp_norm, arm64_norm] using hsp_sub_al)
    (by simp [evalAddrMode, wp_norm, arm64_norm, bv_lin_norm])
    (by bv_lin) rfl rfl (by wp_sep_access) (by wp_sep_access) fun m2 hm2 => ?_
  wp_steps 4
  refine hb_step_stp64_perm (ea := s.sp - 32#64) (ea2 := s.sp - 24#64) (wb := none)
    (by hb_wp_simp) (by hb_wp_simp) hf_9
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, wp_norm, arm64_norm] using hsp_sub_al)
    (by simp [evalAddrMode, wp_norm, arm64_norm, bv_lin_norm])
    (by bv_lin) rfl rfl (by wp_sep_access) (by wp_sep_access) fun m3 hm3 => ?_
  wp_steps 9
  have hm3_perm : ∀ a, m3.perm a = s.mem.perm a := fun a =>
    (congrFun hm3 a).trans ((congrFun hm2 a).trans (congrFun hm1 a))
  have hgap3 : ∃ gap : BitVec 64, 65536 ≤ gap.toNat ∧ gap.toNat % 4096 = 0 ∧ gap.toNat + size ≤ 2 ^ 48 ∧ m3.canMap gap size = true := by
    rcases hgap with ⟨gap, h1, h2, h3, h4⟩
    exact ⟨gap, h1, h2, h3, (canMap_congr hm3_perm gap size).trans h4⟩
  refine step_svc_mmap_anon_stack hsvc (pc := S.mmapWrapperAddr + 76#64) (reqLen := reqLen) (size := size)
    (by hb_wp_simp) (by hb_wp_simp) hf_19 (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
    (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) hlen0 hsz_eq hpos hal (by simpa [wp_norm, arm64_norm] using hphys) hgap3
    fun altBase hbase4k hbaseAl hbaseFit hbaseMap3 => ?_
  have hbaseMap : s.mem.canMap altBase size = true := (canMap_congr hm3_perm altBase size).symm.trans hbaseMap3
  have hne_adds1 : ConditionHolds .NE (addsPState64 altBase 1#64) = true := cond_ne_adds1_true (by omega)
  wp_steps 6
  refine hb_step_b_to (pc := S.mmapWrapperAddr + 120#64) (dst := L.syscallRetAddr) (by hb_wp_simp) (by hb_wp_simp) hf_30 ?_
  refine step_hb_syscallRet_nonneg hret' (ret_pc := ret_pc) (x0v := altBase)
    (F := memRegion altBase size ∗ memMapped altBase size ∗ ((s.sp - 64#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 56#64) ↦₆₄ s.readReg64 (.gpr 30#5)) ∗
      ((s.sp - 48#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗ ((s.sp - 40#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ F)
    (fun R hm => by
      simp only [wp_norm, arm64_norm] at hm ⊢
      rw [stackAt_eq_cells s.sp 4]; fold_stack_cells)
    (by hb_wp_simp) (by hb_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm, bv_lin_norm] using hsp_align)
    (by hb_wp_simp) (by hb_wp_simp) (by omega)
    fun sf hpc_f hrun_f hsp_f hsp_al_f hcs_f hx0_f hnv_f hvm_f => ?_
  wp_conv_pre => simp only [wp_norm, arm64_norm]; rw [stackAt_eq_cells s.sp 4]
  unfold_stack_cells 4
  refine SepWP.weaken_pre_frame (P' := (memRegion altBase size ∗ memMapped altBase size ∗ stackAt s.sp 0x40) ∗ F)
    (fun R hm => by rw [stackAt_eq_cells s.sp 8]; fold_stack_cells) ?_
  have hnv_all : HbNonVmFields s sf := (by
    simp only [hbNonVm_pc_r, hbNonVm_w64_r, hbNonVm_ps_r, hbNonVm_or_r, hbNonVm_phys_r, hbNonVm_mem_r]
    exact HbNonVmFields.rfl s : HbNonVmFields s _).trans hnv_f
  refine hnext sf altBase hbase4k hbaseAl hbaseFit hbaseMap hpc_f hrun_f
    (by simpa [wp_norm, arm64_norm, bv_lin_norm] using hsp_f) hsp_al_f ?_ hx0_f hnv_all
    (by simpa [wp_norm, arm64_norm] using hvm_f.physMemAvail_eq)
    (by simpa [wp_norm, arm64_norm] using hvm_f.brk_eq)
    (by simpa [wp_norm, arm64_norm] using hvm_f.brkStart_eq)
    fun a => ?_
  · rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs_f with ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, gv⟩
    simp only [wp_norm, arm64_norm] at g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 gv
    rw [CalleeSavedPreserved.iff_regs]; simp [wp_norm, arm64_norm, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, gv]
  · rw [hvm_f.perm_eq a]
    simp only [wp_norm, arm64_norm, Memory.perm_mapZero, hm3_perm a]

theorem step_hb_ldarb {prog : Program} {target_pc pc ea : BitVec 64} {v : BitVec 8}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rn rt : Reg} (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldarStlr .B8 true rn rt))
    (hsp : checkRegSPAligned s rn = true) (haddr : s.readReg64 rn = ea)
    (hload : SepLoad8 ea P v)
    (hnext : SepWP prog target_pc ((s.writeReg64 rt (v.zeroExtend 64)).setPC (pc + 4#64)) P post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP at hnext ⊢; intro R hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.ldarStlr .B8 true rn rt) s = (s.writeReg64 rt (v.zeroExtend 64)).setPC (pc + 4#64) := by
    simp [Program.evalInst, execInstWithSvc, Memory.readSized, State.writeReg, State.advancePC, State.setPC,
      MemWidth.isAligned, MemWidth.bytes, hsp, haddr, hload.load hm, hload.readable hm, hpc]
  rw [hstep]; exact hnext R hm

theorem step_hb_stlrb {prog : Program} {target_pc pc ea : BitVec 64} {val : BitVec 8}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rn rt : Reg} (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldarStlr .B8 false rn rt))
    (hsp : checkRegSPAligned s rn = true) (haddr : s.readReg64 rn = ea)
    (hval : (s.readReg64 rt).truncate 8 = val) (hstore : SepStore8 ea val P P')
    (hnext : SepWP prog target_pc ((s.setMem (s.mem.write8 ea val)).setPC (pc + 4#64)) P' post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP at hnext ⊢; intro R hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.ldarStlr .B8 false rn rt) s = (s.setMem (s.mem.write8 ea val)).setPC (pc + 4#64) := by
    rw [← hval]
    simp [Program.evalInst, execInstWithSvc, Memory.writeSized, State.advancePC, State.setPC, State.setMem,
      MemWidth.isAligned, MemWidth.bytes, hsp, haddr, hstore.writable hm, hpc]
  rw [hstep]; exact hnext R (hstore.store hm)

private theorem hb_seq_nonVm {prog : Program} {mid target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hext : ∀ pc, prog.externAt? pc = none) (hsvc : prog.svc = Syscall.standard)
    (h : SepWP (prog.withSvc nonVmSvc) mid s P
      (fun sm Pm => VmFieldsPreserved s sm → SepWP prog target sm Pm post oom)) :
    SepWP prog target s P post oom := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  have hL' : (prog.withSvc nonVmSvc).CodeLoaded s.mem := (Program.withSvc_codeLoaded ..).mpr hL
  rcases SepWP.to_reaches_pc h hm hL' with ⟨sm, hst1, ⟨_, hrun_m, Pm, hmm, hcont⟩ | ⟨_, hoom⟩⟩
  · rcases Steps.of_nonVm_running hext hsvc hst1 hrun_m with ⟨hst1P, hvm⟩
    obtain ⟨sf, hst2, hout⟩ := SepWP.to_reaches_pc (hcont hvm) hmm (hst1P.codeLoaded hL)
    exact ⟨sf, hst1P.trans hst2, hout⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩; exact False.elim hf

private theorem hb_done_nonVm {prog : Program} {mid : BitVec 64} {s sm : State} {Pm : SepProp}
    {post : State → SepProp → Prop}
    (hpc : sm.pc = mid) (hrun : sm.status = .Running)
    (hnext : VmFieldsPreserved s sm → post sm Pm) :
    SepWP prog mid sm Pm (fun sm' Pm' => VmFieldsPreserved s sm' → post sm' Pm') :=
  SepWP.done hpc hrun hnext

private theorem hbAltstackReqSz_bv_eq_csel (entries : List (BitVec 64 × BitVec 64)) :
    (if BitVec.ult 12288#64 (((entries.find? (·.1 == 51#64)).map Prod.snd).getD 0#64)
     then ((entries.find? (·.1 == 51#64)).map Prod.snd).getD 0#64
     else 12288#64) = BitVec.ofNat 64 (hbAltstackReqSz entries) := by
  dsimp only [hbAltstackReqSz]
  split <;> apply BitVec.eq_of_toNat_eq
  · next h =>
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (((entries.find? (·.1 == 51#64)).map Prod.snd).getD 0#64).isLt; omega)]
    omega
  · next h =>
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at h
    change 12288 = (max (((entries.find? (·.1 == 51#64)).map Prod.snd).getD 0#64).toNat 12288) % 18446744073709551616
    omega

private theorem stackAt_40_eq_10_30 (sp : BitVec 64) :
    stackAt sp 0x40 = stackAt (sp - 0x30#64) 0x10 ∗ stackAt sp 0x30 := by
  rw [stackAt_split_cells sp 0x10 6 (by decide), ← stackAt_eq_cells sp 6]

private theorem stackAt_40_eq_20_20 (sp : BitVec 64) :
    stackAt sp 0x40 = stackAt (sp - 0x20#64) 0x20 ∗ stackAt sp 0x20 := by
  rw [stackAt_split_cells sp 0x20 4 (by decide), ← stackAt_eq_cells sp 4]

private theorem stackAt_30_eq_10_20 (sp : BitVec 64) :
    stackAt sp 0x30 = stackAt (sp - 0x20#64) 0x10 ∗ stackAt sp 0x20 := by
  rw [stackAt_split_cells sp 0x10 4 (by decide), ← stackAt_eq_cells sp 4]

private theorem hb_hasInstrs_withSvc {P : Program} {svc : State → State} {base : BitVec 64}
    {is : List Instr} (h : hasInstrs P base is) : hasInstrs (P.withSvc svc) base is := by
  intro i hi; rw [Program.withSvc_fetch]; exact h i hi

abbrev sigaltstackInstrs (L : StdBinaryLayout) (S : HbStartupLayout) : List Instr :=
  decodeWords [0xa9bf7bfd#32, 0x910003fd#32, 0xb4000100#32, 0xb9400802#32,
    0x370800a2#32, 0xf9400804#32, 0xd282ffe3#32, 0xeb03009f#32,
    0x540000e9#32, 0x37000182#32, 0xd2801088#32, 0xd4000001#32] ++
  [.bl (L.syscallRetAddr - (S.sigaltstackAddr + 0x30#64))] ++
  decodeWords [0xa8c17bfd#32, 0xd65f03c0#32]

abbrev makeHandlerHeadInstrs (C : HbCliLayout) : List Instr :=
  let mh := C.makeStackHandlerAddr
  decodeWords [0xd10243ff#32, 0xa9067bfd#32, 0xf9003bf5#32, 0xa9084ff4#32, 0x910183fd#32] ++
  [iAdrp .x8 (mh + 0x14#64) C.needAltstackAddr, iAddLo12 .x8 .x8 C.needAltstackAddr] ++
  decodeWords [0x08dffd08#32, 0x34000a28#32, 0x370004a0#32]

abbrev makeHandlerBodyInstrs (C : HbCliLayout) (S : HbStartupLayout) : List Instr :=
  let L := C.std; let mh := C.makeStackHandlerAddr; let mhb := mh + 0xb8#64
  decodeWords [0x910003e1#32, 0xaa1f03e0#32, 0xa9007fff#32, 0xf9000bff#32] ++
  [iBl (mhb + 0x10#64) S.sigaltstackAddr] ++
  decodeWords [0x394023e8#32, 0xaa1f03e0#32, 0x360803e8#32, 0x52800660#32] ++
  [ iBl (mhb + 0x24#64) L.getauxvalAddr, iAdrp .x8 (mhb + 0x28#64) L.pageSizeGlobalAddr,
    decodeWord 0xf1400c1f#32, decodeWord 0x52860009#32, iLdr64Lo12 .x19 .x8 L.pageSizeGlobalAddr ] ++
  decodeWords [0x9a898015#32, 0x52800443#32, 0xaa1f03e0#32, 0x52800062#32,
               0x72a00043#32, 0x8b1302a1#32, 0x12800004#32, 0xaa1f03e5#32] ++
  [iBl (mhb + 0x58#64) S.mmapWrapperAddr] ++
  decodeWords [0xb100041f#32, 0x54000320#32, 0xaa1303e1#32, 0x2a1f03e2#32, 0xaa0003f4#32] ++
  [iBl (mhb + 0x70#64) S.mprotectWrapperAddr] ++
  decodeWords [0x35000560#32, 0x8b130288#32, 0x910003e0#32, 0xaa1f03e1#32,
               0xb9000bff#32, 0xf90003e8#32, 0xf9000bf5#32] ++
  [iBl (mhb + 0x90#64) S.sigaltstackAddr] ++
  decodeWords [0xf94003e0#32, 0xa9484ff4#32, 0xf9403bf5#32, 0xa9467bfd#32,
               0x910243ff#32, 0xd65f03c0#32]

private theorem step_hb_make_handler_pre {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc ret_pc auxvAddr : BitVec 64} {entries : List (BitVec 64 × BitVec 64)} {errno0 : BitVec 32}
    (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc)
    (hmh_head : hasInstrs P C.makeStackHandlerAddr (makeHandlerHeadInstrs C))
    (hmh_body : hasInstrs P (C.makeStackHandlerAddr + 0xb8#64) (makeHandlerBodyInstrs C S))
    (hsas : hasInstrs P S.sigaltstackAddr (sigaltstackInstrs C.std S))
    (hauxv : hasInstrs P C.std.getauxvalAddr (getauxvalInstrs C.std))
    (herrno : P.hasCode C.std.errnoLocationAddr [0xd53bd040#32, 0xd1029000#32, 0xd65f03c0#32])
    (hret : P.hasCode C.std.syscallRetAddr syscallRetNonnegWords)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R →
      s.mem ⊨ (((C.needAltstackAddr ↦₈ 1#8) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
        (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ (muslErrnoAddr s ↦₃₂ errno0) ∗
        (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64)) ∗ stackAt s.sp 0xd0) ∗ (F ∗ R))
    (hpc : s.pc = C.makeStackHandlerAddr) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hsp_lo : 0xd0 ≤ s.sp.toNat)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = 1#64)
    (hsas0 : s.sigAltStack = {}) (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64)
    (healign : MemWidth.isAligned .W32 (muslErrnoAddr s) = true)
    (hnext : ∀ (s2 : State) (errno1 : BitVec 32) (w_mh3 : BitVec 64),
      s2.pc = C.makeStackHandlerAddr + 272#64 → s2.status = .Running →
      s2.sp = s.sp - 144#64 → s2.spAligned = true →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = BitVec.ofNat 64 (hbAltstackReqSz entries) + 4096#64 →
      s2.readReg64 .x2 = 3#64 → s2.readReg64 .x3 = 131106#64 →
      s2.readReg32 .x4 = 0xffffffff#32 → s2.readReg64 .x5 = 0#64 →
      CalleeSavedPreserved
        (((s.writeReg64 (.gpr 29#5) (s.sp - 48#64)).writeReg64 (.gpr 19#5) 4096#64).writeReg64
          (.gpr 21#5) (BitVec.ofNat 64 (hbAltstackReqSz entries))) s2 →
      HbNonVmFields s s2 →
      SepWP P target_pc s2
        (((stackAt (s.sp - 144#64) 0x40 ∗
           ((s.sp - 144#64) ↦₆₄ 0#64) ∗ ((s.sp - 136#64) ↦₃₂ 2#32) ∗ ((s.sp - 132#64) ↦₃₂ 0#32) ∗ ((s.sp - 128#64) ↦₆₄ 0#64) ∗
           memRegion (s.sp - BitVec.ofNat 64 120) 72 ∗
           ((s.sp - 48#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 40#64) ↦₆₄ ret_pc) ∗
           ((s.sp - 32#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ ((s.sp - 24#64) ↦₆₄ w_mh3) ∗
           ((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
           (C.needAltstackAddr ↦₈ 1#8) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
           (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ (muslErrnoAddr s2 ↦₃₂ errno1) ∗
           (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64)) ∗ F)) post oom) :
    SepWP P target_pc s Pre post oom := by
  have huoss_ne : s.sp - 144#64 ≠ 0#64 := by intro h; have := congrArg BitVec.toNat h; bv_omega
  have huoss_fit : (s.sp - 144#64).toNat + 24 ≤ 2 ^ 64 := by bv_omega
  have huoss8 : (s.sp - 144#64) + 8#64 = s.sp - 136#64 := by bv_lin
  have huoss12 : (s.sp - 144#64) + 12#64 = s.sp - 132#64 := by bv_lin
  have huoss16 : (s.sp - 144#64) + 16#64 = s.sp - 128#64 := by bv_lin
  have hsp_sub_al : ((s.sp - 144#64) &&& 0xf#64 == 0#64) = true := by
    simpa using s.spAligned_sub 0x90#64 hsp_align
  refine SepWP.weaken_pre_frame
    (P' := (((C.needAltstackAddr ↦₈ 1#8) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
      (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ (muslErrnoAddr s ↦₃₂ errno0) ∗
      (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64)) ∗ stackAt s.sp 0xd0) ∗ F)
    (fun R hm => by rw [sepConj_assoc]; exact hpre R hm) ?_
  wp_conv_pre =>
    rw [stackAt_split_cells s.sp 0x40 18 (by decide),
        cells_split_sub s.sp 144 120 3 15,
        cells_split_sub s.sp 120 48 9 6,
        ← memRegion_cells (s.sp - BitVec.ofNat 64 120) 9 (by decide)]
  unfold_stack_cells 9
  have hret' := hret
  have_instrs hmh_head 0 10
  wp_steps 7
  refine step_hb_ldarb (pc := C.makeStackHandlerAddr + 28#64) (ea := C.needAltstackAddr) (v := 1#8)
    (by hb_wp_simp) (by hb_wp_simp) hf_7 rfl
    (by hb_wp_simp) (by wp_sep_access) ?_
  wp_steps 2
  clear hf_0 hf_1 hf_2 hf_3 hf_4 hf_5 hf_6 hf_7 hf_8 hf_9
  have_instrs hmh_body 0 22
  clear hret; wp_steps 4
  refine hb_step_bl_to (pc := C.makeStackHandlerAddr + 200#64) (dst := S.sigaltstackAddr)
    (by hb_wp_simp) (by hb_wp_simp) hf_4 ?_
  rw [show C.makeStackHandlerAddr + 200#64 + 4#64 = C.makeStackHandlerAddr + 204#64 by bv_lin]
  refine step_hb_sigaltstack_probe hsvc hsas hret' (ret_pc := C.makeStackHandlerAddr + 204#64)
    (uoss := s.sp - 144#64) (v0 := 0#64) (v1 := 0#64) (v2 := 0#64) (F := ?_)
    (fun R hm => by
      simp only [wp_norm, arm64_norm] at hm ⊢
      rw [stackAt_40_eq_10_30 (s.sp - 144#64)] at hm
      revert hm; sep_frame)
    rfl (by hb_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_sub_al)
    (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
    huoss_ne huoss_fit (by simp [wp_norm, arm64_norm, hsas0])
    fun s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 _ hnv1 => ?_
  have hsp1_eq : s1.sp = s.sp - 144#64 := by simpa [wp_norm, arm64_norm, bv_lin_norm] using hsp1
  have htp1_eq : s1.tpidrEl0 = s.tpidrEl0 := by have h := hnv1.2.2.1; simp only [wp_norm, arm64_norm] at h; exact h
  have hsp1_raw : (s1.sp &&& 15#64 == 0#64) = true := hsp_al1
  clear hsp1
  wp_conv_pre => simp only [wp_norm, arm64_norm]; rw [← hsp1_eq]
  wp_steps 4
  refine hb_step_bl_to (pc := C.makeStackHandlerAddr + 220#64) (dst := C.std.getauxvalAddr)
    (by hb_wp_simp) (by hb_wp_simp) hf_9 ?_
  rw [show C.makeStackHandlerAddr + 220#64 + 4#64 = C.makeStackHandlerAddr + 224#64 by bv_lin]
  refine step_hb_getauxval_opt hauxv herrno (ret_pc := C.makeStackHandlerAddr + 224#64)
    (tag := 51#64) (auxvAddr := auxvAddr) (entries := entries) (errno0 := errno0) (F := ?_)
    (fun R hm => by
      simp only [wp_norm, arm64_norm] at hm ⊢
      rw [show muslErrnoAddr (((s1.writeReg64 (.gpr 8#5) 2#64).writeReg64 (.gpr 0#5) 51#64).writeReg64 (.gpr 30#5) (C.makeStackHandlerAddr + 224#64) |>.setPC C.std.getauxvalAddr) = muslErrnoAddr s by
        unfold muslErrnoAddr; simp [wp_norm, arm64_norm, htp1_eq]]
      rw [hsp1_eq, stackAt_30_eq_10_20 (s.sp - 144#64)] at hm
      rw [hsp1_eq]; revert hm; sep_frame)
    rfl (by hb_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al1)
    (by hb_wp_simp) (by hb_wp_simp) (by decide) (by decide) hnonull
    (by unfold muslErrnoAddr at healign ⊢; simpa [wp_norm, arm64_norm, htp1_eq] using healign)
    fun s2 errno1 hpc2 hrun2 hsp2 hsp_al2 hx0_2 hcs2 hnv2 => ?_
  have hsp2_eq : s2.sp = s.sp - 144#64 := by simpa [wp_norm, arm64_norm, hsp1_eq] using hsp2
  have hsp2_raw : (s2.sp &&& 15#64 == 0#64) = true := hsp_al2
  clear hsp2
  wp_steps 12
  have hnv01 : HbNonVmFields s s1 := (by hb_nv_rfl s : HbNonVmFields s _).trans hnv1
  have hnv12 : HbNonVmFields s1 s2 := (by hb_nv_rfl s1 : HbNonVmFields s1 _).trans hnv2
  refine SepWP.weaken_pre_frame
    (P' := ((stackAt (s.sp - 144#64) 0x40 ∗
      ((s.sp - 144#64) ↦₆₄ 0#64) ∗ ((s.sp - 136#64) ↦₃₂ 2#32) ∗ ((s.sp - 132#64) ↦₃₂ 0#32) ∗ ((s.sp - 128#64) ↦₆₄ 0#64) ∗
      memRegion (s.sp - BitVec.ofNat 64 120) 72 ∗
      ((s.sp - 48#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((s.sp - 40#64) ↦₆₄ ret_pc) ∗
      ((s.sp - 32#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗ ((s.sp - 24#64) ↦₆₄ _) ∗
      ((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗ ((s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗
      (C.needAltstackAddr ↦₈ 1#8) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
      (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ (muslErrnoAddr s2 ↦₃₂ errno1) ∗
      (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64)) ∗ F))
    (fun R hm => by
      simp only [wp_norm, arm64_norm, hsp1_eq] at hm ⊢
      rw [stackAt_40_eq_10_30 (s.sp - 144#64), stackAt_30_eq_10_20 (s.sp - 144#64)]
      simp only [bv_lin_norm] at hm ⊢
      revert hm; sep_entail) ?_
  refine hnext _ errno1 _ (by hb_wp_simp) (by hb_wp_simp)
    (by simp [wp_norm, arm64_norm, hsp2_eq])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al2)
    (by hb_wp_simp)
    (by simp [wp_norm, arm64_norm, hbAltstackReqSz_bv_eq_csel])
    (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
    ?_ ((hnv01.trans hnv12).trans ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs1 with ⟨_, g20_1, _, g22_1, g23_1, g24_1, g25_1, g26_1, g27_1, g28_1, g29_1, gv_1⟩
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs2 with ⟨_, g20_2, _, g22_2, g23_2, g24_2, g25_2, g26_2, g27_2, g28_2, g29_2, gv_2⟩
  simp only [wp_norm, arm64_norm, bv_lin_norm] at g20_1 g22_1 g23_1 g24_1 g25_1 g26_1 g27_1 g28_1 g29_1 gv_1 g20_2 g22_2 g23_2 g24_2 g25_2 g26_2 g27_2 g28_2 g29_2 gv_2
  rw [CalleeSavedPreserved.iff_regs]
  simp [wp_norm, arm64_norm, hbAltstackReqSz_bv_eq_csel,
    g20_2, g22_2, g23_2, g24_2, g25_2, g26_2, g27_2, g28_2, g29_2, gv_2,
    g20_1, g22_1, g23_1, g24_1, g25_1, g26_1, g27_1, g28_1, g29_1, gv_1]

private theorem step_hb_make_handler_post {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc ret_pc auxvAddr altBase reqBv w_mh3 : BitVec 64} {entries : List (BitVec 64 × BitVec 64)} {errno1 : BitVec 32}
    (hsvc : P.svc = Syscall.standard ∨ P.svc = nonVmSvc)
    (hmh_body : hasInstrs P (C.makeStackHandlerAddr + 0xb8#64) (makeHandlerBodyInstrs C S))
    (hsas : hasInstrs P S.sigaltstackAddr (sigaltstackInstrs C.std S))
    (hret : P.hasCode C.std.syscallRetAddr syscallRetNonnegWords)
    {s s4 : State} {Pre4 F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre4 : ∀ R : SepProp, s4.mem ⊨ Pre4 ∗ R →
      s4.mem ⊨ ((((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64) ∗ memRegionProtNone altBase 4096 ∗ stackAt (s.sp - 144#64) 0x30) ∗
        (memRegion (altBase + 4096#64) (hbExpectedAltRawSz entries) ∗ stackAt (s.sp - 144#64 - 0x30#64) 0x10 ∗
          ((s.sp - 144#64) ↦₆₄ 0#64 ∗ (s.sp - 136#64) ↦₃₂ 2#32 ∗ (s.sp - 132#64) ↦₃₂ 0#32 ∗
            (s.sp - 128#64) ↦₆₄ 0#64 ∗ memRegion (s.sp - BitVec.ofNat 64 120) 72 ∗
            (s.sp - 48#64) ↦₆₄ s.readReg64 (.gpr 29#5) ∗ (s.sp - 40#64) ↦₆₄ ret_pc ∗
            (s.sp - 32#64) ↦₆₄ s.readReg64 (.gpr 21#5) ∗ (s.sp - 24#64) ↦₆₄ w_mh3 ∗
            (s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 20#5) ∗ (s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 19#5) ∗
            C.needAltstackAddr ↦₈ 1#8 ∗ (C.std.libcAddr + 8#64) ↦₆₄ auxvAddr ∗
            auxvAddr ↦ₛ encodeAuxvBytes entries ∗ muslErrnoAddr s4 ↦₃₂ errno1 ∗
            C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ F)) ∗ R)
    (hpc4 : s4.pc = C.makeStackHandlerAddr + 300#64) (hrun4 : s4.status = .Running)
    (hsp4_eq : s4.sp = s.sp - 144#64) (hsp_align : s.spAligned = true) (hsp_al4 : s4.spAligned = true)
    (hsp_lo : 0xd0 ≤ s.sp.toNat) (hx0_4 : s4.readReg64 .x0 = 0#64)
    (hx19_4 : s4.readReg64 (.gpr 19#5) = 4096#64)
    (hx20_4 : s4.readReg64 (.gpr 20#5) = altBase)
    (hx21_4 : s4.readReg64 (.gpr 21#5) = reqBv)
    (hreq_lo : 6144 ≤ reqBv.toNat) (hsas4 : s4.sigAltStack = {})
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      sf.readReg64 .x0 = altBase + 4096#64 →
      sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      sf.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) →
      CalleeSavedPreserved
        (((((s4.writeReg64 (.gpr 19#5) (s.readReg64 (.gpr 19#5))).writeReg64 (.gpr 20#5) (s.readReg64 (.gpr 20#5))).writeReg64
          (.gpr 21#5) (s.readReg64 (.gpr 21#5))).writeReg64 (.gpr 29#5) (s.readReg64 (.gpr 29#5)))) sf →
      HbNonVmFields (s4.setSigAltStack { sp := altBase + 4096#64, size := reqBv, ssFlags := 0#32 }) sf →
      SepWP P target_pc sf
        (((memRegionProtNone altBase 4096 ∗
           memRegion (altBase + 4096#64) (hbExpectedAltRawSz entries) ∗
           (C.needAltstackAddr ↦₈ 1#8) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
           (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ (muslErrnoAddr sf ↦₃₂ errno1) ∗
           (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64)) ∗ stackAt s.sp 0xd0) ∗ F) post oom) :
    SepWP P target_pc s4 Pre4 post oom := by
  refine SepWP.weaken_pre_frame (P' := _) hpre4 ?_
  have hret' := hret
  have huoss_ne : s.sp - 144#64 ≠ 0#64 := by intro h; have := congrArg BitVec.toNat h; bv_omega
  have huoss_fit : (s.sp - 144#64).toNat + 24 ≤ 2 ^ 64 := by bv_omega
  have huoss8 : (s.sp - 144#64) + 8#64 = s.sp - 136#64 := by bv_lin
  have huoss12 : (s.sp - 144#64) + 12#64 = s.sp - 132#64 := by bv_lin
  have huoss16 : (s.sp - 144#64) + 16#64 = s.sp - 128#64 := by bv_lin
  have hsp4_raw : (s4.sp &&& 15#64 == 0#64) = true := hsp_al4
  have_instrs hmh_body 29 14
  wp_conv_pre => rw [← huoss8, ← huoss16, ← hsp4_eq]
  wp_steps 7
  refine hb_step_bl_to (pc := C.makeStackHandlerAddr + 328#64) (dst := S.sigaltstackAddr)
    (by hb_wp_simp) (by hb_wp_simp) hf_36 ?_
  rw [show C.makeStackHandlerAddr + 328#64 + 4#64 = C.makeStackHandlerAddr + 332#64 by bv_lin]
  refine step_hb_sigaltstack_install hsvc hsas hret' (ret_pc := C.makeStackHandlerAddr + 332#64)
    (uss := s.sp - 144#64) (ssSp := altBase + 4096#64) (ssSize := reqBv) (pad := 0#32) (F := ?_)
    (fun R hm => by
      simp only [wp_norm, arm64_norm] at hm ⊢
      revert hm; sep_frame)
    rfl (by hb_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al4)
    (by hb_wp_simp)
    (by simp [wp_norm, arm64_norm])
    (by hb_wp_simp) huoss_ne huoss_fit hreq_lo
    (by simp [wp_norm, arm64_norm, hsas4])
    fun s5 hpc5 hrun5 hsp5 hsp_al5 hcs5 _ hnv5 => ?_
  have hsp5_eq : s5.sp = s.sp - 144#64 := by simpa [wp_norm, arm64_norm, hsp4_eq] using hsp5
  have hsp5_raw : (s5.sp &&& 15#64 == 0#64) = true := hsp_al5
  have hsp5_60 : s5.sp + 96#64 = s.sp - 48#64 := by rw [hsp5_eq]; bv_lin
  have hsp5_68 : s5.sp + 96#64 + 8#64 = s.sp - 40#64 := by rw [hsp5_eq]; bv_lin
  have hsp5_70 : s5.sp + 112#64 = s.sp - 32#64 := by rw [hsp5_eq]; bv_lin
  have hsp5_80 : s5.sp + 128#64 = s.sp - 16#64 := by rw [hsp5_eq]; bv_lin
  have hsp5_88 : s5.sp + 128#64 + 8#64 = s.sp - 8#64 := by rw [hsp5_eq]; bv_lin
  have hsp5_end : s5.sp + 144#64 = s.sp := by rw [hsp5_eq]; bv_lin
  clear hsp5
  wp_conv_pre =>
    simp only [wp_norm, arm64_norm]
    rw [← hsp5_60, ← hsp5_68, ← hsp5_70, ← hsp5_80, ← hsp5_88,
        show (s.sp - 144#64) ↦₆₄ (altBase + 4096#64) = s5.sp ↦₆₄ (altBase + 4096#64) by rw [hsp5_eq]]
  wp_steps 6
  have htp_sf : muslErrnoAddr s4 = muslErrnoAddr ((((((s5.writeReg64 (.gpr 0#5) (altBase + 4096#64)).writeReg64 (.gpr 20#5) (s.readReg64 (.gpr 20#5))).writeReg64 (.gpr 19#5) (s.readReg64 (.gpr 19#5))).writeReg64 (.gpr 21#5) (s.readReg64 (.gpr 21#5))).writeReg64 (.gpr 29#5) (s.readReg64 (.gpr 29#5))).writeReg64 (.gpr 30#5) ret_pc |>.writeReg64 .sp s.sp |>.setPC ret_pc) := by
    unfold muslErrnoAddr
    have htp45 : s5.tpidrEl0 = s4.tpidrEl0 := by have h := hnv5.2.2.1; simp only [wp_norm, arm64_norm, State.setSigAltStack] at h; exact h
    simp [wp_norm, arm64_norm, htp45]
  refine SepWP.weaken_pre_frame
    (P' := (((memRegionProtNone altBase 4096 ∗
      memRegion (altBase + 4096#64) (hbExpectedAltRawSz entries) ∗
      (C.needAltstackAddr ↦₈ 1#8) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
      (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ (muslErrnoAddr s4 ↦₃₂ errno1) ∗
      (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64)) ∗ stackAt s.sp 0xd0) ∗ F))
    (fun R hm => by
      simp only [State.mem_setPC, State.mem_writeReg64] at hm ⊢
      rw [hsp5_68, hsp5_60, hsp5_88, hsp5_80, hsp5_70, hsp5_eq, hsp4_eq] at hm
      have hpair : (((s.sp - 136#64) ↦₃₂ 0#32) ∗ ((s.sp - 132#64) ↦₃₂ 0#32)) = ((s.sp - 136#64) ↦₆₄ 0#64) := by
        rw [show s.sp - 132#64 = (s.sp - 136#64) + 4#64 by bv_lin, pointsTo32_pair]
        rfl
      have hm' : s5.mem ⊨ ((memRegionProtNone altBase 4096 ∗ memRegion (altBase + 4096#64) (hbExpectedAltRawSz entries) ∗
        (stackAt (s.sp - 144#64 - 0x30#64) 0x10 ∗ stackAt (s.sp - 144#64) 0x30) ∗ ((s.sp - 144#64) ↦₆₄ (altBase + 4096#64)) ∗
        (((s.sp - 136#64) ↦₃₂ 0#32) ∗ ((s.sp - 132#64) ↦₃₂ 0#32)) ∗ ((s.sp - 128#64) ↦₆₄ reqBv) ∗
        memRegion (s.sp - BitVec.ofNat 64 120) 72 ∗
        ((s.sp - 48#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗
        ((s.sp - 40#64) ↦₆₄ ret_pc) ∗ ((s.sp - 32#64) ↦₆₄ s.readReg64 (.gpr 21#5)) ∗
        ((s.sp - 24#64) ↦₆₄ w_mh3) ∗ ((s.sp - 16#64) ↦₆₄ s.readReg64 (.gpr 20#5)) ∗
        ((s.sp - 8#64) ↦₆₄ s.readReg64 (.gpr 19#5)) ∗ (C.needAltstackAddr ↦₈ 1#8) ∗
        ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗ (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗
        (muslErrnoAddr s4 ↦₃₂ errno1) ∗ (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗
        ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64)) ∗ F) ∗ R := by
        revert hm; sep_entail
      rw [hpair, ← stackAt_40_eq_10_30 (s.sp - 144#64)] at hm'
      rw [stackAt_split_cells s.sp 0x40 18 (by decide),
          cells_split_sub s.sp 144 120 3 15,
          cells_split_sub s.sp 120 48 9 6,
          ← memRegion_cells (s.sp - BitVec.ofNat 64 120) 9 (by decide)]
      revert hm'; fold_stack_cells) ?_
  rw [htp_sf]
  refine hnext _ (by hb_wp_simp) (by simp [wp_norm, arm64_norm, hrun5])
    (by simp [wp_norm, arm64_norm])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align)
    (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
    ?_ ((HbNonVmFields.trans ⟨rfl, rfl, rfl, rfl, rfl⟩ hnv5).trans ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs5 with ⟨_, _, _, g22_5, g23_5, g24_5, g25_5, g26_5, g27_5, g28_5, _, gv_5⟩
  simp only [wp_norm, arm64_norm] at g22_5 g23_5 g24_5 g25_5 g26_5 g27_5 g28_5 gv_5
  rw [CalleeSavedPreserved.iff_regs]
  simp [wp_norm, arm64_norm, g22_5, g23_5, g24_5, g25_5, g26_5, g27_5, g28_5, gv_5]

private theorem HbNonVmFields.setSigAltStack {s0 s1 : State} (sas : SigAltStack) (h : HbNonVmFields s0 s1) :
    HbNonVmFields (s0.setSigAltStack sas) (s1.setSigAltStack sas) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, _root_.rfl⟩

/-- Step `make_handler` (`C.makeStackHandlerAddr`) allocating, guard-protecting, and installing the alternate signal stack. -/
theorem step_hb_make_handler {P : Program} {C : HbCliLayout} {S : HbStartupLayout}
    {target_pc ret_pc auxvAddr : BitVec 64} {entries : List (BitVec 64 × BitVec 64)} {errno0 : BitVec 32}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (hmh_head : hasInstrs P C.makeStackHandlerAddr (makeHandlerHeadInstrs C))
    (hmh_body : hasInstrs P (C.makeStackHandlerAddr + 0xb8#64) (makeHandlerBodyInstrs C S))
    (hsas : hasInstrs P S.sigaltstackAddr (sigaltstackInstrs C.std S))
    (hauxv : hasInstrs P C.std.getauxvalAddr (getauxvalInstrs C.std))
    (herrno : P.hasCode C.std.errnoLocationAddr [0xd53bd040#32, 0xd1029000#32, 0xd65f03c0#32])
    (hmmap : hasInstrs P S.mmapWrapperAddr (mmapWrapperInstrs C.std S))
    (hmprot : hasInstrs P S.mprotectWrapperAddr (mprotectWrapperInstrs C.std S))
    (hret : P.hasCode C.std.syscallRetAddr syscallRetNonnegWords)
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpre : ∀ R : SepProp, s.mem ⊨ Pre ∗ R →
      s.mem ⊨ (((C.needAltstackAddr ↦₈ 1#8) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
        (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ (muslErrnoAddr s ↦₃₂ errno0) ∗
        (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64)) ∗ stackAt s.sp 0xd0) ∗ (F ∗ R))
    (hpc : s.pc = C.makeStackHandlerAddr) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hsp_lo : 0xd0 ≤ s.sp.toNat)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = 1#64)
    (hsas0 : s.sigAltStack = {}) (hnonull : ∀ t v, (t, v) ∈ entries → t ≠ 0#64)
    (hbnd : ∀ e ∈ entries, e.1 = 51#64 → e.2.toNat ≤ 524288)
    (healign : MemWidth.isAligned .W32 (muslErrnoAddr s) = true)
    (hphys : hbExpectedAltRawSz entries + 4096 ≤ s.physMemAvail)
    (hgap : ∃ gap : BitVec 64, 65536 ≤ gap.toNat ∧ gap.toNat % 4096 = 0 ∧
      gap.toNat + (hbExpectedAltRawSz entries + 4096) ≤ 2 ^ 48 ∧
      s.mem.canMap gap (hbExpectedAltRawSz entries + 4096) = true)
    (hnext : ∀ (sf : State) (altBase : BitVec 64) (errno1 : BitVec 32),
      4096 ≤ altBase.toNat → altBase.toNat % 4096 = 0 →
      altBase.toNat + (hbExpectedAltRawSz entries + 4096) ≤ 2 ^ 48 →
      s.mem.canMap altBase (hbExpectedAltRawSz entries + 4096) = true →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
      CalleeSavedPreserved s sf → sf.readReg64 .x0 = altBase + 4096#64 →
      HbNonVmFields (s.setSigAltStack
        { sp := altBase + 4096#64, size := BitVec.ofNat 64 (hbAltstackReqSz entries), ssFlags := 0#32 }) sf →
      sf.physMemAvail = s.physMemAvail - (hbExpectedAltRawSz entries + 4096) →
      sf.brk = s.brk → sf.brkStart = s.brkStart →
      (∀ a, sf.mem.perm a =
        ((s.mem.mapZero altBase (hbExpectedAltRawSz entries + 4096)).setPermNonFrozen altBase 4096 Perm.protNone).perm a) →
      SepWP P target_pc sf
        (((memRegionProtNone altBase 4096 ∗
           memRegion (altBase + 4096#64) (hbExpectedAltRawSz entries) ∗
           memMapped altBase (4096 + hbExpectedAltRawSz entries) ∗
           (C.needAltstackAddr ↦₈ 1#8) ∗ ((C.std.libcAddr + 0x08#64) ↦₆₄ auxvAddr) ∗
           (auxvAddr ↦ₛ encodeAuxvBytes entries) ∗ (muslErrnoAddr sf ↦₃₂ errno1) ∗
           (C.std.pageSizeGlobalAddr ↦₆₄ 4096#64) ∗ ((C.std.libcAddr + 0x30#64) ↦₆₄ 4096#64)) ∗ stackAt s.sp 0xd0) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  have ⟨hal_raw, hlo_raw, hhi_raw⟩ := hbExpectedAltRawSz_spec hbnd
  have hreq_bnd : 12288 ≤ hbAltstackReqSz entries ∧ hbAltstackReqSz entries ≤ 524288 := by
    unfold hbAltstackReqSz
    cases hfind : entries.find? (·.1 == 51#64) with
    | none => simp
    | some kv =>
      have hmem := List.mem_of_find?_eq_some hfind
      have heq : kv.1 = 51#64 := by simpa using List.find?_some hfind
      have hle := hbnd kv hmem heq
      simp only [Option.map_some, Option.getD_some]; omega
  let reqBv := BitVec.ofNat 64 (hbAltstackReqSz entries)
  let reqLen := reqBv + 4096#64
  let mapSz := hbExpectedAltRawSz entries + 4096
  have hreqBv_toNat : reqBv.toNat = hbAltstackReqSz entries := by
    dsimp [reqBv]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hreq_lo : 6144 ≤ reqBv.toNat := by omega
  have hreqLen_toNat : reqLen.toNat = hbAltstackReqSz entries + 4096 := by
    dsimp [reqLen]; rw [hreqBv_toNat, Nat.mod_eq_of_lt (by omega)]
  have hreqLen_ne : reqLen ≠ 0#64 := by
    intro h; have h0 : reqLen.toNat = 0 := congrArg BitVec.toNat h; omega
  have hreqLen_hi : reqLen.toNat ≤ 528384 := by omega
  have hsz_eq : Arm64.pageAlignUp reqLen.toNat = mapSz := by
    rw [hreqLen_toNat, hbPageAlignUp_add_page]; rfl
  have hmap_pos : 0 < mapSz := by omega
  have hmap_al : mapSz % 4096 = 0 := by omega
  have hmap_hi : mapSz ≤ 528384 := by omega
  have hmap_split : mapSz = 4096 + hbExpectedAltRawSz entries := by omega
  have hmap_fit64 : 4096 + hbExpectedAltRawSz entries ≤ 2 ^ 64 := by omega
  have hmh_head' := hb_hasInstrs_withSvc (svc := nonVmSvc) hmh_head
  have hmh_body' := hb_hasInstrs_withSvc (svc := nonVmSvc) hmh_body
  have hsas' := hb_hasInstrs_withSvc (svc := nonVmSvc) hsas
  have hauxv' := hb_hasInstrs_withSvc (svc := nonVmSvc) hauxv
  refine hb_seq_nonVm (mid := C.makeStackHandlerAddr + 272#64) hext hsvc ?_
  refine step_hb_make_handler_pre (Or.inr rfl) hmh_head' hmh_body' hsas' hauxv' herrno hret
    hpre hpc hrun hsp_align hsp_lo hlr hx0 hsas0 hnonull healign
    fun s2 errno1 w_mh3 hpc2 hrun2 hsp2 hsp_al2 hx0_2 hx1_2 hx2_2 hx3_2 hx4_2 hx5_2 hcs2 hnv2 => ?_
  refine hb_done_nonVm hpc2 hrun2 fun hvm2 => ?_
  have_instrs hmh_body 22 7
  refine hb_step_bl_to (pc := C.makeStackHandlerAddr + 272#64) (dst := S.mmapWrapperAddr)
    hpc2 hrun2 hf_22 ?_
  rw [show C.makeStackHandlerAddr + 272#64 + 4#64 = C.makeStackHandlerAddr + 276#64 by bv_lin]
  have hgap2 : ∃ gap : BitVec 64, 65536 ≤ gap.toNat ∧ gap.toNat % 4096 = 0 ∧
      gap.toNat + mapSz ≤ 2 ^ 48 ∧ ((s2.writeReg64 .lr (C.makeStackHandlerAddr + 276#64)).setPC S.mmapWrapperAddr).mem.canMap gap mapSz = true := by
    rcases hgap with ⟨gap, h1, h2, h3, h4⟩
    exact ⟨gap, h1, h2, h3, (canMap_congr hvm2.perm_eq gap mapSz).trans h4⟩
  refine step_hb_mmap_anon_zero hsvc hmmap hret (ret_pc := C.makeStackHandlerAddr + 276#64)
    (reqLen := reqLen) (size := mapSz) (F := ?_)
    (fun R hm => by simp only [wp_norm, arm64_norm, hsp2] at hm ⊢; revert hm; sep_frame)
    rfl (by simp [wp_norm, arm64_norm, hrun2])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al2)
    (by hb_wp_simp) (by simp [wp_norm, arm64_norm, hx0_2])
    (by simp [wp_norm, arm64_norm, hx1_2, reqLen, reqBv])
    (by simp [wp_norm, arm64_norm, hx2_2]) (by simp [wp_norm, arm64_norm, hx3_2])
    (by simpa [State.readReg32, wp_norm, arm64_norm] using hx4_2)
    (by simp [wp_norm, arm64_norm, hx5_2])
    hreqLen_ne hreqLen_hi hsz_eq hmap_pos hmap_al hmap_hi
    (by simpa [wp_norm, arm64_norm, hvm2.physMemAvail_eq] using hphys) hgap2
    fun s3 altBase hbase4k hbaseAl hbaseFit hbaseMap2 hpc3 hrun3 hsp3 hsp_al3 hcs3 hx0_3 hnv3 hphys3 hbrk3 hbrkS3 hperm3 => ?_
  have hbaseMap : s.mem.canMap altBase mapSz = true :=
    (canMap_congr hvm2.perm_eq altBase mapSz).symm.trans hbaseMap2
  have hsp3_eq : s3.sp = s.sp - 144#64 := by simpa [wp_norm, arm64_norm, hsp2] using hsp3
  have hsp3_raw : (s3.sp &&& 15#64 == 0#64) = true := hsp_al3
  have hx19_3 : s3.readReg64 (.gpr 19#5) = 4096#64 := by
    have h1 := hcs2.readReg64_x19; have h2 := hcs3.readReg64_x19
    simpa [wp_norm, arm64_norm] using h2.trans h1
  have hva4k : altBase.toNat + 4096 ≤ 2 ^ 48 :=
    Nat.le_trans (Nat.add_le_add_left (Nat.le_add_left 4096 (hbExpectedAltRawSz entries)) altBase.toNat) hbaseFit
  have heq_adds1 : ConditionHolds .EQ (addsPState64 altBase 1#64) = false :=
    cond_eq_adds1_false (Nat.le_trans (Nat.add_le_add_left (by decide : 1 ≤ 4096) altBase.toNat)
      (Nat.le_trans hva4k (by decide : 2 ^ 48 ≤ 2 ^ 64 - 1)))
  clear hsp3; wp_steps 5
  refine hb_step_bl_to (pc := C.makeStackHandlerAddr + 296#64) (dst := S.mprotectWrapperAddr)
    (by hb_wp_simp) (by hb_wp_simp) hf_28 ?_
  rw [show C.makeStackHandlerAddr + 296#64 + 4#64 = C.makeStackHandlerAddr + 300#64 by bv_lin]
  refine step_hb_mprotect_none hsvc hmprot hret (ret_pc := C.makeStackHandlerAddr + 300#64)
    (altBase := altBase) (F := ?_)
    (fun R hm => by
      simp only [wp_norm, arm64_norm, hsp2, hsp3_eq] at hm ⊢
      rw [hmap_split,
          memRegion_split altBase 4096 (hbExpectedAltRawSz entries) hmap_fit64,
          stackAt_40_eq_10_30 (s.sp - 144#64)] at hm
      revert hm; sep_frame)
    rfl (by hb_wp_simp)
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al3)
    (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp) (by hb_wp_simp)
    hbaseAl hva4k
    fun s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hx0_4 hnv4 hphys4 hbrk4 hbrkS4 hperm4 => ?_
  have hsp4_eq : s4.sp = s.sp - 144#64 := by simpa [wp_norm, arm64_norm, hsp3_eq] using hsp4
  have hx19_4 : s4.readReg64 (.gpr 19#5) = 4096#64 := by
    have := hcs4.readReg64_x19; simpa [wp_norm, arm64_norm, hx19_3] using this
  have hx20_4 : s4.readReg64 (.gpr 20#5) = altBase := by
    have := hcs4.readReg64_x20; simpa [wp_norm, arm64_norm, hx0_3] using this
  have hx21_4 : s4.readReg64 (.gpr 21#5) = reqBv := by
    have h1 := hcs2.readReg64_x21; have h2 := hcs3.readReg64_x21; have h3 := hcs4.readReg64_x21
    simp only [wp_norm, arm64_norm] at h1 h2 h3
    exact h3.trans (h2.trans h1)
  have hnv23 : HbNonVmFields s2 s3 := (by hb_nv_rfl s2 : HbNonVmFields s2 _).trans hnv3
  have hnv34 : HbNonVmFields s3 s4 := (by hb_nv_rfl s3 : HbNonVmFields s3 _).trans hnv4
  have hnv04 : HbNonVmFields s s4 := hnv2.trans (hnv23.trans hnv34)
  have hsas4 : s4.sigAltStack = {} := hnv04.2.2.2.2.trans hsas0
  have htp24 : muslErrnoAddr s2 = muslErrnoAddr s4 := by
    unfold muslErrnoAddr; rw [(hnv23.trans hnv34).2.2.1]
  refine hb_seq_nonVm (mid := ret_pc) hext hsvc ?_
  refine step_hb_make_handler_post (Or.inr rfl) hmh_body' hsas' hret
    (F := memMapped altBase (4096 + hbExpectedAltRawSz entries) ∗ F)
    (fun R hm => by
      simp only [wp_norm, arm64_norm, hsp3_eq, htp24] at hm ⊢
      revert hm; sep_entail)
    hpc4 hrun4 hsp4_eq hsp_align hsp_al4 hsp_lo hx0_4 hx19_4 hx20_4 hx21_4 hreq_lo hsas4
    fun sf hpc_f hrun_f hsp_f hsp_al_f hx0_f hx19_f hx20_f hx21_f hx29_f hcs_f hnv_f => ?_
  refine hb_done_nonVm hpc_f hrun_f fun hvm_post => ?_
  refine hb_step_entail (hnext sf altBase errno1 hbase4k hbaseAl hbaseFit hbaseMap
    hpc_f hrun_f hsp_f hsp_al_f ?_ hx0_f ((hnv04.setSigAltStack _).trans hnv_f)
    (by rw [hvm_post.physMemAvail_eq]; simpa [wp_norm, arm64_norm, hphys3, hvm2.physMemAvail_eq] using hphys4)
    (by rw [hvm_post.brk_eq]; simpa [wp_norm, arm64_norm, hbrk3, hvm2.brk_eq] using hbrk4)
    (by rw [hvm_post.brkStart_eq]; simpa [wp_norm, arm64_norm, hbrkS3, hvm2.brkStart_eq] using hbrkS4)
    fun a => ?_)
    (fun R hm => by revert hm; sep_entail)
  · rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs2 with ⟨_, _, _, g22_2, g23_2, g24_2, g25_2, g26_2, g27_2, g28_2, _, gv_2⟩
    rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs3 with ⟨_, _, _, g22_3, g23_3, g24_3, g25_3, g26_3, g27_3, g28_3, _, gv_3⟩
    rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs4 with ⟨_, _, _, g22_4, g23_4, g24_4, g25_4, g26_4, g27_4, g28_4, _, gv_4⟩
    rcases (CalleeSavedPreserved.iff_regs _ _).mp hcs_f with ⟨_, _, _, g22_5, g23_5, g24_5, g25_5, g26_5, g27_5, g28_5, _, gv_5⟩
    simp only [wp_norm, arm64_norm] at g22_2 g23_2 g24_2 g25_2 g26_2 g27_2 g28_2 gv_2 g22_3 g23_3 g24_3 g25_3 g26_3 g27_3 g28_3 gv_3 g22_4 g23_4 g24_4 g25_4 g26_4 g27_4 g28_4 gv_4 g22_5 g23_5 g24_5 g25_5 g26_5 g27_5 g28_5 gv_5
    rw [CalleeSavedPreserved.iff_regs]
    exact ⟨hx19_f, hx20_f, hx21_f,
      g22_5.trans (g22_4.trans (g22_3.trans g22_2)),
      g23_5.trans (g23_4.trans (g23_3.trans g23_2)),
      g24_5.trans (g24_4.trans (g24_3.trans g24_2)),
      g25_5.trans (g25_4.trans (g25_3.trans g25_2)),
      g26_5.trans (g26_4.trans (g26_3.trans g26_2)),
      g27_5.trans (g27_4.trans (g27_3.trans g27_2)),
      g28_5.trans (g28_4.trans (g28_3.trans g28_2)),
      hx29_f,
      gv_5.trans (gv_4.trans (gv_3.trans gv_2))⟩
  · rw [hvm_post.perm_eq a, hperm4 a]
    simp only [wp_norm, arm64_norm, Memory.perm_setPermNonFrozen, hperm3, Memory.perm_mapZero, hvm2.perm_eq, mapSz]

end

end CaseStudies.Hashbrown.Proofs.StdCli
