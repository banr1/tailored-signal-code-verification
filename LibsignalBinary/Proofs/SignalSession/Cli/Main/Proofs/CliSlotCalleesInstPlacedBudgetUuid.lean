/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.Placed.GenLsBlock
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.InImage.UuidTryParse.ParserTryParse
import ProofLib.Placed.OpcodeExclusion
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `<uuid::Uuid>::try_parse`

Relocatable `VmPreserved` and `.keepsFs` contracts for `decode_hex_32` (Block `254`),
`Parser::try_parse` (Block `255`), and `<uuid::Uuid>::try_parse` (Block `252`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetUuid

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  blkPC_252 blkPl_252 blkPC_254 blkPl_254 blkPC_255 blkPl_255
  libsignalSessionLib ls_subroutine_ok_cl_of_block ls_subroutine_ok_cl_of_plain
  lsmpl sepWP_seq_lscl withLsCl withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  decodeHex32 parseHyphenated parseSimple uuidTryParse
)
open CryptoVerification.LibsignalTripleRatchet (
  uuidErrParseOther uuidResultAt uuidTryParseCodeSpec uuidTryParseSpec
)
open CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse (
  ParserRegsPreserved braced_all_eq braced_ne_0 braced_ne_37
  decodeHex32ResultAt_sp52_none decodeHex32ResultAt_sp52_some
  decodeHex32ResultAt_sp88_none decodeHex32ResultAt_sp88_some decodeHex32Spec
  eq_ofNat_of_toNat_eq exists_36_parts exists_38_parts exists_45_parts
  len_eq_of_reg_eq len_ne_of_reg_ne
  memRegion_out17_split memRegion_out28_split memRegion_out32_split
  memRegion_sp52_17_none memRegion_sp52_17_some memRegion_sp56_17_split
  memRegion_sp88_17_none memRegion_sp88_17_some
  memRegion_sp88_32_for_hyphen memRegion_sp88_32_for_simple
  parseHyphenated_all_eq parseHyphenated_ne_13 parseHyphenated_ne_18
  parseHyphenated_ne_23 parseHyphenated_ne_8 parseHyphenated_of_parts
  parserTryParseResultAt parserTryParseResultAt_some_eq
  parserTryParseResultAt_sp56_none parserTryParseResultAt_sp56_some
  parserTryParseSpec sepWP_parser_branch sepWP_parser_hyph36
  stackAt_parser_split stackAt_uuid_split subroutine_ok_of_sepWP_simple
  urn_all_eq uuidResultAt_some_eq uuidTryParse_of_other_len
)
open CryptoVerification.SignalSession.Cli.MainHops.UuidFs (decodeHex32_placed_okFs)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (
  sepWP_rebase_vmPreserved trapHooks vmPreserved_advancePC vmPreserved_applyWriteback
  vmPreserved_appendTrace vmPreserved_refl_iff vmPreserved_setFs
  vmPreserved_setMem_write16 vmPreserved_setMem_write32 vmPreserved_setMem_write64
  vmPreserved_setMem_write8 vmPreserved_setMem_writeBytes vmPreserved_setPC
  vmPreserved_setPState vmPreserved_setStatus vmPreserved_stepExclLoop
  vmPreserved_writeReg vmPreserved_writeReg32 vmPreserved_writeReg64
  vmPreserved_writeVReg128 vmPreserved_writeVReg32 vmPreserved_writeVReg64
  tpidrEl0_applyWriteback
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem fs_writeReg_placed (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by cases s; cases w <;> cases r <;> rfl

private theorem sepWP_vm_step {P : Program} {b mid target : BitVec 64}
    {Hk : String → Option (State → State)} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hwp : SepWP (P.rebase b Hk) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → SepWP (P.rebase b Hk) target sm Pm post))) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq hwp fun _ _ _ _ ⟨hvm, hk⟩ => hk hvm

private theorem sepWP_lscl_vm_step [LibsignalPlacement] {P : Program} {b mid target : BitVec 64}
    {Hk : String → Option (State → State)} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hwp : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧
      (LibsignalCodeLoaded lsmpl sm.mem → VmPreserved s sm → SepWP (P.rebase b Hk) target sm Pm post))) :
    SepWP (P.rebase b Hk) target s Pre post :=
  sepWP_seq_lscl hcl (mid := mid) (SepWP.mono hwp fun _ _ _ _ ⟨hvm, hk⟩ hcl' => hk hcl' hvm)

private def vmCore (s : State) := (s.brkStart, s.brk, s.tpidrEl0, s.physMemAvail, s.fs, s.mem.perm)
private theorem vmCore_setPC (s : State) (p : BitVec 64) : vmCore (s.setPC p) = vmCore s := by cases s; rfl
private theorem vmCore_advancePC (s : State) : vmCore s.advancePC = vmCore s := by cases s; rfl
private theorem vmCore_setPState (s : State) (p : PState) : vmCore (s.setPState p) = vmCore s := by cases s; rfl
private theorem vmCore_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    vmCore (s.writeReg64 r v) = vmCore s := by cases s; cases r <;> rfl
private theorem vmCore_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    vmCore (s.writeReg32 r v) = vmCore s := by cases s; cases r <;> rfl
private theorem vmCore_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    vmCore (s.writeReg w r v) = vmCore s := by cases s; cases w <;> cases r <;> rfl
private theorem vmCore_setMem (s : State) (m : Memory) :
    vmCore (s.setMem m) =
      ((vmCore s).1, (vmCore s).2.1, (vmCore s).2.2.1, (vmCore s).2.2.2.1, (vmCore s).2.2.2.2.1, m.perm) := by
  cases s; rfl
private theorem vm_of_core {s1 s2 : State} (h : vmCore s1 = vmCore s2) : VmPreserved s1 s2 :=
  ⟨⟨(congrArg Prod.fst h).symm, (congrArg (fun x => x.2.1) h).symm, (congrArg (fun x => x.2.2.1) h).symm⟩,
    (congrArg (fun x => x.2.2.2.1) h).symm,
    fun a => congrFun (congrArg (fun x => x.2.2.2.2.2) h).symm a,
    LibsignalBinary.Heap.FdsHiFrame.of_fs_eq (congrArg (fun x => x.2.2.2.2.1) h).symm⟩

local macro "vm_core_step" : tactic =>
  `(tactic| exact vm_of_core (by simp only [vmCore_setPC, vmCore_advancePC, vmCore_setPState,
    vmCore_writeReg64, vmCore_writeReg32, vmCore_writeReg, vmCore_setMem]))

attribute [local irreducible] VmPreserved

private theorem vm_chain {s0 s1 s2 : State} (h01 : VmPreserved s0 s1) (h12 : VmPreserved s1 s2) :
    VmPreserved s0 s2 := h01.trans h12

private theorem strip_codeLoaded_of_keep_local {P : Program} {m : Memory} (hL : P.CodeLoaded m) :
    P.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep P) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : P.base + BitVec.ofNat 64 i - P.base = BitVec.ofNat 64 i := by bv_omega
  have hkeep : ProofLib.progKeep P (P.base + BitVec.ofNat 64 i) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hi
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem strip_execOnlyIn_of_keep_local (P : Program) (m : Memory) :
    P.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep P) m) :=
  fun _ hx => of_decide_eq_true (ProofLib.strip_perm_x_imp hx).2

private theorem findSome?_override_none_local : ∀ (l : List (String × Nat)) (off : Nat),
    (l.findSome? fun (_, o) => if o == off then (none : Option (State → State)) else none) = none
  | [], _ => rfl
  | (_, _) :: tl, off => by
    dsimp only [List.findSome?]; rw [ite_self]; exact findSome?_override_none_local tl off

private theorem findSome?_trapHooks_some_local :
    ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
      (l.findSome? fun (n, o) => if o == off then trapHooks n else none) = some f →
      f = fun s => s.setStatus (.Exception "extern")
  | [], _, _, h => by simp at h
  | (n, o) :: tl, off, f, h => by
    simp only [List.findSome?_cons, trapHooks] at h
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte, Option.some.injEq] at h; exact h.symm
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
      exact findSome?_trapHooks_some_local tl h

private theorem findSome?_stubs_eq_none_local (Hk : String → Option (State → State)) :
    ∀ (l : List (String × Nat)) {off : Nat},
      (l.findSome? fun (n, o) => if o == off then trapHooks n else none) = none →
      (l.findSome? fun (n, o) => if o == off then Hk n else none) = none
  | [], _, _ => rfl
  | (n, o) :: tl, off, h => by
    simp only [List.findSome?_cons, trapHooks] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h; cases h
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact findSome?_stubs_eq_none_local Hk tl h

private theorem externAt?_rebase_trapHooks_some_local {P : Program} {b pc : BitVec 64} {f : State → State}
    (h : (P.rebase b trapHooks).externAt? pc = some f) :
    f = fun s => s.setStatus (.Exception "extern") := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at h; dsimp only at h
  rw [findSome?_override_none_local] at h
  cases hm : (P.stubs.findSome? fun (n, o) => if o == (pc - b).toNat then trapHooks n else none) with
  | none => rw [hm] at h; cases h
  | some g =>
    rw [hm] at h; injection h with hgf; subst hgf
    exact findSome?_trapHooks_some_local P.stubs hm

private theorem externAt?_rebase_eq_none_of_trapHooks_local {P : Program} {b pc : BitVec 64}
    {Hk : String → Option (State → State)} (h : (P.rebase b trapHooks).externAt? pc = none) :
    (P.rebase b Hk).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at h ⊢; dsimp only at h ⊢
  rw [findSome?_override_none_local] at h ⊢
  have h1 : (P.stubs.findSome? fun (n, o) => if o == (pc - b).toNat then trapHooks n else none) = none := by
    cases hm : (P.stubs.findSome? fun (n, o) => if o == (pc - b).toNat then trapHooks n else none) with
    | none => rfl
    | some _ => rw [hm] at h; cases h
  rw [findSome?_stubs_eq_none_local Hk P.stubs h1]; rfl

private theorem steps_start_running_local {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem steps_blk254_lift_strip [LibsignalPlacement] (H : LibsignalHooks)
    (hall_svc : ((blkPC_254).rebase (blkPl_254).base trapHooks).allInstrs (fun ins => !ins.isSvc0) = true)
    (hall_msr : ((blkPC_254).rebase (blkPl_254).base trapHooks).allInstrs (fun ins => !ins.isMsrTpidrEl0) = true)
    {s1' sf' : State} (hsteps : Steps ((blkPC_254).rebase (blkPl_254).base trapHooks) s1' sf')
    (hrun_f : sf'.status = .Running) :
    let Q := (blkPC_254).rebase (blkPl_254).base trapHooks
    let P := (blkPC_254).rebase (blkPl_254).base H
    ∀ (s1 : State), s1' = ProofLib.stripS (ProofLib.progKeep Q) s1 → Q.CodeLoaded s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (ProofLib.progKeep Q) sf ∧
        Steps P s1 sf ∧ ProofLib.NonSyscallPreserved s1 sf ∧ sf.tpidrEl0 = s1.tpidrEl0 := by
  intro Q P
  induction hsteps with
  | refl => exact fun s1 hs1 _ => ⟨s1, hs1, .refl s1, ProofLib.NonSyscallPreserved.refl s1, rfl⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1; have hrb' : sb'.status = .Running := steps_start_running_local hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ =>
      rw [externAt?_rebase_trapHooks_some_local he] at hrb'
      cases s1; cases hrb'
    | extern_fault _ _ _ => cases s1; cases hrb'
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := (by cases s1; exact hr1')
      have hL1' := strip_codeLoaded_of_keep_local hL1
      have hexec' := strip_execOnlyIn_of_keep_local Q s1.mem
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall_svc hL1' hexec' _ inst hfe'
      have hnmsr : inst.isMsrTpidrEl0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall_msr hL1' hexec' _ inst hfe'
      have hpc_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).pc = s1.pc := (by cases s1; rfl)
      have hmem_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).mem =
          ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem := (by cases s1; rfl)
      have hext_trap : Q.externAt? s1.pc = none := by
        rw [hpc_eq] at hfe'
        cases he : Q.externAt? s1.pc with
        | none => rfl
        | some _ => unfold Program.fetchMem at hfe'; rw [he] at hfe'; cases hfe'
      have hext_P : P.externAt? s1.pc = none :=
        externAt?_rebase_eq_none_of_trapHooks_local (Hk := H) hext_trap
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        rw [hpc_eq, hmem_eq] at hfe'; unfold Program.fetchMem at hfe' ⊢
        rw [hext_trap] at hfe'; rw [hext_P]
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe' ⊢
        by_cases hal_pc : s1.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe' ⊢
          split at hfe'
          · contradiction
          · rename_i hce'
            have hce : s1.mem.canExec s1.pc 4 = true := by
              simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
              unfold Memory.canExec at hce' ⊢; rw [Memory.allPerm_iff] at hce' ⊢
              intro k hk; have hxk := hce' k hk
              rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
            have hr32 : (ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem).read32 s1.pc =
                s1.mem.read32 s1.pc := by simp [Memory.read32, ProofLib.strip_read8]
            rw [hr32] at hfe'; simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact hfe'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'; contradiction
      have hev_Q : Q.evalInst inst (ProofLib.stripS (ProofLib.progKeep Q) s1) =
          ProofLib.stripS (ProofLib.progKeep Q) (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      have htp_1 : (execInst inst s1).tpidrEl0 = s1.tpidrEl0 := by
        refine Step.tpidrEl0_of_noMsrTpidrEl0 (prog := P) ?_ ?_ hstep_P
        · intro i hfi; rw [hfe_P] at hfi; injection hfi with h_eq; subst h_eq; exact hnmsr
        · intro _ hfk; rw [hext_P] at hfk; cases hfk
      obtain ⟨sf, hsf_eq, hsteps_P, hnsp_rest, htp_rest⟩ :=
        ih hrun_f (execInst inst s1) hev_Q (hstep_P.codeLoaded hL1)
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P,
        ProofLib.NonSyscallPreserved.trans
          (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1) hnsp_rest,
        htp_rest.trans htp_1⟩

theorem decodeHex32_placed_vm_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_254).rebase (blkPl_254).base H)
      (blkPl_254).base
      (withVmPreserved decodeHex32Spec.keepsFs) := by
  apply subroutine_ok_intro
  intro x R s0 hpc hrun hpre hal hL
  let Q := (blkPC_254).rebase (blkPl_254).base trapHooks
  have hQ_eq : Q = libsignalSessionLib.blockProgram lsmpl 254 trapHooks :=
    (inferInstance : IsLsBlockProg Q 254 trapHooks).eq_blockProgram
  have hall_svc : Q.allInstrs (fun ins => !ins.isSvc0) = true := by
    rw [hQ_eq]
    exact PlacedLib.program_noSvc0_of_patchSafe
      (lib := libsignalSessionLib.blockLib 254) (by rfl) blkPl_254 trapHooks
  have hall_msr : Q.allInstrs (fun ins => !ins.isMsrTpidrEl0) = true := by
    rw [hQ_eq]
    exact PlacedLib.program_noMsrTpidrEl0_of_patchSafe
      (lib := libsignalSessionLib.blockLib 254) (by rfl) blkPl_254 trapHooks
  let keep := ProofLib.progKeep Q
  have hL_Q : Q.CodeLoaded s0.mem := hL.of_base_code rfl rfl
  have hL_strip : Q.CodeLoaded (ProofLib.stripExecOutside keep s0.mem) :=
    strip_codeLoaded_of_keep_local hL_Q
  dsimp only [withVmPreserved] at hpre
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hpre
  have hpc_s : (ProofLib.stripS keep s0).pc = (blkPl_254).base := by cases s0; exact hpc
  have hrun_s : (ProofLib.stripS keep s0).status = .Running := by cases s0; exact hrun
  have hal_s : (ProofLib.stripS keep s0).spAligned = true := by cases s0; exact hal
  have hm_s : (ProofLib.stripS keep s0).mem ⊨ decodeHex32Spec.keepsFs.pre x (ProofLib.stripS keep s0) ∗ R_view := by
    cases s0; exact hm_strip
  obtain ⟨sf', hstepsQ, ⟨hpc_f', hrun_f', hpost', hcc'⟩ | ⟨_, hoom'⟩⟩ :=
    subroutine_ok_apply_full (oom := fun _ => False) (decodeHex32_placed_okFs trapHooks)
      x R_view hpc_s hrun_s hm_s hal_s
      (by intro _ _ hp; dsimp only [Spec.keepsFs, decodeHex32Spec] at hp; exact not_satisfies_false_sepConj hp)
      (by intro _ _ _ he; dsimp only [Spec.keepsFs, decodeHex32Spec] at he; exact not_satisfies_false_sepConj he)
      (by intro _ _ ho; dsimp only [Spec.keepsFs, decodeHex32Spec] at ho; exact not_satisfies_false_sepConj ho)
      hL_strip
  · obtain ⟨sf, hsf_eq, hstepsP, hnsp, htp⟩ :=
      steps_blk254_lift_strip H hall_svc hall_msr hstepsQ hrun_f' s0 rfl hL_Q
    have hvm : VmPreserved s0 sf := hnsp.toVmPreserved htp
    have hperm_eq : ∀ a, sf.mem.perm a = s0.mem.perm a := fun a => congrFun hnsp.2.1 a
    have hpost_mem' : ProofLib.stripExecOutside keep sf.mem ⊨
        decodeHex32Spec.keepsFs.post x s0 sf ∗ R_view := by
      rw [hsf_eq] at hpost'; cases s0; cases sf; exact hpost'
    have hpost_mem : sf.mem ⊨ decodeHex32Spec.keepsFs.post x s0 sf ∗ R :=
      hunstrip hperm_eq hpost_mem'
    have hpc_f : sf.pc = s0.readReg64 .x30 := by rw [hsf_eq] at hpc_f'; cases s0; cases sf; exact hpc_f'
    have hsp_f : sf.sp = s0.sp := by have hsp_f' := hcc'.1; rw [hsf_eq] at hsp_f'; cases s0; cases sf; exact hsp_f'
    have hrun_f : sf.status = .Running := by rw [hsf_eq] at hrun_f'; cases sf; exact hrun_f'
    have hcs_f : CalleeSavedPreserved s0 sf := by
      have hcs' := hcc'.2; rw [hsf_eq] at hcs'; cases s0; cases sf; exact hcs'
    refine ⟨sf, hstepsP, Or.inl ⟨hpc_f, hrun_f, ?_, ⟨hsp_f, hcs_f⟩⟩⟩
    dsimp only [withVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm, hpost_mem⟩
  · exact False.elim hoom'

private abbrev parserPostVm (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64)
    (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R →
      sf.mem ⊨ (withVmPreserved parserTryParseSpec.keepsFs).post (p, bs, out17) s0 sf ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private abbrev parserFrameSep (sliceP : SepProp) (out17 : BitVec 64)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 : State) : SepProp :=
  ((sliceP ∗ (out17 ↦₆₄ out_w0) ∗ ((out17 + 8#64) ↦₆₄ out_w1) ∗ ((out17 + 16#64) ↦₈ out_b2)) ∗
   (stackAt (s0.sp - 96#64) 0x20 ∗ memRegion (s0.sp - 96#64) 8 ∗ memRegion (s0.sp - 88#64) 32 ∗
    memRegion (s0.sp - 56#64) 4 ∗ memRegion (s0.sp - 52#64) 17 ∗ memRegion (s0.sp - 35#64) 3 ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))

private theorem wp_err_vm_placed [LibsignalPlacement] (hooks : LibsignalHooks)
    (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 s : State)
    (hsp_align : s0.spAligned = true) (huuid : uuidTryParse bs = none)
    (hpc : s.pc = (blkPl_255).base + bv% (420)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hx8 : s.readReg64 .x8 = out17)
    (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hvm0 : VmPreserved s0 s) (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s
      (parserFrameSep (p ↦ₛ bs) out17 out_w0 out_w1 out_b2 s0)
      (parserPostVm p bs out17 s0 R) := by
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  dsimp only [parserFrameSep]
  apply sepWP_vm_step (mid := s0.readReg64 .x30)
  by_vm_steps
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm1 => ?_⟩
    have hvm_tot := vm_chain hvm0 hvm1
    unfold parserPostVm withVmPreserved Spec.keepsFs parserTryParseSpec
    simp only [huuid, parserTryParseResultAt, stackAt_parser_split s0.sp]
    wp_done

private theorem wp_simple_vm_placed [LibsignalPlacement] (hooks : LibsignalHooks)
    (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 s : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s.mem) (hsp_align : s0.spAligned = true)
    (hlen : bs.length = 32) (hpc : s.pc = (blkPl_255).base + bv% (328))
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = p) (hx8 : s.readReg64 .x8 = out17)
    (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hvm0 : VmPreserved s0 s) (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s
      (parserFrameSep (p ↦ₛ bs) out17 out_w0 out_w1 out_b2 s0)
      (parserPostVm p bs out17 s0 R) := by
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  have hcallee_hex := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_255).rebase (blkPl_255).base hooks) (decodeHex32_placed_vm_ok hooks)
  change subroutine_ok _ (lsmpl.base 254) _ at hcallee_hex
  simp only [withLsCl, withVmPreserved, Spec.keepsFs, decodeHex32Spec, sepConj_assoc] at hcallee_hex
  have huuid : uuidTryParse bs = decodeHex32 bs := by unfold uuidTryParse parseSimple; simp [hlen]
  dsimp only [parserFrameSep]
  rw [memRegion_sp88_32_for_simple s0.sp]
  apply sepWP_lscl_vm_step hcl0 (mid := lsmpl.base 254)
  by_vm_steps
    wp_steps
    refine SepWP.done (by rfl) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun _hcl_call hvm1 => ?_⟩
    have hvm01 := vm_chain hvm0 hvm1
    wp_apply
    have hvm_hex := vm_chain hvm01 ‹_›
    cases hdec : decodeHex32 bs with
    | none =>
      rw [decodeHex32ResultAt_sp88_none s0.sp, hsp]
      apply sepWP_vm_step (mid := s0.readReg64 .x30)
      by_vm_steps
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm2 => ?_⟩
        have hvm_tot := vm_chain hvm_hex hvm2
        unfold parserPostVm withVmPreserved Spec.keepsFs parserTryParseSpec
        simp only [huuid, hdec, parserTryParseResultAt, stackAt_parser_split s0.sp,
          memRegion_sp88_32_for_simple s0.sp, memRegion_sp88_17_none s0.sp]
        wp_done
    | some u =>
      rw [decodeHex32ResultAt_sp88_some s0.sp u, hsp]
      apply sepWP_vm_step (mid := s0.readReg64 .x30)
      by_vm_steps
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm2 => ?_⟩
        have hvm_tot := vm_chain hvm_hex hvm2
        unfold parserPostVm withVmPreserved Spec.keepsFs parserTryParseSpec
        simp only [huuid, hdec, parserTryParseResultAt_some_eq, stackAt_parser_split s0.sp,
          memRegion_sp88_32_for_simple s0.sp, memRegion_sp88_17_some s0.sp]
        wp_done

set_option maxHeartbeats 800000 in
private theorem wp_hyphenated_vm_placed [LibsignalPlacement] (hooks : LibsignalHooks)
    (p p19 : BitVec 64) (bs s36 : List (BitVec 8)) (Frame : SepProp) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 s : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s.mem) (hsp_align : s0.spAligned = true)
    (hs36 : s36.length = 36) (hframe : (p ↦ₛ bs) = ((p19 ↦ₛ s36) ∗ Frame))
    (huuid : uuidTryParse bs = parseHyphenated s36)
    (hpc : s.pc = (blkPl_255).base + bv% (44)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = p19)
    (hx8 : s.readReg64 .x8 = out17) (hx29 : s.readReg64 .x29 = s0.sp - 32#64)
    (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hvm0 : VmPreserved s0 s) (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s
      (parserFrameSep ((p19 ↦ₛ s36) ∗ Frame) out17 out_w0 out_w1 out_b2 s0)
      (parserPostVm p bs out17 s0 R) := by
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  have hcallee_hex := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_255).rebase (blkPl_255).base hooks) (decodeHex32_placed_vm_ok hooks)
  change subroutine_ok _ (lsmpl.base 254) _ at hcallee_hex
  simp only [withLsCl, withVmPreserved, Spec.keepsFs, decodeHex32Spec, sepConj_assoc] at hcallee_hex
  rcases exists_36_parts s36 hs36 with
    ⟨hex32, b8, b13, b18, b23, w0, w4, w1, w2, w3, w5,
     hhex_len, hb8, hb13, hb18, hb23, hhex_eq, hp19_split, hsp_hex32⟩
  have hph := parseHyphenated_of_parts s36 hex32 b8 b13 b18 b23 hs36 hb8 hb13 hb18 hb23 hhex_eq
  dsimp only [parserFrameSep]
  rw [hp19_split p19, memRegion_sp88_32_for_hyphen s0.sp]
  wp_pull_exists
  wp_steps
  wp_if h8
  · apply sepWP_vm_step (mid := s0.readReg64 .x30)
    by_vm_steps
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm1 => ?_⟩
      have hvm_tot := vm_chain (vm_chain hvm0 (by simp only [arm64_norm])) hvm1
      unfold parserPostVm withVmPreserved Spec.keepsFs parserTryParseSpec
      simp only [hframe, hp19_split p19, huuid, parseHyphenated_ne_8 hph h8, parserTryParseResultAt,
        stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]
      wp_done
  · wp_steps; wp_if h13
    · apply sepWP_vm_step (mid := s0.readReg64 .x30)
      by_vm_steps
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm1 => ?_⟩
        have hvm_tot := vm_chain (vm_chain hvm0 (by simp only [arm64_norm])) hvm1
        unfold parserPostVm withVmPreserved Spec.keepsFs parserTryParseSpec
        simp only [hframe, hp19_split p19, huuid, parseHyphenated_ne_13 hph h13, parserTryParseResultAt,
          stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]
        wp_done
    · wp_steps; wp_if h18
      · apply sepWP_vm_step (mid := s0.readReg64 .x30)
        by_vm_steps
          wp_steps
          refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm1 => ?_⟩
          have hvm_tot := vm_chain (vm_chain hvm0 (by simp only [arm64_norm])) hvm1
          unfold parserPostVm withVmPreserved Spec.keepsFs parserTryParseSpec
          simp only [hframe, hp19_split p19, huuid, parseHyphenated_ne_18 hph h18, parserTryParseResultAt,
            stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]
          wp_done
      · wp_steps; wp_if h23
        · apply sepWP_vm_step (mid := s0.readReg64 .x30)
          by_vm_steps
            wp_steps
            refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm1 => ?_⟩
            have hvm_tot := vm_chain (vm_chain hvm0 (by simp only [arm64_norm])) hvm1
            unfold parserPostVm withVmPreserved Spec.keepsFs parserTryParseSpec
            simp only [hframe, hp19_split p19, huuid, parseHyphenated_ne_23 hph h23, parserTryParseResultAt,
              stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]
            wp_done
        · have hall := parseHyphenated_all_eq hph h8 h13 h18 h23
          apply sepWP_lscl_vm_step (by convert hcl0 using 1; wp_norm_lhs) (mid := lsmpl.base 254)
          by_vm_steps
            wp_steps
            refine SepWP.done (by rfl) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun _hcl_call hvm1 => ?_⟩
            have hvm01 := vm_chain (vm_chain hvm0 (by simp only [arm64_norm])) hvm1
            apply SepWP.focus_rw (hsp_hex32 s0.sp)
            wp_apply
            have hvm_hex := vm_chain hvm01 ‹_›
            cases hdec : decodeHex32 hex32 with
            | none =>
              rw [decodeHex32ResultAt_sp52_none s0.sp, ← hsp_hex32 s0.sp, hsp]
              apply sepWP_vm_step (mid := s0.readReg64 .x30)
              by_vm_steps
                wp_steps
                refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm2 => ?_⟩
                have hvm_tot := vm_chain hvm_hex hvm2
                unfold parserPostVm withVmPreserved Spec.keepsFs parserTryParseSpec
                simp only [hframe, hp19_split p19, huuid, hall, hdec, parserTryParseResultAt,
                  stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp, memRegion_sp52_17_none s0.sp]
                wp_done
            | some u =>
              rw [decodeHex32ResultAt_sp52_some s0.sp u, ← hsp_hex32 s0.sp, hsp]
              apply sepWP_vm_step (mid := s0.readReg64 .x30)
              by_vm_steps
                wp_steps
                refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm2 => ?_⟩
                have hvm_tot := vm_chain hvm_hex hvm2
                unfold parserPostVm withVmPreserved Spec.keepsFs parserTryParseSpec
                simp only [hframe, hp19_split p19, huuid, hall, hdec, parserTryParseResultAt_some_eq,
                  stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp, memRegion_sp52_17_some s0.sp]
                wp_done

set_option maxHeartbeats 800000 in
private theorem wp_braced_vm_placed [LibsignalPlacement] (hooks : LibsignalHooks)
    (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 s : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s.mem) (hsp_align : s0.spAligned = true)
    (hlen : bs.length = 38) (hpc : s.pc = (blkPl_255).base + bv% (388))
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = p) (hx8 : s.readReg64 .x8 = out17)
    (hx29 : s.readReg64 .x29 = s0.sp - 32#64) (htr : s.trace = s0.trace)
    (hfs : s.fs = s0.fs) (hvm0 : VmPreserved s0 s) (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s
      (parserFrameSep (p ↦ₛ bs) out17 out_w0 out_w1 out_b2 s0)
      (parserPostVm p bs out17 s0 R) := by
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  have h_hyph := wp_hyphenated_vm_placed hooks
  have h_err := wp_err_vm_placed hooks
  rcases exists_38_parts bs hlen with ⟨b0, b37, s36, hs36, _, huuid, hp_split⟩
  dsimp only [parserFrameSep]
  rw [hp_split p]; wp_steps; wp_if hb0
  · rw [← hp_split p]
    refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align (braced_ne_0 huuid hb0)
      ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm]))
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
  · wp_steps; wp_if hb37
    · rw [← hp_split p]
      refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align (braced_ne_37 huuid hb37)
        ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm]))
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
    · wp_step; wp_step
      refine h_hyph p (p + 1#64) bs s36 ((p ↦₈ b0) ∗ ((p + 37#64) ↦₈ b37))
        out17 R out_w0 out_w1 out_b2 s0 _ (by convert hcl0 using 1; wp_norm_lhs)
        hsp_align hs36 (hp_split p) (braced_all_eq huuid hb0 hb37)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm]))
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs

set_option maxHeartbeats 800000 in
private theorem wp_urn_vm_placed [LibsignalPlacement] (hooks : LibsignalHooks)
    (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 s : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s.mem) (hsp_align : s0.spAligned = true)
    (hlen : bs.length = 45) (hpc : s.pc = (blkPl_255).base + bv% (212))
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = p) (hx8 : s.readReg64 .x8 = out17)
    (hx29 : s.readReg64 .x29 = s0.sp - 32#64) (htr : s.trace = s0.trace)
    (hfs : s.fs = s0.fs) (hvm0 : VmPreserved s0 s) (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s
      (parserFrameSep (p ↦ₛ bs) out17 out_w0 out_w1 out_b2 s0)
      (parserPostVm p bs out17 s0 R) := by
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  have h_hyph := wp_hyphenated_vm_placed hooks
  have h_err := wp_err_vm_placed hooks
  rcases exists_45_parts bs hlen with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, s36, hs36, huuid, hp_split⟩
  dsimp only [parserFrameSep]
  rw [hp_split p]; wp_steps; wp_if hb0
  · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x75#8 ≠ b0 from fun h => hb0 (h ▸ rfl)]
    rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
      ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
  · wp_steps; wp_if hb1
    · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x72#8 ≠ b1 from fun h => hb1 (h ▸ rfl)]
      rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
        ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
    · wp_steps; wp_if hb2
      · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x6e#8 ≠ b2 from fun h => hb2 (h ▸ rfl)]
        rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
          ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
      · wp_steps; wp_if hb3
        · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x3a#8 ≠ b3 from fun h => hb3 (h ▸ rfl)]
          rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
            ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
        · wp_steps; wp_if hb4
          · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x75#8 ≠ b4 from fun h => hb4 (h ▸ rfl)]
            rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
              ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
          · wp_steps; wp_if hb5
            · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x75#8 ≠ b5 from fun h => hb5 (h ▸ rfl)]
              rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
                ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
            · wp_steps; wp_if hb6
              · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x69#8 ≠ b6 from fun h => hb6 (h ▸ rfl)]
                rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
                  ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
              · wp_steps; wp_if hb7
                · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x64#8 ≠ b7 from fun h => hb7 (h ▸ rfl)]
                  rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
                    ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
                · wp_steps; wp_if hb8
                  · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x3a#8 ≠ b8 from fun h => hb8 (h ▸ rfl)]
                    rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
                      ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
                  · wp_step; wp_step
                    refine h_hyph p (p + 9#64) bs s36
                      ((p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1) ∗ ((p + 2#64) ↦₈ b2) ∗
                       ((p + 3#64) ↦₈ b3) ∗ ((p + 4#64) ↦₈ b4) ∗ ((p + 5#64) ↦₈ b5) ∗
                       ((p + 6#64) ↦₈ b6) ∗ ((p + 7#64) ↦₈ b7) ∗ ((p + 8#64) ↦₈ b8))
                      out17 R out_w0 out_w1 out_b2 s0 _ (by convert hcl0 using 1; wp_norm_lhs)
                      hsp_align hs36 (hp_split p)
                      (urn_all_eq huuid hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8)
                      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm]))
                      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs

set_option maxHeartbeats 800000 in
theorem parserTryParse_placed_vm_ok [LibsignalPlacement] (hooks : LibsignalHooks) :
    subroutine_ok ((blkPC_255).rebase (blkPl_255).base hooks) (blkPl_255).base
      (withLsCodeLoaded lsmpl (withVmPreserved parserTryParseSpec.keepsFs)) := by
  apply subroutine_ok_of_sepWP_simple
  intro ⟨p, bs, out17⟩ R s0 hpc hrun hsp
  change SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s0
    (((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧ s0.readReg64 .x8 = out17⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out17 17) ∗ stackAt s0.sp 0x80) ∗
      ⌜LibsignalCodeLoaded lsmpl s0.mem⌝) (parserPostVm p bs out17 s0 R)
  rw [sepConj_comm]; apply SepWP.pure_elim; intro hcl0
  have h_braced := wp_braced_vm_placed hooks
  have h_urn := wp_urn_vm_placed hooks
  have h_simple := wp_simple_vm_placed hooks
  have h_hyph := wp_hyphenated_vm_placed hooks
  have h_err := wp_err_vm_placed hooks
  simp only [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hx0, hx1, hx8⟩
  rw [memRegion_out17_split out17, stackAt_parser_split s0.sp]; wp_pull_exists
  apply sepWP_lscl_vm_step hcl0 (mid := (blkPl_255).base + bv% (16))
  by_vm_steps
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hcl1 hvm1 => ?_⟩
    wp_steps; wp_if hgt
    · have hne32 : bs.length ≠ 32 := fun hlen => by
        rw [show s0.readReg64 .x1 = 32#64 by rw [eq_ofNat_of_toNat_eq hx1, hlen]] at hgt; revert hgt; decide
      have hne36 : bs.length ≠ 36 := fun hlen => by
        rw [show s0.readReg64 .x1 = 36#64 by rw [eq_ofNat_of_toNat_eq hx1, hlen]] at hgt; revert hgt; decide
      wp_steps; wp_if heq38
      · apply sepWP_parser_branch
        refine h_braced p bs out17 R _ _ _ s0 _ (by convert hcl1 using 1; wp_norm_lhs)
          hsp (len_eq_of_reg_eq hx1 heq38) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          first | exact vm_chain hvm1 (by vm_core_step) | wp_norm_lhs
      · have hne38 := len_ne_of_reg_ne hx1 heq38
        wp_steps; wp_if hne45_reg
        · have huuid := uuidTryParse_of_other_len hne32 hne36 hne38 (len_ne_of_reg_ne hx1 hne45_reg)
          apply sepWP_parser_branch
          refine h_err p bs out17 R _ _ _ s0 _ hsp huuid ?_ ?_ ?_ ?_ ?_ ?_ ?_
            ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            first | exact vm_chain hvm1 (by vm_core_step) | wp_norm_lhs
        · apply sepWP_parser_branch
          refine h_urn p bs out17 R _ _ _ s0 _ (by convert hcl1 using 1; wp_norm_lhs)
            hsp (len_eq_of_reg_eq hx1 hne45_reg) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            first | exact vm_chain hvm1 (by vm_core_step) | wp_norm_lhs
    · have hne38 : bs.length ≠ 38 := fun hlen => by
        rw [show s0.readReg64 .x1 = 38#64 by rw [eq_ofNat_of_toNat_eq hx1, hlen]] at hgt; revert hgt; decide
      have hne45 : bs.length ≠ 45 := fun hlen => by
        rw [show s0.readReg64 .x1 = 45#64 by rw [eq_ofNat_of_toNat_eq hx1, hlen]] at hgt; revert hgt; decide
      wp_steps; wp_if heq32
      · apply sepWP_parser_branch
        refine h_simple p bs out17 R _ _ _ s0 _ (by convert hcl1 using 1; wp_norm_lhs)
          hsp (len_eq_of_reg_eq hx1 heq32) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          first | exact vm_chain hvm1 (by vm_core_step) | wp_norm_lhs
      · have hne32 := len_ne_of_reg_ne hx1 heq32
        wp_steps; wp_if hne36_reg
        · have huuid := uuidTryParse_of_other_len hne32 (len_ne_of_reg_ne hx1 hne36_reg) hne38 hne45
          apply sepWP_parser_branch
          refine h_err p bs out17 R _ _ _ s0 _ hsp huuid ?_ ?_ ?_ ?_ ?_ ?_ ?_
            ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            first | exact vm_chain hvm1 (by vm_core_step) | wp_norm_lhs
        · have hlen36 := len_eq_of_reg_eq hx1 hne36_reg
          have huuid : uuidTryParse bs = parseHyphenated bs := by unfold uuidTryParse; simp [hlen36]
          apply sepWP_parser_hyph36
          refine h_hyph p p bs bs emp out17 R _ _ _ s0 _ (by convert hcl1 using 1; wp_norm_lhs)
            hsp hlen36 (sepConj_emp (p ↦ₛ bs)).symm huuid ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            first | exact vm_chain hvm1 (by vm_core_step) | wp_norm_lhs

theorem uuidTryParse_placed_vm_ok [LibsignalPlacement] (hooks : LibsignalHooks) :
    subroutine_ok ((blkPC_252).rebase (blkPl_252).base hooks) (blkPl_252).base
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse).keepsFs)) := by
  have hcallee := ls_subroutine_ok_cl_of_block
    (callerProg := (blkPC_252).rebase (blkPl_252).base hooks) (parserTryParse_placed_vm_ok hooks)
  change subroutine_ok _ (lsmpl.base 255) _ at hcallee
  simp only [withLsCl, withVmPreserved, Spec.keepsFs, parserTryParseSpec, sepConj_assoc] at hcallee
  apply subroutine_ok_of_sepWP_simple
  intro ⟨p, bs, out⟩ R s0 hpc hrun hsp
  dsimp only [withLsCodeLoaded, withVmPreserved, Spec.keepsFs, uuidTryParseCodeSpec,
    uuidTryParseSpec, BitVec.ofNat_eq_ofNat] at *
  rw [sepConj_comm]; apply SepWP.pure_elim; intro hcl0
  simp only [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hx0, hx1, hx8⟩
  rw [memRegion_out32_split out, stackAt_uuid_split s0.sp]; wp_pull_exists
  apply sepWP_lscl_vm_step hcl0 (mid := lsmpl.base 255)
  by_vm_steps
    wp_steps
    refine SepWP.done (by rfl) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun _hcl_call hvm1 => ?_⟩
    wp_apply
    have hvm_p := vm_chain hvm1 ‹_›
    cases huuid : uuidTryParse bs with
    | none =>
      rw [parserTryParseResultAt_sp56_none s0.sp]; wp_pull_exists; wp_focus_pure; intro _htag
      apply sepWP_vm_step (mid := s0.readReg64 .x30)
      by_vm_steps
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm2 => ?_⟩
        have hvm_tot := vm_chain hvm_p hvm2
        simp only [uuidResultAt, uuidErrParseOther, memRegion_out28_split out, memRegion_sp56_17_split s0.sp]
        wp_done
    | some u =>
      rw [parserTryParseResultAt_sp56_some s0.sp u]
      apply sepWP_vm_step (mid := s0.readReg64 .x30)
      by_vm_steps
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm2 => ?_⟩
        have hvm_tot := vm_chain hvm_p hvm2
        simp only [uuidResultAt_some_eq out u, memRegion_sp56_17_split s0.sp]
        wp_done

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetUuid
