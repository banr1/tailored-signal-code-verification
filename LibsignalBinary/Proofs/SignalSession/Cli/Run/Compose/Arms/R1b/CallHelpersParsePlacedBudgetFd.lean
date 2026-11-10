/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSomeBudget
public import ProofLib.Placed.OpcodeExclusion
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import ProofLib.SepLogic.WPp

/-!
# `FdsGe3Closed`-Threaded Parsing Callee `SepWPp` Wrappers for Arm `R1b`

Lifts `<PublicKey>::deserialize` (Block `201`) to preserve `VmPreserved` and `State.fs`, and provides
`Ok`-branch `fs`- and `FdsGe3Closed`-preserving `SepWPp` call wrappers on Block `579` for
`split_signed`, `split_id`, `<PublicKey>::deserialize`, and `kem::PublicKey::deserialize`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudgetFd

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement blkPC_201 blkPl_201 instIsLsBlockProg_201
   libsignalSessionLib lsLogFilterAddr lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (ls_subroutine_ok_rocl_of_block subroutine_ok_withLsCodeRoLoaded_of_plain withLsCodeRoLoaded
   withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (deserializeFullPlacedSpec deserializeFull_placed_ok deserializeResult33At)
open CryptoVerification.LibsignalTripleRatchetRepr (speAt speWord strRefAt utf8)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SignalSession.Cli
  (splitId splitIdResultAt splitOkTag splitSigned splitSignedResultAt)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers (vecU8_to_ownedBytes)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_590)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (InRunPlaced PanicK RunNeeds RunSem r1b_CodeOk r1b_StackBounds r1b_cells2_to_region16
   r1b_sepWPp_drop_left r1b_spAligned_of_fsp runFsp runPcPlaced runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs (kemDeserResAt kemPkDeserialize)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runFrame)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudgetFd
  (fs_eq_of_splitId_eq_some splitIdSpecPlacedOkFs)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudgetFd
  (fs_eq_of_splitSigned_eq_some splitSignedSpecPlacedOkFs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_placed r1b_files_eq_of_trace_eq_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
  (cliKemDeserializeSpec kemDeserializeEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (RunCalleesPlacedFd slotWithFdsGe3Closed)

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## `<PublicKey>::deserialize` (Block `201`) `VmPreserved` and `State.fs` Lift -/

def withVmAndFsPreserved {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    post := fun x s0 sf => ⌜VmPreserved s0 sf ∧ sf.fs = s0.fs⌝ ∗ spec.post x s0 sf }

private theorem blk201_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (libsignalSessionLib.blockLib 201).text = true := by
  rfl

private theorem blk201_patchSafe_msr :
    (libsignalSessionLib.blockLib 201).text.patchSafe Obj.msrTpidrEl0Pat = true := by rfl

private theorem option_or_isSome {α : Type} (o₁ o₂ : Option α) :
    (o₁.or o₂).isSome = (o₁.isSome || o₂.isSome) := by cases o₁ <;> rfl

private theorem findSome?_isSome_congr {α β γ : Type} (l : List α)
    (f : α → Option β) (g : α → Option γ) (h : ∀ x, (f x).isSome = (g x).isSome) :
    (l.findSome? f).isSome = (l.findSome? g).isSome := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.findSome?]
    cases hf : f x <;> cases hg : g x
    · exact ih
    · have hx := h x; rw [hf, hg] at hx; cases hx
    · have hx := h x; rw [hf, hg] at hx; cases hx
    · rfl

private theorem findSome?_ite_map_status {α : Type} (l : List (String × Nat)) (off : Nat)
    (tbl : String → Option α) {f : State → State}
    (h : (l.findSome? fun (n, o) =>
      if o == off then (tbl n).map (fun _ (s : State) => s.setStatus (.Exception "ext")) else none) =
      some f)
    (s : State) : (f s).status = .Exception "ext" := by
  induction l with
  | nil => simp [List.findSome?] at h
  | cons hd tl ih =>
    rcases hd with ⟨n, o⟩
    simp only [List.findSome?] at h
    cases ho : o == off
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h; exact ih h
    · simp only [ho, ↓reduceIte] at h
      cases htn : tbl n with
      | none => simp only [htn, Option.map] at h; exact ih h
      | some _ => simp only [htn, Option.map] at h; injection h with hf; subst hf; cases s; rfl

private theorem block201_hooksException_externAt?_isSome [LibsignalPlacement]
    (H : LibsignalHooks) (pc : BitVec 64) :
    (((libsignalSessionLib.blockProgram lsmpl 201 (hooksException H)).externAt? pc)).isSome =
      (((libsignalSessionLib.blockProgram lsmpl 201 H).externAt? pc)).isSome := by
  unfold Program.externAt? Program.hookAtOff? Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program
  dsimp only
  rw [option_or_isSome, option_or_isSome]
  rw [findSome?_isSome_congr _
    (fun x : String × Nat =>
      if (x.2 == (pc - (libsignalSessionLib.blockPlacement lsmpl 201).base).toNat) = true then
        hooksException H x.1 else none)
    (fun x : String × Nat =>
      if (x.2 == (pc - (libsignalSessionLib.blockPlacement lsmpl 201).base).toNat) = true then
        H x.1 else none)]
  intro x
  cases h : (x.2 == (pc - (libsignalSessionLib.blockPlacement lsmpl 201).base).toNat) <;>
    simp [hooksException]

private theorem block201_hooksException_not_running [LibsignalPlacement]
    {H : LibsignalHooks} {pc : BitVec 64} {f : State → State}
    (h : (libsignalSessionLib.blockProgram lsmpl 201 (hooksException H)).externAt? pc = some f)
    (s : State) : (f s).status ≠ .Running := by
  unfold Program.externAt? Program.hookAtOff? Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program at h
  dsimp only [hooksException] at h
  have hnone : ∀ (l : List (String × Nat)),
      (l.findSome? fun (_ : String × Nat) => (none : Option (State → State))) = none := by
    intro l; induction l with | nil => rfl | cons _ _ ih => exact ih
  simp only [ite_self, hnone, Option.or_none] at h
  rw [findSome?_ite_map_status _ _ _ h]
  decide

private theorem strip_codeLoaded_of_keep {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun k hk => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 k - prog.base = BitVec.ofNat 64 k := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 k) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hk
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq k hk, hL.perm_eq k hk, hL.isLazyFree_eq k hk⟩

private theorem strip_execOnlyIn_of_keep (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := fun _ hpx =>
  of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem steps_start_running {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem steps_block201_lift_vm_fs [LibsignalPlacement] (H : LibsignalHooks)
    (hall_svc : (libsignalSessionLib.blockProgram lsmpl 201 (hooksException H)).allInstrs
      (fun ins => !ins.isSvc0) = true)
    (hall_msr : (libsignalSessionLib.blockProgram lsmpl 201 (hooksException H)).allInstrs
      (fun ins => !ins.isMsrTpidrEl0) = true)
    {s1' sf' : State}
    (hsteps : Steps (libsignalSessionLib.blockProgram lsmpl 201 (hooksException H)) s1' sf')
    (hrun_f : sf'.status = .Running) :
    let Q := libsignalSessionLib.blockProgram lsmpl 201 (hooksException H)
    let P := libsignalSessionLib.blockProgram lsmpl 201 H
    ∀ (s1 : State), s1' = ProofLib.stripS (ProofLib.progKeep Q) s1 → Q.CodeLoaded s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (ProofLib.progKeep Q) sf ∧
        Steps P s1 sf ∧ VmPreserved s1 sf ∧ sf.fs = s1.fs := by
  intro Q P
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, hs1, .refl s1, VmPreserved.refl s1, rfl⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1
    have hrb' : sb'.status = .Running := steps_start_running hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ =>
      exact False.elim (block201_hooksException_not_running he _ hrb')
    | extern_fault _ _ _ => cases s1; cases hrb'
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := (by cases s1; exact hr1')
      have hL1' : Q.CodeLoaded (ProofLib.stripS (ProofLib.progKeep Q) s1).mem :=
        strip_codeLoaded_of_keep hL1
      have hexec' : Q.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep Q) s1).mem :=
        strip_execOnlyIn_of_keep Q s1.mem
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall_svc hL1' hexec' _ inst hfe'
      have hnmsr : inst.isMsrTpidrEl0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall_msr hL1' hexec' _ inst hfe'
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).pc = s1.pc := (by cases s1; rfl)
        have hmem_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).mem =
            ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem := (by cases s1; rfl)
        rw [hpc_eq, hmem_eq] at hfe'
        dsimp only [Q, P] at hfe' ⊢
        unfold Program.fetchMem at hfe' ⊢
        rw [block201_hooksException_externAt?_isSome H s1.pc] at hfe'
        cases heP : ((libsignalSessionLib.blockProgram lsmpl 201 H).externAt? s1.pc).isSome
        · simp only [heP, Bool.false_eq_true, ↓reduceIte] at hfe' ⊢
          by_cases hal_pc : s1.pc.toNat % 4 = 0
          · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe' ⊢
            split at hfe'
            · contradiction
            · rename_i hce'
              have hce : s1.mem.canExec s1.pc 4 = true := by
                simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
                unfold Memory.canExec at hce' ⊢
                rw [Memory.allPerm_iff] at hce' ⊢
                intro k hk
                have hxk := hce' k hk
                rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
              have hr32 : (ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem).read32 s1.pc =
                  s1.mem.read32 s1.pc := by
                simp [Memory.read32, ProofLib.strip_read8]
              rw [hr32] at hfe'
              simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              exact hfe'
          · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'
            contradiction
        · simp only [heP, ↓reduceIte] at hfe'
          contradiction
      have hev_Q : Q.evalInst inst (ProofLib.stripS (ProofLib.progKeep Q) s1) =
          ProofLib.stripS (ProofLib.progKeep Q) (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      have hLQ_next : Q.CodeLoaded (execInst inst s1).mem := hstep_P.codeLoaded hL1
      obtain ⟨sf, hsf_eq, hsteps_P, hvm_rest, hfs_rest⟩ :=
        ih hrun_f (execInst inst s1) hev_Q hLQ_next
      have hnsp1 := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1
      have hvm1 : VmPreserved s1 (execInst inst s1) :=
        hnsp1.toVmPreserved (execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1)
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P, hvm1.trans hvm_rest,
        hfs_rest.trans hnsp1.2.2.2.2.2.2⟩

private theorem deserializeFull_vm_fs_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base
      (withVmAndFsPreserved deserializeFullPlacedSpec) := by
  have hP_eq : (blkPC_201).rebase (blkPl_201).base H =
      libsignalSessionLib.blockProgram lsmpl 201 H :=
    IsLsBlockProg.eq_blockProgram
  have hQ_eq : (blkPC_201).rebase (blkPl_201).base (hooksException H) =
      libsignalSessionLib.blockProgram lsmpl 201 (hooksException H) :=
    IsLsBlockProg.eq_blockProgram
  rw [hP_eq]
  have hbase_ok : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 201 (hooksException H))
      (blkPl_201).base deserializeFullPlacedSpec := by
    rw [← hQ_eq]; exact deserializeFull_placed_ok (hooksException H)
  have hall_svc : (libsignalSessionLib.blockProgram lsmpl 201 (hooksException H)).allInstrs
      (fun ins => !ins.isSvc0) = true :=
    VerifiedLibraries.RustStd.blockProgram_rebase_allInstrs_not_isSvc0
      libsignalSessionLib lsmpl 201 blk201_noSvc0
  have hall_msr : (libsignalSessionLib.blockProgram lsmpl 201 (hooksException H)).allInstrs
      (fun ins => !ins.isMsrTpidrEl0) = true :=
    Obj.PlacedLib.program_noMsrTpidrEl0_of_patchSafe blk201_patchSafe_msr
      (libsignalSessionLib.blockPlacement lsmpl 201) (hooksException H)
  refine subroutine_ok_of_sepWP fun x R s0 hpc hrun hpre hal =>
    ⟨deserializeFullPlacedSpec.pre x s0, R, hpre, ?_⟩
  apply SepWP.of_reaches_pc
  intro R' hm hLP
  let Q0 := libsignalSessionLib.blockProgram lsmpl 201 (hooksException H)
  let keep := ProofLib.progKeep Q0
  have hLQ : Q0.CodeLoaded s0.mem := hLP.of_base_code rfl rfl
  have hLQ_strip : Q0.CodeLoaded (ProofLib.stripS keep s0).mem := by
    change Q0.CodeLoaded (ProofLib.stripExecOutside keep s0.mem)
    exact strip_codeLoaded_of_keep hLQ
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hm
  have hpre_eq : deserializeFullPlacedSpec.pre x (ProofLib.stripS keep s0) =
      deserializeFullPlacedSpec.pre x s0 := by
    rcases x with ⟨ptr, bs, sret⟩; cases s0; rfl
  have hm_strip' : (ProofLib.stripS keep s0).mem ⊨
      deserializeFullPlacedSpec.pre x (ProofLib.stripS keep s0) ∗ R_view := by
    rw [hpre_eq]; exact hm_strip
  have hpc_s : (ProofLib.stripS keep s0).pc = (blkPl_201).base := by cases s0; exact hpc
  have hrun_s : (ProofLib.stripS keep s0).status = .Running := by cases s0; exact hrun
  have hal_s : (ProofLib.stripS keep s0).spAligned = true := by cases s0; exact hal
  obtain ⟨sf', hstepsQ, hout, -⟩ :=
    hbase_ok.no_fault_before_outcome x R_view (ProofLib.stripS keep s0)
      hpc_s hrun_s hm_strip' hal_s hLQ_strip
  rcases hout with ⟨⟨hpcf', _, hrunf'⟩, ⟨hspf', hcsf'⟩, hpost'⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · obtain ⟨sf, hsf_eq, hstepsP, hvm, hfs⟩ :=
      steps_block201_lift_vm_fs H hall_svc hall_msr hstepsQ hrunf' s0 rfl hLQ
    have hpost_eq : deserializeFullPlacedSpec.post x (ProofLib.stripS keep s0) sf' =
        deserializeFullPlacedSpec.post x s0 sf := by
      rw [hsf_eq]; rcases x with ⟨ptr, bs, sret⟩; cases s0; cases sf; rfl
    rw [hpost_eq] at hpost'
    have hperm_eq : ∀ a, sf.mem.perm a = s0.mem.perm a := hvm.perm_eq
    have hpost_mem : ProofLib.stripExecOutside keep sf.mem ⊨
        deserializeFullPlacedSpec.post x s0 sf ∗ R_view := by
      have hm_eq : sf'.mem = ProofLib.stripExecOutside keep sf.mem := by rw [hsf_eq]; cases sf; rfl
      rwa [← hm_eq]
    have hpost_sf : sf.mem ⊨ deserializeFullPlacedSpec.post x s0 sf ∗ R' :=
      hunstrip hperm_eq hpost_mem
    have hpcf : sf.pc = s0.readReg64 .x30 := by
      rw [hsf_eq] at hpcf'; cases s0; cases sf; exact hpcf'
    have hrunf : sf.status = .Running := by
      rw [hsf_eq] at hrunf'; cases sf; exact hrunf'
    have hspf : sf.sp = s0.sp := by
      rw [hsf_eq] at hspf'; cases s0; cases sf; exact hspf'
    have hcsf : CalleeSavedPreserved s0 sf := by
      rw [hsf_eq] at hcsf'; cases s0; cases sf; exact hcsf'
    refine ⟨sf, hstepsP, Or.inl ⟨hpcf, hrunf, deserializeFullPlacedSpec.post x s0 sf, hpost_sf, ?_⟩⟩
    refine ⟨fun hmR => ?_, hspf, hcsf⟩
    dsimp only [withVmAndFsPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hvm, hfs⟩, hmR⟩
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem pkDeserializeFull_vm_fs_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (ext : LibsignalHooks)
    [hcaller : IsLsBlockProg callerProg i ext]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_201).base
      (withLsCodeRoLoaded lsmpl (withVmAndFsPreserved deserializeFullPlacedSpec)) := by
  have h201 : subroutine_ok ((blkPC_201).rebase (blkPl_201).base ext)
      (blkPl_201).base (withLsCodeRoLoaded lsmpl (withVmAndFsPreserved deserializeFullPlacedSpec)) :=
    subroutine_ok_withLsCodeRoLoaded_of_plain (deserializeFull_vm_fs_placed_ok ext)
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg
    ((blkPC_201).rebase (blkPl_201).base ext) i 201 ext
    hcaller (instIsLsBlockProg_201 ext) (blkPl_201).base _
    h201 _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-! ## Parsing Callee `SepWPp` Wrappers -/

theorem r1b_call_splitSigned_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {cEnvs : RunCalleesEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {ret fp : BitVec 64} {file : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hc : RunCalleesPlacedFd A lim cEnvs H B σ)
    (hbnd : r1b_StackBounds B resStack) (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsmpl.base 592) (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0) (hfp : st_bl.readReg64 .fp = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0) (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = ret) (hx1 : st_bl.readReg64 .x1 = fp)
    (hx2 : (st_bl.readReg64 .x2).toNat = file.length)
    (hfit : FitsEnv M lim st (cEnvs.splitSigned file))
    (hpanicK : PanicK g s0 Qp)
    (herr : ∀ (sf : State) (evs : List AllocEvent) (eCap ePtr : BitVec 64) (eBs : List (BitVec 8)),
      cEnvs.splitSigned file evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      splitSigned file = none → sf.fs.files = st_bl.fs.files → sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ speWord 1) ∗
          ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          memRegion (ret + 32#64) 16 ∗
          ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
          (fp ↦ₛ file) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom)
    (hok : ∀ (sf : State) (evs : List AllocEvent) (id : BitVec 32) (key sig : List (BitVec 8)),
      cEnvs.splitSigned file evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      splitSigned file = some (id, key, sig) →
      sf.fs = st_bl.fs →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ splitOkTag) ∗
          ((ret + 8#64) ↦₆₄ (fp + 4#64)) ∗
          ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 key.length) ∗
          ((ret + 24#64) ↦₃₂ id) ∗ memRegion (ret + 28#64) 4 ∗
          ((ret + 32#64) ↦₆₄ (fp + 4#64 + BitVec.ofNat 64 key.length)) ∗
          ((ret + 40#64) ↦₆₄ 64#64) ∗
          (fp ↦ₛ file) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      ((fp ↦ₛ file) ∗ memRegion ret 48 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F)
      Q Qp oom := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call_placed (x := ({ ret := ret, fp := fp, file := file, ro := false }, st))
    (hc.splitSigned hbnd.splitSigned) hinv hpc hrun hal_bl hlr hpanicK
    (F := F) ?_ (hnext := ?_)
  · dsimp only [splitSignedSpecPlacedOkFs, withLsCodeRoLoaded, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [splitSignedSpecPlacedOkFs, withLsCodeRoLoaded, bytesAt, splitSignedResultAt]
    simp only [Bool.false_eq_true, ↓reduceIte, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_imp =>
      SepWPp.exists_elim fun evs => SepWPp.pure_elim fun ⟨htr_f, hevs⟩ => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq_placed hh hsteps htr_f
    cases hsp_res : splitSigned file with
    | none =>
      dsimp only [speAt]
      have hstr_drop : strRefAt (ret + 32#64) (utf8 "bundle") ⊢
          ∃∗ fnPtr : BitVec 64, (fnPtr ↦ᵣ utf8 "bundle") ∗ memRegion (ret + 32#64) 16 := by
        dsimp only [strRefAt]
        refine Entails.sepExists_elim fun fnPtr => Entails.sepExists_right fnPtr ?_
        have hcells :
            ((ret + 32#64) ↦₆₄ fnPtr) ∗
              ((ret + 32#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "bundle").length) ⊢
            memRegion (ret + 32#64) 16 := r1b_cells2_to_region16 _ _ _
        exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_right hcells)
      have hev : ((ret ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A.repAlloc (ret + 8#64) bs)) ⊢
          ∃∗ eBs : List (BitVec 8), ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
            (ret ↦₆₄ speWord 1) ∗
            ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
            ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
            ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs := by
        rw [sepExists_sepConj_right]
        refine Entails.sepExists_elim fun eBs => Entails.sepExists_right eBs ?_
        have hv := vecU8_to_ownedBytes A.repAlloc (ret + 8#64) eBs
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv
        exact Entails.trans (sepConj_mono_right hv) (by
          simp only [sepExists_sepConj_right]
          exact Entails.sepExists_elim fun eCap => Entails.sepExists_right eCap
            (Entails.sepExists_elim fun ePtr => Entails.sepExists_right ePtr
              (Entails.of_eq (by sep_ac_rfl))))
      refine sepWPp_weaken_pre
        (P' := (∃∗ eBs : List (BitVec 8), ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
          (ret ↦₆₄ speWord 1) ∗
          ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs) ∗
          (∃∗ fnPtr : BitVec 64, (fnPtr ↦ᵣ utf8 "bundle") ∗ memRegion (ret + 32#64) 16) ∗
          (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F) ?_ ?_
      · rw [hsp]
        refine Entails.trans (Entails.of_eq (show _ =
          ((ret ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A.repAlloc (ret + 8#64) bs)) ∗
          strRefAt (ret + 32#64) (utf8 "bundle") ∗
          (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F by sep_ac_rfl)) ?_
        exact sepConj_mono hev (sepConj_mono_left hstr_drop)
      · simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun fnPtr =>
          SepWPp.exists_elim fun eBs =>
          SepWPp.exists_elim fun eCap =>
          SepWPp.exists_elim fun ePtr => ?_
        refine sepWPp_weaken_pre
          (P' := (fnPtr ↦ᵣ utf8 "bundle") ∗
            ((ret ↦₆₄ speWord 1) ∗
              ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
              ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
              memRegion (ret + 32#64) 16 ∗
              ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
              (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
              A.pool lim (M.stepEvents evs st) sf ∗ F))
          (Entails.of_eq (by sep_ac_rfl)) ?_
        exact r1b_sepWPp_drop_left (herr sf evs eCap ePtr eBs hevs hin_f hcs_f hsp_res hfiles_f htr_f)
    | some triple =>
      rcases triple with ⟨id, key, sig⟩
      have hfs_eq : sf.fs = st_bl.fs := fs_eq_of_splitSigned_eq_some hfs_imp hsp_res
      dsimp only
      refine sepWPp_weaken_pre ?_
        (hok sf evs id key sig hevs hin_f hcs_f hsp_res hfs_eq hfiles_f htr_f)
      rw [hsp]
      exact Entails.of_eq (by sep_ac_rfl)

theorem r1b_call_splitId_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {cEnvs : RunCalleesEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {ret fp : BitVec 64} {file : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hc : RunCalleesPlacedFd A lim cEnvs H B σ)
    (hbnd : r1b_StackBounds B resStack) (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsmpl.base 593) (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0) (hfp : st_bl.readReg64 .fp = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0) (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = ret) (hx1 : st_bl.readReg64 .x1 = fp)
    (hx2 : (st_bl.readReg64 .x2).toNat = file.length)
    (hfit : FitsEnv M lim st (cEnvs.splitId file))
    (hpanicK : PanicK g s0 Qp)
    (herr : ∀ (sf : State) (evs : List AllocEvent) (eCap ePtr : BitVec 64) (eBs : List (BitVec 8)),
      cEnvs.splitId file evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      splitId file = none → sf.fs.files = st_bl.fs.files → sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ speWord 1) ∗
          ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          memRegion (ret + 32#64) 16 ∗
          ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
          (fp ↦ₛ file) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom)
    (hok : ∀ (sf : State) (evs : List AllocEvent) (id : BitVec 32) (key : List (BitVec 8)),
      cEnvs.splitId file evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      splitId file = some (id, key) →
      sf.fs = st_bl.fs →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ splitOkTag) ∗
          ((ret + 8#64) ↦₃₂ id) ∗ memRegion (ret + 12#64) 4 ∗
          ((ret + 16#64) ↦₆₄ (fp + 4#64)) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 key.length) ∗
          memRegion (ret + 32#64) 16 ∗
          (fp ↦ₛ file) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      ((fp ↦ₛ file) ∗ memRegion ret 48 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F)
      Q Qp oom := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call_placed (x := ({ ret := ret, fp := fp, file := file, ro := false }, st))
    (hc.splitId hbnd.splitId) hinv hpc hrun hal_bl hlr hpanicK
    (F := F) ?_ (hnext := ?_)
  · dsimp only [splitIdSpecPlacedOkFs, withLsCodeRoLoaded, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [splitIdSpecPlacedOkFs, withLsCodeRoLoaded, bytesAt, splitIdResultAt]
    simp only [Bool.false_eq_true, ↓reduceIte, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_imp =>
      SepWPp.exists_elim fun evs => SepWPp.pure_elim fun ⟨htr_f, hevs⟩ => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq_placed hh hsteps htr_f
    cases hsp_res : splitId file with
    | none =>
      dsimp only [speAt]
      have hstr_drop : strRefAt (ret + 32#64) (utf8 "bundle") ⊢
          ∃∗ fnPtr : BitVec 64, (fnPtr ↦ᵣ utf8 "bundle") ∗ memRegion (ret + 32#64) 16 := by
        dsimp only [strRefAt]
        refine Entails.sepExists_elim fun fnPtr => Entails.sepExists_right fnPtr ?_
        have hcells :
            ((ret + 32#64) ↦₆₄ fnPtr) ∗
              ((ret + 32#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "bundle").length) ⊢
            memRegion (ret + 32#64) 16 := r1b_cells2_to_region16 _ _ _
        exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_right hcells)
      have hev : ((ret ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A.repAlloc (ret + 8#64) bs)) ⊢
          ∃∗ eBs : List (BitVec 8), ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
            (ret ↦₆₄ speWord 1) ∗
            ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
            ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
            ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs := by
        rw [sepExists_sepConj_right]
        refine Entails.sepExists_elim fun eBs => Entails.sepExists_right eBs ?_
        have hv := vecU8_to_ownedBytes A.repAlloc (ret + 8#64) eBs
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv
        exact Entails.trans (sepConj_mono_right hv) (by
          simp only [sepExists_sepConj_right]
          exact Entails.sepExists_elim fun eCap => Entails.sepExists_right eCap
            (Entails.sepExists_elim fun ePtr => Entails.sepExists_right ePtr
              (Entails.of_eq (by sep_ac_rfl))))
      refine sepWPp_weaken_pre
        (P' := (∃∗ eBs : List (BitVec 8), ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
          (ret ↦₆₄ speWord 1) ∗
          ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs) ∗
          (∃∗ fnPtr : BitVec 64, (fnPtr ↦ᵣ utf8 "bundle") ∗ memRegion (ret + 32#64) 16) ∗
          (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F) ?_ ?_
      · rw [hsp]
        refine Entails.trans (Entails.of_eq (show _ =
          ((ret ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A.repAlloc (ret + 8#64) bs)) ∗
          strRefAt (ret + 32#64) (utf8 "bundle") ∗
          (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F by sep_ac_rfl)) ?_
        exact sepConj_mono hev (sepConj_mono_left hstr_drop)
      · simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun fnPtr =>
          SepWPp.exists_elim fun eBs =>
          SepWPp.exists_elim fun eCap =>
          SepWPp.exists_elim fun ePtr => ?_
        refine sepWPp_weaken_pre
          (P' := (fnPtr ↦ᵣ utf8 "bundle") ∗
            ((ret ↦₆₄ speWord 1) ∗
              ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
              ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
              memRegion (ret + 32#64) 16 ∗
              ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
              (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
              A.pool lim (M.stepEvents evs st) sf ∗ F))
          (Entails.of_eq (by sep_ac_rfl)) ?_
        exact r1b_sepWPp_drop_left (herr sf evs eCap ePtr eBs hevs hin_f hcs_f hsp_res hfiles_f htr_f)
    | some pair =>
      rcases pair with ⟨id, key⟩
      have hfs_eq : sf.fs = st_bl.fs := fs_eq_of_splitId_eq_some hfs_imp hsp_res
      dsimp only
      refine sepWPp_weaken_pre ?_
        (hok sf evs id key hevs hin_f hcs_f hsp_res hfs_eq hfiles_f htr_f)
      rw [hsp]
      exact Entails.of_eq (by sep_ac_rfl)

theorem r1b_call_pkDeserialize_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {g : RunCall} {s0 st_bl : State} {retOff : Nat}
    {ptr sret : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsmpl.base 201)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = ptr)
    (hx1 : (st_bl.readReg64 .x1).toNat = bs.length)
    (hx8 : st_bl.readReg64 .x8 = sret)
    (hlen : bs.length < 2 ^ 63)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      VmPreserved st_bl sf →
      sf.fs = st_bl.fs →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (deserializeResult33At sret (PublicKey.deserialize bs) ∗
          (ptr ↦ₛ bs) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      ((ptr ↦ₛ bs) ∗ memRegion sret 33 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ F)
      Q Qp oom := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call_placed (ptr, bs, sret)
    (pkDeserializeFull_vm_fs_placed_ok (callerProg := runProgPlaced H) (i := 579) H)
    hinv hpc hrun hal_bl hlr hpanicK (F := F) ?_ (hnext := ?_)
  · dsimp only [withVmAndFsPreserved, deserializeFullPlacedSpec]
    simp only [sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hx1, hx8, hlen⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [withVmAndFsPreserved, deserializeFullPlacedSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hvm_f, hfs_eq⟩ => SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq_placed hh hsteps htr_f
    refine sepWPp_weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sf hin_f hcs_f hvm_f hfs_eq hfiles_f htr_f)

theorem r1b_call_pkDeserialize_pool_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {g : RunCall} {s0 st_bl : State} {retOff : Nat}
    {ptr sret : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsmpl.base 201)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = ptr)
    (hx1 : (st_bl.readReg64 .x1).toNat = bs.length)
    (hx8 : st_bl.readReg64 .x8 = sret)
    (hlen : bs.length < 2 ^ 63)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs = st_bl.fs →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (deserializeResult33At sret (PublicKey.deserialize bs) ∗
          (ptr ↦ₛ bs) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st sf ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      ((ptr ↦ₛ bs) ∗ memRegion sret 33 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        A.pool lim st st_bl ∗ F)
      Q Qp oom :=
  r1b_call_pkDeserialize_placed_fd hh hinv hpc hrun hsp hfp hvregs hsp0 hlr
    hx0 hx1 hx8 hlen hpanicK fun sf hin_f hcs_f hvm_f hfs_eq hfiles_f htr_f => by
      rw [← A.pool_of_vmPreserved hvm_f]
      exact hnext sf hin_f hcs_f hfs_eq hfiles_f htr_f

private theorem subroutine_ok_lscro_withFds_of_withFds_lscro [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withFdsGe3Closed (withLsCodeRoLoaded lsmpl spec))) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (withFdsGe3Closed spec)) := by
  refine subroutine_ok_mono h ?_ ?_ (fun _ _ _ _ hp => hp)
  · intro x R s0 hpre
    dsimp only [withLsCodeRoLoaded, withFdsGe3Closed] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  · intro x R s0 sf hpost
    dsimp only [withLsCodeRoLoaded, withFdsGe3Closed] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

theorem r1b_call_kemDeserialize_of_kem_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {r p : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hkem : (slotWithFdsGe3Closed (slotsOfPlaced A lim sEnvs S needs).kemDeserialize).OkPlaced
      (lsProg_579 H) (blkPl_590).base)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : r1b_CodeOk st_bl.mem)
    (hfds : FdsGe3Closed st_bl.fs)
    (hpc : st_bl.pc = lsmpl.base 590)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = r)
    (hx1 : st_bl.readReg64 .x1 = p)
    (hx2 : st_bl.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hlen : bs.length < 2 ^ 63)
    (hfit : FitsEvents M lim st (kemDeserializeEvents bs))
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      FdsGe3Closed sf.fs →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (kemDeserResAt A.repAlloc r (kemPkDeserialize bs) ∗
          (p ↦ₛ bs) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (kemDeserializeEvents bs) st) sf ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (memRegion r 24 ∗ (p ↦ₛ bs) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F)
      Q Qp oom := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  have hcall := subroutine_ok_lscro_withFds_of_withFds_lscro
    (hkem (resStack - runFrame) hbnd.kem hbnd.sub63)
  refine r1b_call_placed (x := ({ r := r, ro := false, p := p, bs := bs }, st))
    hcall hinv hpc hrun hal_bl hlr hpanicK (F := F) ?_ (hnext := ?_)
  · dsimp only [withFdsGe3Closed, cliKemDeserializeSpec, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right hfds
    apply Entails.pure_right ⟨hx0, hx1, hx2, hlen, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [withFdsGe3Closed, cliKemDeserializeSpec, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun hfds_f => SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq_placed hh hsteps htr_f
    refine sepWPp_weaken_pre ?_ (hnext sf hin_f hcs_f hfds_f hfiles_f htr_f)
    rw [hsp]
    exact Entails.of_eq (by sep_ac_rfl)

theorem r1b_call_kemDeserialize_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {r p : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlacedFd A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs))
    (hbnd : r1b_StackBounds B resStack)
    (hinv : r1b_CodeOk st_bl.mem)
    (hfds : FdsGe3Closed st_bl.fs)
    (hpc : st_bl.pc = lsmpl.base 590)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = r)
    (hx1 : st_bl.readReg64 .x1 = p)
    (hx2 : st_bl.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hlen : bs.length < 2 ^ 63)
    (hfit : FitsEvents M lim st (kemDeserializeEvents bs))
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      FdsGe3Closed sf.fs →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (kemDeserResAt A.repAlloc r (kemPkDeserialize bs) ∗
          (p ↦ₛ bs) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (kemDeserializeEvents bs) st) sf ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (memRegion r 24 ∗ (p ↦ₛ bs) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F)
      Q Qp oom :=
  r1b_call_kemDeserialize_of_kem_placed_fd hh hc.kemDeserialize hbnd hinv hfds
    hpc hrun hsp hfp hvregs hsp0 hlr hx0 hx1 hx2 hlen hfit hpanicK hnext

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudgetFd
