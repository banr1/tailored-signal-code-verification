/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS0PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsPlaced
import ProofLib.Placed.OpcodeExclusion

/-!
# Budget-Threaded CLI Block `433` Segment `S0` Seam

Proves `s0_433_cli` (`S0PSeamPlaced`) on Block `433` via `OpcodeExclusion` under
`[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudgetPart2

open Arm64 ProofLib SepProp
open CryptoVerification (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  blkPC_252 blkPl_252 extract_withLsCodeLoaded libsignalMutatedBlocks libsignalSessionLib
  lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel uuidTryParseCodeSpec)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (blkPC_434 blkPl_434)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.MainHops.UuidFs (uuidTryParse_placed_okFs_F)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other)
open CryptoVerification.SignalSession.Cli.Slots (blackBox_row_placed)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS0PlacedBudget (
  s0_433_placed_ok_P_of_callees)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (S0PSeamPlaced)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

private theorem allBlocks_patchSafe :
    (libsignalSessionLib.blocks.all fun b =>
      b.patchSafe Obj.svc0Pat && b.patchSafe Obj.msrTpidrEl0Pat) = true := by decide +kernel

private theorem all_getD_of_all {α : Type} {p : α → Bool} (d : α) (hd : p d = true) :
    ∀ (l : List α) (i : Nat), l.all p = true → p (l.getD i d) = true
  | [], _, _ => hd
  | _ :: _, 0, h => by simp only [List.all_cons, Bool.and_eq_true] at h; exact h.1
  | _ :: tl, i + 1, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h; exact all_getD_of_all d hd tl i h.2

private theorem blockLib_patchSafe (j : Nat) :
    (libsignalSessionLib.blockLib j).text.patchSafe Obj.svc0Pat = true ∧
      (libsignalSessionLib.blockLib j).text.patchSafe Obj.msrTpidrEl0Pat = true := by
  have htxt : (libsignalSessionLib.blockLib j).text =
      libsignalSessionLib.blocks.getD j { code := [] } := rfl
  have h := all_getD_of_all ({ code := [] } : Obj.CodeBlock) (by decide +kernel)
    libsignalSessionLib.blocks j allBlocks_patchSafe
  rw [htxt]; simp only [Bool.and_eq_true] at h; exact h

private def unmutBlks : List Nat :=
  (List.range libsignalSessionLib.blocks.length).filter fun j => !(decide (j ∈ libsignalMutatedBlocks))

private def unmutKeep (pl : Obj.MultiPlacement) (a : BitVec 64) : Bool :=
  unmutBlks.any fun j => ProofLib.progKeep (libsignalSessionLib.blockProgram pl j (fun _ => none)) a

private theorem strip_lsCodeLoaded {pl : Obj.MultiPlacement} {m : Memory}
    (hcl : LibsignalCodeLoaded pl m) :
    LibsignalCodeLoaded pl (ProofLib.stripExecOutside (unmutKeep pl) m) := by
  intro j hj hunmut X O svc; have hL := hcl j hj hunmut X O svc
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun k hk => ?_
  have hno := hL.no_wrap
  let Pj := libsignalSessionLib.blockProgram pl j X O svc
  let Pj0 := libsignalSessionLib.blockProgram pl j (fun _ => none)
  have hsub : Pj0.base + BitVec.ofNat 64 k - Pj0.base = BitVec.ofNat 64 k := by bv_omega
  have hkeep0 : ProofLib.progKeep Pj0 (Pj.base + BitVec.ofNat 64 k) = true := by
    unfold ProofLib.progKeep
    change decide ((Pj0.base + BitVec.ofNat 64 k - Pj0.base).toNat < Pj.code.length) = true
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact decide_eq_true hk
  have hj_mem : j ∈ unmutBlks := List.mem_filter.mpr ⟨List.mem_range.mpr hj, by simp [hunmut]⟩
  have hkeep : unmutKeep pl (Pj.base + BitVec.ofNat 64 k) = true := List.any_eq_true.mpr ⟨j, hj_mem, hkeep0⟩
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq k hk, hL.perm_eq k hk, hL.isLazyFree_eq k hk⟩

private theorem findSome?_isSome_congr_local {α β γ : Type} (l : List α)
    (f : α → Option β) (g : α → Option γ) (h : ∀ x, (f x).isSome = (g x).isSome) :
    (l.findSome? f).isSome = (l.findSome? g).isSome := by
  induction l with
  | nil => rfl
  | cons x _ ih =>
    simp only [List.findSome?]; cases hf : f x <;> cases hg : g x <;> try first | exact ih | rfl
    all_goals (have hx := h x; rw [hf, hg] at hx; cases hx)

private theorem findSome?_ite_map_status_local {α : Type} (l : List (String × Nat)) (off : Nat)
    (tbl : String → Option α) {f : State → State}
    (h : (l.findSome? fun x =>
      if (x.2 == off) = true then (tbl x.1).map (fun _ (s : State) => s.setStatus (.Exception "ext"))
      else none) = some f)
    (s : State) : (f s).status = .Exception "ext" := by
  induction l with
  | nil => simp [List.findSome?] at h
  | cons hd tl ih =>
    simp only [List.findSome?] at h; cases ho : hd.2 == off
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h; exact ih h
    · simp only [ho, ↓reduceIte] at h
      cases htn : tbl hd.1 with
      | none => simp only [htn, Option.map] at h; exact ih h
      | some _ => simp only [htn, Option.map] at h; injection h with hf; subst hf; cases s; rfl

private theorem findSome?_const_none_local {α β : Type} (l : List α) :
    l.findSome? (fun _ => (none : Option β)) = none := by
  induction l with | nil => rfl | cons _ _ ih => exact ih

private theorem ls_hooksException_externAt?_isSome (pl : Obj.MultiPlacement)
    (i : Nat) (H : LibsignalHooks) (pc : BitVec 64) :
    ((libsignalSessionLib.blockProgram pl i (hooksException H)).externAt? pc).isSome =
      ((libsignalSessionLib.blockProgram pl i H).externAt? pc).isSome := by
  have hor : ∀ {α : Type} (a b : Option α), (a.or b).isSome = (a.isSome || b.isSome) := by
    intro _ a _; cases a <;> rfl
  unfold Program.externAt? Program.hookAtOff? Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program
  dsimp only; rw [hor, hor]
  rw [findSome?_isSome_congr_local _
    (fun x : String × Nat =>
      if (x.2 == (pc - (libsignalSessionLib.blockPlacement pl i).base).toNat) = true then
        hooksException H x.1 else none)
    (fun x : String × Nat =>
      if (x.2 == (pc - (libsignalSessionLib.blockPlacement pl i).base).toNat) = true then
        H x.1 else none)]
  intro x; cases (x.2 == (pc - (libsignalSessionLib.blockPlacement pl i).base).toNat) <;>
    simp [hooksException]

private theorem ls_hooksException_externAt?_not_running {pl : Obj.MultiPlacement}
    {i : Nat} {H : LibsignalHooks} {pc : BitVec 64} {f : State → State}
    (h : (libsignalSessionLib.blockProgram pl i (hooksException H)).externAt? pc = some f)
    (s : State) : (f s).status ≠ .Running := by
  unfold Program.externAt? Program.hookAtOff? Obj.MultiPlacedLib.blockProgram
    Obj.PlacedLib.program at h
  dsimp only [hooksException] at h; simp only [ite_self, findSome?_const_none_local, Option.or_none] at h
  rw [findSome?_ite_map_status_local _ _ _ h]; decide

private theorem blockProgram_none_externAt? (pl : Obj.MultiPlacement) (j : Nat) (pc : BitVec 64) :
    (libsignalSessionLib.blockProgram pl j (fun _ => none)).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program
  dsimp only; simp only [ite_self, findSome?_const_none_local, Option.or_none]

private theorem steps_ls_lift_strip (pl : Obj.MultiPlacement) (i : Nat) (H : LibsignalHooks)
    {s1' sf' : State}
    (hsteps : Steps (libsignalSessionLib.blockProgram pl i (hooksException H)) s1' sf')
    (hrun_f : sf'.status = .Running) :
    let P := libsignalSessionLib.blockProgram pl i H
    let keep := unmutKeep pl
    ∀ (s1 : State), s1' = ProofLib.stripS keep s1 → LibsignalCodeLoaded pl s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS keep sf ∧ Steps P s1 sf ∧ VmPreserved s1 sf := by
  intro P keep; let Q := libsignalSessionLib.blockProgram pl i (hooksException H)
  induction hsteps with
  | refl => intro s1 hs1 _; exact ⟨s1, hs1, .refl s1, VmPreserved.refl s1⟩
  | @step sa' sb' _ h1 hrest ih =>
    intro s1 hsa hcl1; subst hsa
    have hrb' : sb'.status = .Running := by
      cases hrest with | refl => exact hrun_f | step hs _ => cases hs <;> assumption
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ => exact False.elim (ls_hooksException_externAt?_not_running he _ hrb')
    | extern_fault _ _ _ => cases s1; cases hrb'
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      have hpc_eq : (ProofLib.stripS keep s1).pc = s1.pc := by cases s1; rfl
      have hmem_eq : (ProofLib.stripS keep s1).mem = ProofLib.stripExecOutside keep s1.mem := by
        cases s1; rfl
      rw [hpc_eq, hmem_eq] at hfe'
      have ⟨hex_q, hal_pc, hce'⟩ : (Q.externAt? s1.pc).isSome = false ∧ s1.pc.toNat % 4 = 0 ∧
          (ProofLib.stripExecOutside keep s1.mem).canExec s1.pc 4 = true := by
        unfold Program.fetchMem at hfe'
        split at hfe'; · contradiction
        rename_i h1; split at hfe'; · contradiction
        rename_i h2; split at hfe'; · contradiction
        rename_i h3; exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩
      have hkeep_pc : keep s1.pc = true := by
        have hcx := hce'; unfold Memory.canExec at hcx; rw [Memory.allPerm_iff] at hcx
        simpa using (ProofLib.strip_perm_x_imp (hcx 0 (by omega))).2
      obtain ⟨j, hj_mem, hkeep_j⟩ := List.any_eq_true.mp hkeep_pc
      have ⟨hj_lt, hj_unm⟩ : j < libsignalSessionLib.blocks.length ∧ (j ∈ libsignalMutatedBlocks) = false := by
        unfold unmutBlks at hj_mem; rw [List.mem_filter, List.mem_range] at hj_mem
        exact ⟨hj_mem.1, by simpa using hj_mem.2⟩
      let Rj := libsignalSessionLib.blockProgram pl j (fun _ => none)
      have hLj : Rj.CodeLoaded (ProofLib.stripExecOutside keep s1.mem) :=
        strip_lsCodeLoaded hcl1 j hj_lt hj_unm _ _ _
      have hin_j : (s1.pc - Rj.base).toNat + 4 ≤ Rj.code.length := by
        have hmod4_j : Rj.code.length % 4 = 0 := by
          change ((libsignalSessionLib.blockLib j).text.patched
            (libsignalSessionLib.blockPlacement pl j)).length % 4 = 0
          rw [Obj.CodeBlock.length_patched]; omega
        unfold ProofLib.progKeep at hkeep_j
        have hb_eq : (libsignalSessionLib.blockProgram pl j (fun _ => none)).base = Rj.base := rfl
        have hc_eq : (libsignalSessionLib.blockProgram pl j (fun _ => none)).code = Rj.code := rfl
        rw [hb_eq, hc_eq, decide_eq_true_eq] at hkeep_j
        have hal_base := hLj.aligned; have hal_off : (s1.pc - Rj.base).toNat % 4 = 0 := by bv_omega
        omega
      have hfm_Rj : Rj.fetchMem (ProofLib.stripExecOutside keep s1.mem) s1.pc = some inst := by
        unfold Program.fetchMem at hfe' ⊢; rw [hex_q] at hfe'; rw [blockProgram_none_externAt?]; exact hfe'
      have ⟨hps_svc, hps_msr⟩ := blockLib_patchSafe j
      have hHj : Obj.HoldsBytes (ProofLib.stripExecOutside keep s1.mem) Rj.base Rj.code
          (fun _ => Perm.rx) := fun k hk => ⟨hLj.byte_eq k hk, hLj.perm_eq k hk, hLj.isLazyFree_eq k hk⟩
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs_holdsBytes_in_code
          (Obj.PlacedLib.program_noSvc0_of_patchSafe hps_svc (libsignalSessionLib.blockPlacement pl j))
          hLj.aligned hLj.no_wrap hHj hin_j hfm_Rj
      have hnmsr : inst.isMsrTpidrEl0 = false := by
        simpa using Program.fetchMem_of_allInstrs_holdsBytes_in_code
          (Obj.PlacedLib.program_noMsrTpidrEl0_of_patchSafe hps_msr
            (libsignalSessionLib.blockPlacement pl j))
          hLj.aligned hLj.no_wrap hHj hin_j hfm_Rj
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        unfold Program.fetchMem at hfe' ⊢
        rw [hex_q] at hfe'; rw [← ls_hooksException_externAt?_isSome pl i H s1.pc, hex_q]
        simp only [Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq, not_true_eq_false] at hfe' ⊢
        have hce : s1.mem.canExec s1.pc 4 = true := by
          unfold Memory.canExec at hce' ⊢; rw [Memory.allPerm_iff] at hce' ⊢; intro k hk
          have hxk := hce' k hk; rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
        have hr32 : (ProofLib.stripExecOutside keep s1.mem).read32 s1.pc = s1.mem.read32 s1.pc := by
          simp [Memory.read32, ProofLib.strip_read8]
        simp only [hce', hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfe' ⊢; rwa [hr32] at hfe'
      have hev_Q : Q.evalInst inst (ProofLib.stripS keep s1) = ProofLib.stripS keep (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      obtain ⟨sf, hsf_eq, hsteps_P, hvm_rest⟩ := ih hrun_f (execInst inst s1) hev_Q
        (fun j' hj' hunm X O svc => hstep_P.codeLoaded (hcl1 j' hj' hunm X O svc))
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P,
        ((ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1).toVmPreserved
          (Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1)).trans hvm_rest⟩

private theorem uuidTryParse_placed_vm_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse))) := by
  have hprog : (blkPC_252).rebase (blkPl_252).base H =
      libsignalSessionLib.blockProgram lsmpl 252 H := IsLsBlockProg.eq_blockProgram
  have hQ : (blkPC_252).rebase (blkPl_252).base (hooksException H) =
      libsignalSessionLib.blockProgram lsmpl 252 (hooksException H) := IsLsBlockProg.eq_blockProgram
  have hok : subroutine_ok ((blkPC_252).rebase (blkPl_252).base (hooksException H)) (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse)) := by
    refine subroutine_ok_mono (uuidTryParse_placed_okFs_F (hooksException H))
      (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
    dsimp only [withLsCodeLoaded, Spec.keepsFs] at hq ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2
  apply subroutine_ok_outcome_intro; intro x R s0 hpc hrun hpre hsp
  obtain ⟨hcl_ls, hpre0⟩ := extract_withLsCodeLoaded hpre; dsimp only [withVmPreserved] at hpre0
  let keep := unmutKeep lsmpl; obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hpre0
  let s0' := ProofLib.stripS keep s0
  have hcl_strip : LibsignalCodeLoaded lsmpl s0'.mem := strip_lsCodeLoaded hcl_ls
  have hpre_strip : s0'.mem ⊨
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse)).pre x s0' ∗ R_view := by
    dsimp only [withLsCodeLoaded]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl_strip, ?_⟩
    have hpre_eq : (uuidTryParseCodeSpec uuidTryParse).pre x s0' =
        (uuidTryParseCodeSpec uuidTryParse).pre x s0 := by rcases x with ⟨p, bs, out⟩; cases s0; rfl
    rwa [hpre_eq]
  have hQL : ((blkPC_252).rebase (blkPl_252).base (hooksException H)).CodeLoaded s0'.mem :=
    hQ ▸ hcl_strip 252 (by decide) (by decide) (hooksException H) (fun _ => none) Syscall.standard
  obtain ⟨sf', hstepsQ0, hout, _⟩ := hok.no_fault_before_outcome x R_view s0'
    (by cases s0; exact hpc) (by cases s0; exact hrun) hpre_strip (by cases s0; exact hsp) hQL
  rcases hout with ⟨hret', hcc', hpost'⟩ | ⟨_, hpan'⟩ | ⟨_, _, hex'⟩ | ⟨_, hoom'⟩
  · obtain ⟨sf, hsf_eq, hstepsP0, hvm⟩ :=
      steps_ls_lift_strip lsmpl 252 H (hQ ▸ hstepsQ0) hret'.2.2 s0 rfl hcl_ls
    have hstepsP : Steps ((blkPC_252).rebase (blkPl_252).base H) s0 sf := by rw [hprog]; exact hstepsP0
    have hret : Returned s0 sf := by rw [hsf_eq] at hret'; cases s0; cases sf; exact hret'
    have hcc : CallingConventionPreserved s0 sf := by rw [hsf_eq] at hcc'; cases s0; cases sf; exact hcc'
    have hpost_strip : ProofLib.stripExecOutside keep sf.mem ⊨
        (uuidTryParseCodeSpec uuidTryParse).post x s0 sf ∗ R_view := by
      have hmem_sf' : sf'.mem = ProofLib.stripExecOutside keep sf.mem := by rw [hsf_eq]; cases sf; rfl
      have hpost_eq : (uuidTryParseCodeSpec uuidTryParse).post x s0' sf' =
          (uuidTryParseCodeSpec uuidTryParse).post x s0 sf := by
        rw [hsf_eq]; rcases x with ⟨p, bs, out⟩; cases s0; cases sf; rfl
      rwa [hmem_sf', hpost_eq] at hpost'
    have hpost : sf.mem ⊨ (withVmPreserved (uuidTryParseCodeSpec uuidTryParse)).post x s0 sf ∗ R := by
      dsimp only [withVmPreserved]; rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hvm, hunstrip hvm.perm_eq hpost_strip⟩
    exact reaches_outcome_steps hstepsP (reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hpost⟩))
  · exact False.elim (not_satisfies_false_sepConj hpan')
  · exact False.elim (not_satisfies_false_sepConj hex')
  · exact False.elim (not_satisfies_false_sepConj hoom')

/-- `S0PSeamPlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem s0_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S0PSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S tdEnv :=
  s0_433_placed_ok_P_of_callees
    ((cliGhostExterns_other g _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans
      (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W)))
    (uuidTryParse_placed_vm_ok (cliGhostExterns g (cliExternsPlaced mmpl W)))

end LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudgetPart2
