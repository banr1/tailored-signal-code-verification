/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanupBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
public import ProofLib.Placed.OpcodeExclusion
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs -- shake: keep
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.WireCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `ratchet_key = Some(rk)` Head for `<SignalMessage>::try_from`

Lifts `deserializeFull_placed_ok` (Block `201`) to `VmPreserved` and proves the relocatable
`[LibsignalPlacement]` budget-threaded `post_rk_some_head_wp_placed` segment (`+0x3b0 → +0x4c4`)
on Block `85`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSomeBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (PublicKey SignalProtocolError)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement LibsignalHooks libsignalSessionLib lsLogFilterAddr lsmpl
   blkPC_201 blkPl_201)
open CryptoVerification.RustHeap (vecHeader)
open CryptoVerification.LibsignalTripleRatchet
  (blkPC_85 blkPl_85 blkLib_eq_85 deserializeName logOff
   keys_ls_subroutine_ok_of_block_cro subroutine_ok_withLsCodeRoLoaded_of_plain
   LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (speAt speWord)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropSpeName DropSpeGhost dropSpeStackX)
open CryptoVerification.LibsignalTripleRatchet.Prost (skipFieldStackX)
open CryptoVerification.LibsignalTripleRatchet.Wire renaming SepWPp → WSepWPp
open CryptoVerification.LibsignalTripleRatchet.Wire
  (tryFromPlacedProg tryFromPlacedImg logOff_tryFromPlacedImg
   PostEpilogueStatePlaced LoopExitStatePlaced
   vecU8Buf vecU8BufRest vecU8Buf_entails_slice_rest slice_rest_entails_vecU8Buf
   cap_add2_ne_of_lt cap_add1_eq_of_lt stackAt_sub_split entails_of_eq
   spe40_of_rk_ct wireTail64_entails_memRegion64 memRegion48_split33_15
   deserializeResult33At deserializeFullPlacedSpec deserializeFull_placed_ok)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget (DropSpeOkWPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanupBudget
  (postNoPanicQp pool_eq_of_vmPreserved wpp_sync_pre wpp_of_sepWP_end_noPanic_placed
   wpp_call_noPanic_placed)
open VerifiedLibraries.RustStd (blockProgram_rebase_allInstrs_not_isSvc0)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `VmPreserved` lift for `PublicKey::deserialize` (Block `201`) -/

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
  unfold Program.externAt? Program.hookAtOff? MultiPlacedLib.blockProgram PlacedLib.program
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
  unfold Program.externAt? Program.hookAtOff? MultiPlacedLib.blockProgram PlacedLib.program at h
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

private theorem steps_block201_lift_vm [LibsignalPlacement] (H : LibsignalHooks)
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
        Steps P s1 sf ∧ VmPreserved s1 sf := by
  intro Q P
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, hs1, .refl s1, VmPreserved.refl s1⟩
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
      obtain ⟨sf, hsf_eq, hsteps_P, hvm_rest⟩ :=
        ih hrun_f (execInst inst s1) hev_Q hLQ_next
      have hvm1 : VmPreserved s1 (execInst inst s1) :=
        (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1).toVmPreserved
          (execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1)
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P, hvm1.trans hvm_rest⟩

theorem deserializeFull_vm_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base
      (withVmPreserved deserializeFullPlacedSpec) := by
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
  · obtain ⟨sf, hsf_eq, hstepsP, hvm⟩ :=
      steps_block201_lift_vm H hall_svc hall_msr hstepsQ hrunf' s0 rfl hLQ
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
    dsimp only [withVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm, hmR⟩
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem deserializeFull_vm_ok_at_placed [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok (tryFromPlacedProg H)
      ((blkPl_85).ρ deserializeName)
      (withLsCodeRoLoaded lsmpl (withVmPreserved deserializeFullPlacedSpec)) := by
  have h1 := keys_ls_subroutine_ok_of_block_cro (callerProg := tryFromPlacedProg H)
    (subroutine_ok_withLsCodeRoLoaded_of_plain (deserializeFull_vm_placed_ok H))
  simp only [deserializeName, arm64_norm]
  exact h1

/-! ## Relocatable `[LibsignalPlacement]` `post_rk_some_head_wp_placed` (Block `85`) -/

local macro "wp_steps_sync_rk85 " mid:term : tactic => `(tactic| (
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_85).rebase (blkPl_85).base (hooksException _))
    blkLib_eq_85 TryFromPostCleanupBudget.blk85_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by first | wp_norm_lhs | simp [arm64_norm]) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  first
    | refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
        (hnext := ?_)
    | refine ProofLib.SepWP.transport_atStatePool
        (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
        (hnext := ?_)
))

private theorem wpp_call_s [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {s0 s : State} {P F : SepProp} {φ : Prop}
    {Q : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (T : State → SepProp)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T s)) (hφ : φ)
    (hP : P = T s ∗ F := by sep_focus)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → LibsignalCodeRoLoaded lsmpl sf.mem →
      CalleeSavedPreserved s sf →
      WSepWPp prog ret sf (spec.post x s sf ∗ F) Q (postNoPanicQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    WSepWPp prog ret s P Q (postNoPanicQp s0) :=
  wpp_call_noPanic_placed x hcall hpc hrun hsp hcl hlr hspec hφ hP hnext hexit hpan hoom_eq

theorem post_rk_some_head_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hDropSpe : DropSpeOkWPlaced A lim H)
    (st : M.σ) {s0 s : State}
    {sp' x19 x20 x21 x23 w16 w32 w40 w72 w80 w88 w96
      rkCap rkPtr ctCap ctPtr ctLen pqCap pqPtr pqLen adCap adPtr adLen : BitVec 64}
    {w28 w48 w60 w64 cTag cVal pcTag pcVal : BitVec 32}
    (rk : List (BitVec 8))
    (hst : LoopExitStatePlaced s0 sp' x19 x20 x21 x23 s)
    (hpc : s.pc = (blkPl_85).base + 944#64)
    (hrun : s.status = .Running)
    (hx24 : s.readReg64 .x24 = 0#64) :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1220#64) s
      (((sp' + 16#64) ↦₆₄ w16) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
        ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
        ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗ ((sp' + 64#64) ↦₃₂ w64) ∗
        ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
        ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗
        vecHeader (sp' + 176#64) rkCap rkPtr (BitVec.ofNat 64 rk.length) ∗
        vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗
        vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗
        ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ∗
        logOff tryFromPlacedImg ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 sp' sf ∧
        sf.pc = (blkPl_85).base + 1220#64 ∧
        sf.status = .Running ∧
        sf.readReg64 .x19 = x19 ∧ sf.readReg64 .x20 = x20 ∧
        sf.readReg64 .x21 = x21 ∧ sf.readReg64 .x22 = adCap ∧
        sf.readReg64 .x23 = x23 ∧ sf.readReg64 .x24 = BitVec.ofNat 64 rk.length ∧
        sf.readReg64 .x25 = pqCap ∧ sf.readReg64 .x26 = rkPtr ∧
        sf.readReg64 .x27 = ctCap ∧ sf.readReg64 .x28 = ctPtr ∧
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((sp' + 16#64) ↦₆₄ adLen) ∗ ((sp' + 28#64) ↦₃₂ cVal) ∗
            ((sp' + 32#64) ↦₆₄ ctLen) ∗ ((sp' + 40#64) ↦₆₄ pqLen) ∗
            ((sp' + 48#64) ↦₃₂ pcTag) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗ ((sp' + 64#64) ↦₃₂ cTag) ∗
            ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
            ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
            deserializeResult33At (sp' + 176#64) (PublicKey.deserialize rk) ∗
            memRegion (sp' + 209#64) 15 ∗
            memRegion (sp' + 224#64) 64 ∗
            vecU8Buf A.repAlloc rkCap rkPtr rk ∗
            logOff tryFromPlacedImg ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  rcases hst with ⟨hregs, hsp, hcl, htr⟩
  have hsp_eq : s.sp = sp' := hregs.sp
  have hx19 : s.readReg64 .x19 = x19 := hregs.x19_eq
  have hx20 : s.readReg64 .x20 = x20 := hregs.x20_eq
  have hx21 : s.readReg64 .x21 = x21 := hregs.x21_eq
  have hx23 : s.readReg64 .x23 = x23 := hregs.x23_eq
  have hx26 : s.readReg64 .x26 = speWord 2 := hregs.x26
  have hcallSpe := hDropSpe
  clear hDropSpe
  have hcallDeser := deserializeFull_vm_ok_at_placed H
  refine WSepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (vecU8Buf_entails_slice_rest A.repAlloc rkCap rkPtr rk)))))))))))))) ?_
  simp only [sepConj_assoc]
  refine WSepWPp.mono_pre (P' :=
      ⌜rk.length ≤ rkCap.toNat ∧ rkCap.toNat < 2 ^ 63 ∧ rkPtr ≠ 0⌝ ∗
      (((sp' + 16#64) ↦₆₄ w16) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
        ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
        ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗ ((sp' + 64#64) ↦₃₂ w64) ∗
        ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
        ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗
        vecHeader (sp' + 176#64) rkCap rkPtr (BitVec.ofNat 64 rk.length) ∗
        (rkPtr ↦ₛ rk) ∗ vecU8BufRest A.repAlloc rkCap rkPtr rk ∗
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗
        vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗
        ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ∗
        logOff tryFromPlacedImg ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine WSepWPp.pure_pre (fun ⟨hrk_le, hrk_lt, _⟩ => ?_)
  have hrk_add2 := cap_add2_ne_of_lt hrk_lt
  have hrk_add1 := cap_add1_eq_of_lt hrk_lt
  have hstackSpe := stackAt_sub_split sp' dropSpeStackX (skipFieldStackX 100)
  refine WSepWPp.mono_pre (P' :=
      ((sp' + 16#64) ↦₆₄ w16) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
      ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
      ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗ ((sp' + 64#64) ↦₃₂ w64) ∗
      ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
      ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗
      ((sp' + 176#64) ↦₆₄ rkCap) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗
      ((sp' + 192#64) ↦₆₄ BitVec.ofNat 64 rk.length) ∗
      (rkPtr ↦ₛ rk) ∗ vecU8BufRest A.repAlloc rkCap rkPtr rk ∗
      ((sp' + 200#64) ↦₆₄ ctCap) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗ ((sp' + 216#64) ↦₆₄ ctLen) ∗
      ((sp' + 224#64) ↦₆₄ pqCap) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗ ((sp' + 240#64) ↦₆₄ pqLen) ∗
      ((sp' + 248#64) ↦₆₄ adCap) ∗ ((sp' + 256#64) ↦₆₄ adPtr) ∗ ((sp' + 264#64) ↦₆₄ adLen) ∗
      ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
      ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ∗
      logOff tryFromPlacedImg ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
    (by
      dsimp only [vecHeader]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      exact Entails.refl _) ?_
  refine WSepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ dropSpeName) ?_
  wp_steps_sync_rk85 ((blkPl_85).ρ dropSpeName)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl1
  have hspe40 := spe40_of_rk_ct sp' rkPtr (BitVec.ofNat 64 rk.length) ctCap ctPtr ctLen
  have htail64 := wireTail64_entails_memRegion64 sp' pqCap pqPtr pqLen adCap adPtr adLen
    cTag cVal pcTag pcVal
  have hspe_eq : speAt A.repAlloc [] (sp' + 176#64) .invalidProtobufEncoding =
      ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 := by
    dsimp only [speAt]
    have ha : sp' + 176#64 + 8#64 = sp' + 184#64 := by bv_omega
    rw [ha]
  refine wpp_sync_pre (fun s1 =>
      ((sp' + 176#64) ↦₆₄ speWord 2) ∗
      (((sp' + 184#64) ↦₆₄ rkPtr) ∗ ((sp' + 192#64) ↦₆₄ BitVec.ofNat 64 rk.length) ∗
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen) ∗
      (vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗
        ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal)) ∗
      ((sp' + 16#64) ↦₆₄ adLen) ∗ ((sp' + 28#64) ↦₃₂ cVal) ∗
      ((sp' + 32#64) ↦₆₄ ctLen) ∗ ((sp' + 40#64) ↦₆₄ pqLen) ∗
      ((sp' + 48#64) ↦₃₂ pcTag) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗ ((sp' + 64#64) ↦₃₂ cTag) ∗
      ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
      ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
      (rkPtr ↦ₛ rk) ∗ vecU8BufRest A.repAlloc rkCap rkPtr rk ∗
      logOff tryFromPlacedImg ∗ A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100))
    (by
      dsimp only [vecHeader]
      apply entails_of_eq
      simp only [arm64_norm]
      sep_ac_rfl) ?_
  refine WSepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono hspe40 (sepConj_mono_left htail64))) ?_
  refine wpp_call_s
    (⟨⟨sp' + 176#64, [], .invalidProtobufEncoding⟩, st⟩ : DropSpeGhost × M.σ) hcallSpe
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align [hsp_eq] hsp) hcl1
    (ret_pc := (blkPl_85).base + 1200#64) (by simp [arm64_norm])
    (fun s1 => speAt A.repAlloc [] (sp' + 176#64) .invalidProtobufEncoding ∗
      A.pool lim st s1 ∗ stackAt sp' dropSpeStackX)
    (φ := sp' + 176#64 = sp' + 176#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_85).base + 1200#64))
    (by simp [dropSpeSpecX, hsp_eq, arm64_norm])
    ⟨rfl, ⟨85, by decide, 1200, by decide, rfl⟩⟩
    (by rw [hspe_eq, hstackSpe]; sep_focus)
    ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [dropSpeSpecX]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine WSepWPp.exists_pre fun evs => ?_
  refine WSepWPp.pure_pre fun htr2 => ?_
  rw [sepConj_left_comm (memRegion (sp' + 176#64) 48) ⌜FreeOnlyEvs evs⌝]
  refine WSepWPp.pure_pre fun hfree => ?_
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, _⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  have htr2_eq : s2.trace = s0.trace := by simp [htr2, htr, arm64_norm]
  have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
  have hx20_2 : s2.readReg64 .x20 = x20 := by simp [hx20_cs, hx20, arm64_norm]
  have hx21_2 : s2.readReg64 .x21 = x21 := by simp [hx21_cs, hx21, arm64_norm]
  have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, arm64_norm]
  have hx23_2 : s2.readReg64 .x23 = x23 := by simp [hx23_cs, hx23, arm64_norm]
  have hx24_2 : s2.readReg64 .x24 = BitVec.ofNat 64 rk.length := by simp [hx24_cs, arm64_norm]
  have hx25_2 : s2.readReg64 .x25 = pqCap := by simp [hx25_cs, arm64_norm]
  have hx26_2 : s2.readReg64 .x26 = rkPtr := by simp [hx26_cs, arm64_norm]
  have hx27_2 : s2.readReg64 .x27 = ctCap := by simp [hx27_cs, arm64_norm]
  have hx28_2 : s2.readReg64 .x28 = ctPtr := by simp [hx28_cs, arm64_norm]
  have hrk_len_lt : rk.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrk_le hrk_lt
  have hrk_toNat : (BitVec.ofNat 64 rk.length).toNat = rk.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WSepWPp.of_sepWP_placed hcl2 (mid := (blkPl_85).ρ deserializeName) ?_
  wp_steps_sync_rk85 ((blkPl_85).ρ deserializeName)
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ⟨inferInstance, ?_⟩
  intro hcl3
  have h48_split := memRegion48_split33_15 sp'
  refine wpp_sync_pre (fun s3 =>
      memRegion (sp' + 176#64) 48 ∗
      A.pool lim (M.stepEvents evs st) s3 ∗
      stackAt sp' dropSpeStackX ∗
      memRegion (sp' + 224#64) 64 ∗
      ((sp' + 16#64) ↦₆₄ adLen) ∗ ((sp' + 28#64) ↦₃₂ cVal) ∗
      ((sp' + 32#64) ↦₆₄ ctLen) ∗ ((sp' + 40#64) ↦₆₄ pqLen) ∗
      ((sp' + 48#64) ↦₃₂ pcTag) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗ ((sp' + 64#64) ↦₃₂ cTag) ∗
      ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
      ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
      (rkPtr ↦ₛ rk) ∗ vecU8BufRest A.repAlloc rkCap rkPtr rk ∗
      logOff tryFromPlacedImg ∗
      memRegion (sp' - BitVec.ofNat 64 (skipFieldStackX 100)) (skipFieldStackX 100 - dropSpeStackX))
    (by apply entails_of_eq; simp only [arm64_norm]; sep_ac_rfl) ?_
  refine wpp_call_noPanic_placed (rkPtr, rk, sp' + 176#64) hcallDeser
    (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
    (by tryFromPost_sp_align [hsp2_eq] hsp2_align) hcl3
    (ret_pc := (blkPl_85).base + 1220#64) (by simp [arm64_norm])
    (T := (rkPtr ↦ₛ rk) ∗ memRegion (sp' + 176#64) 33 ∗ (lsLogFilterAddr ↦₆₄ 0#64))
    (φ := rkPtr = rkPtr ∧ (BitVec.ofNat 64 rk.length).toNat = rk.length ∧
      sp' + 176#64 = sp' + 176#64 ∧ rk.length < 2 ^ 63)
    (by simp [withVmPreserved, deserializeFullPlacedSpec, arm64_norm])
    ⟨rfl, hrk_toNat, rfl, hrk_len_lt⟩
    (by rw [h48_split, logOff_tryFromPlacedImg]; sep_focus)
    ?_
  clear hcallDeser
  intro s4 hpc4 hrun4 hsp4 hsp4_align hcl4 hcs4
  dsimp only [withVmPreserved, deserializeFullPlacedSpec]
  simp only [sepConj_assoc]
  refine WSepWPp.pure_pre fun hvm4 => ?_
  refine WSepWPp.pure_pre fun htr4 => ?_
  rcases hcs4 with ⟨hx19_4cs, hx20_4cs, hx21_4cs, hx22_4cs, hx23_4cs, hx24_4cs, hx25_4cs, hx26_4cs, hx27_4cs, hx28_4cs, _⟩
  refine wpp_of_sepWP_end_noPanic_placed hcl4 ?_
  refine SepWP.done (by simp [hpc4, arm64_norm]) hrun4 ⟨inferInstance, ?_⟩
  intro _
  refine ⟨PostEpilogueStatePlaced.of_steps hcl4 (by simp [hsp4, hsp2_eq, arm64_norm]) hsp_eq hsp
      (by simp [htr4, htr2_eq, arm64_norm]),
    by simp [hpc4, arm64_norm], hrun4,
    by simp [hx19_4cs, hx19_2, arm64_norm],
    by simp [hx20_4cs, hx20_2, arm64_norm],
    by simp [hx21_4cs, hx21_2, arm64_norm],
    by simp [hx22_4cs, hx22_2, arm64_norm],
    by simp [hx23_4cs, hx23_2, arm64_norm],
    by simp [hx24_4cs, hx24_2, arm64_norm],
    by simp [hx25_4cs, hx25_2, arm64_norm],
    by simp [hx26_4cs, hx26_2, arm64_norm],
    by simp [hx27_4cs, hx27_2, arm64_norm],
    by simp [hx28_4cs, hx28_2, arm64_norm],
    evs, hfree, ?_⟩
  have hrepack := slice_rest_entails_vecU8Buf A.repAlloc rkCap rkPtr rk
  have hpool4 := pool_eq_of_vmPreserved A lim (M.stepEvents evs st) hvm4
  rw [← logOff_tryFromPlacedImg, hpool4]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hrepack)))))))))))))))
  apply entails_of_eq
  simp only [hstackSpe, arm64_norm]
  sep_ac_rfl

end LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSomeBudget
