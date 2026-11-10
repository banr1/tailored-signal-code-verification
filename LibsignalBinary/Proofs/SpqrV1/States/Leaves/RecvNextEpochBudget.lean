/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<Ct2Sampled>::recv_next_epoch` (Budget-Threaded)

Budget-threaded contracts for `<Ct2Sampled>::recv_next_epoch` (`31` instructions): fixed-base
`ct2_sampled_recv_next_epoch_ok_ext{,_ofEnv}`, `.inImage img` / `StatesRecvContractsAx` lifts,
and relocatable `[LibsignalPlacement]` Block `355` contracts discharging `drop_glue::<[Poly; 16]>`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochBudget

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPl_355 libsignalSessionCode
  lsProg_355 lsmpl ls_subroutine_ok_of_block sepWP_seq_lscl
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1 (
  Epoch GF16 NUM_POLYS spqrAuthApi spqrPolyApi
)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct2Sampled)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (KeysUnsampled)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Auth (authenticatorAt)
open CryptoVerification.SpqrV1.Drop (
  chunkedCt2SampledAt chunkedKeysUnsampledAt dropGluePoly16Stack
  polyEncoderAt_entails_tag_vecs_tail unchunkedCt2SentAt vecGF16ListOf
)
open CryptoVerification.SpqrV1.Poly (polyArrayBytes)
open CryptoVerification.SpqrV1.States.Leaves (
  AuthWords Ct2SampledRecvNextEpochGhost authWordsList authenticatorAt_extract
  cells4_restore_4160_bottom ct2SampledRecvNextEpochName
  ct2Sampled_outA_recompose ct2Sampled_recv_next_epoch_ok ct2Sampled_stA_post_combine
  dropGluePoly16Name ep_add_one_beq_zero_false leavesProgAtExt memRegion_56_unfold
  relocatedHeap stackAt_4160_bottom stackAt_4160_top_unfold
  sub_ok_of_addr_eq subroutine_ok_withLsCodeLoaded_of_left
  wordsAt wordsAt_cons_off wordsAt_nil wordsBytes
)
open CryptoVerification.SpqrV1.States.Recv (
  growToCalleeExt sub_ok_inImage_growToCalleeExt_ax sub_ok_inImage_of_sub_ok_ax
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (
  dropGluePoly16Spec dropGluePoly16SpecBase drop_glue_poly16_placed_ok
)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget (
  Ct2SampledRecvNextEpochEnv
  ct2SampledRecvNextEpochEnv_nonempty
  ct2SampledRecvNextEpochSpec
  ct2SampledRecvNextEpochSpecBase
  ct2SampledRecvNextEpochSpecOfEnv
  ct2SampledRecvNextEpochSpecOfEnvBase
  subroutine_ok_ct2SampledRecvNextEpochSpecOfEnv_freeOnly
  Ct2SampledRecvNextEpochPlacedOkX
  Ct2SampledRecvNextEpochPlacedOkXOfEnv
  call_dropGluePoly16_cl
)

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrAuthApi
attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## 1. Sequencing & Framed Call Helpers -/

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

private theorem seq_vm_lscl {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {pl : Arm64.Obj.MultiPlacement} {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm →
      LibsignalCodeLoaded pl sm.mem → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post := by
  refine sepWP_seq_lscl hcl (mid := mid) ?_
  refine SepWP.mono h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ hcl_sm => ?_
  exact SepWP.weaken_pre hent (h2 sm hpc hrun hvm hcl_sm hQ)

/-- Plain framed call rule for `subroutine_ok prog entry (dropGluePoly16SpecBase M A lim)`. -/
theorem call_dropGluePoly16_budget
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (dropGluePoly16SpecBase M A lim))
    (arrA : BitVec 64) (vecs : List (List GF16)) (st : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = arrA)
    (hlen : vecs.length = NUM_POLYS)
    (hsplit : P = (vecGF16ListOf A.repAlloc arrA vecs ∗ A.pool lim st s ∗
      stackAt sp_call dropGluePoly16Stack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      AllocCallPreserved s sf → FreeOnlyEvs evs →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((memRegion arrA polyArrayBytes ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt sp_call dropGluePoly16Stack) ∗ Frame) post) :
    SepWP prog (s0.readReg64 Reg.lr) s P post := by
  refine SepWP.call_subroutine_frame hcall (x := (⟨arrA, vecs⟩, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    rw [hsplit, sepConj_assoc] at hm
    dsimp only [dropGluePoly16SpecBase]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hlen⟩, hm⟩
  · dsimp only [dropGluePoly16SpecBase]
    rw [hsp, sepExists_sepConj_left]
    apply SepWP.exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨htr, hacp, hevs⟩ => ?_
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hacp hevs

private theorem call_dropGluePoly16_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (dropGluePoly16Spec M A lim))
    (arrA : BitVec 64) (vecs : List (List GF16)) (st : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = arrA)
    (hlen : vecs.length = NUM_POLYS)
    (hsplit : P = (vecGF16ListOf A.repAlloc arrA vecs ∗ A.pool lim st s ∗
      stackAt sp_call dropGluePoly16Stack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      AllocCallPreserved s sf → FreeOnlyEvs evs →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((memRegion arrA polyArrayBytes ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt sp_call dropGluePoly16Stack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first
      | assumption
      | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog (s0.readReg64 Reg.lr) s P post := by
  refine SepWP.call_subroutine_frame hcall (x := (⟨arrA, vecs⟩, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    rw [hsplit, sepConj_assoc] at hm
    dsimp only [dropGluePoly16Spec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hlen, hlr.symm ▸ hlr_ls⟩, hm⟩
  · dsimp only [dropGluePoly16Spec]
    rw [hsp, sepExists_sepConj_left]
    apply SepWP.exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨htr, hacp, hevs⟩ => ?_
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hacp hevs

private theorem authWordsAt_expand (base : BitVec 64) (g : AuthWords) :
    wordsAt (base + 400#64) (authWordsList g) =
      (((base + 400#64) ↦₆₄ g.v1.w0) ∗
       ((base + 408#64) ↦₆₄ g.v1.w1) ∗
       ((base + 416#64) ↦₆₄ g.v1.w2) ∗
       ((base + 424#64) ↦₆₄ g.v2.w0) ∗
       ((base + 432#64) ↦₆₄ g.v2.w1) ∗
       ((base + 440#64) ↦₆₄ g.v2.w2)) := by
  dsimp only [authWordsList]
  simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
    show (400#64 + 8#64 : BitVec 64) = 408#64 from rfl,
    show (408#64 + 8#64 : BitVec 64) = 416#64 from rfl,
    show (416#64 + 8#64 : BitVec 64) = 424#64 from rfl,
    show (424#64 + 8#64 : BitVec 64) = 432#64 from rfl,
    show (432#64 + 8#64 : BitVec 64) = 440#64 from rfl]

private theorem post_combine_recvNextEpoch
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {F : ShaCompress}
    (outA stA : BitVec 64) (st : Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (out : KeysUnsampled (spqrAuthApi F))
    (hout_eq : out = { uc := { epoch := epoch, auth := st.uc.auth } })
    (tag : BitVec 64) (g : AuthWords) (st_b : M.σ) (evs : List AllocEvent) (s0 sf : State) :
    (memRegion (stA + 8#64) polyArrayBytes ∗
      A.pool lim (M.stepEvents evs st_b) sf ∗
      stackAt s0.sp dropGluePoly16Stack) ∗
      (((stA ↦₆₄ tag) ∗ memRegion (stA + 392#64) 8 ∗
        (((stA + 400#64) ↦₆₄ g.v1.w0) ∗ ((stA + 408#64) ↦₆₄ g.v1.w1) ∗
         ((stA + 416#64) ↦₆₄ g.v1.w2) ∗ ((stA + 424#64) ↦₆₄ g.v2.w0) ∗
         ((stA + 432#64) ↦₆₄ g.v2.w1) ∗ ((stA + 440#64) ↦₆₄ g.v2.w2)) ∗
        ((stA + 448#64) ↦₆₄ st.uc.epoch)) ∗
       (((outA ↦₆₄ g.v1.w0) ∗ ((outA + 8#64) ↦₆₄ g.v1.w1) ∗
         ((outA + 16#64) ↦₆₄ g.v1.w2) ∗ ((outA + 24#64) ↦₆₄ g.v2.w0) ∗
         ((outA + 32#64) ↦₆₄ g.v2.w1) ∗ ((outA + 40#64) ↦₆₄ g.v2.w2)) ∗
        relocatedHeap
          (fun dst => authenticatorAt A.repAlloc dst st.uc.auth)
          (wordsBytes (authWordsList g)) ∗
        ((outA + 48#64) ↦₆₄ epoch)) ∗
       memRegion (s0.sp - 4160#64) 32) ⊢
    chunkedKeysUnsampledAt A.repAlloc outA out ∗
      memRegion stA 456 ∗
      A.pool lim (M.stepEvents evs st_b) sf ∗
      stackAt s0.sp (dropGluePoly16Stack + 32) := by
  rw [← authWordsAt_expand stA g]
  have hst := ct2Sampled_stA_post_combine stA tag st.uc.epoch g
  have hout := ct2Sampled_outA_recompose A.repAlloc outA st.uc.auth epoch out hout_eq g
  have hstk : memRegion (s0.sp - 4160#64) 32 ∗ stackAt s0.sp dropGluePoly16Stack =
      stackAt s0.sp (dropGluePoly16Stack + 32) :=
    (stackAt_4160_bottom s0.sp).symm
  refine Entails.trans ?_
    (sepConj_mono hout (sepConj_mono hst (sepConj_mono_right (Entails.of_eq hstk))))
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 2. Relocatable `[LibsignalPlacement]` Proofs (Block `355`, `31` insns) -/

/-- Relocatable `<Ct2Sampled>::recv_next_epoch` (Block `355`, `31` insns) given a plain
    `subroutine_ok` hypothesis for `drop_glue::<[Poly; 16]>` at `lsmpl.base 265`. -/
theorem ct2_sampled_recv_next_epoch_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (lsProg_355 (Rust.withPanics ext))
      (lsmpl.base 265) (dropGluePoly16Spec M A lim)) :
    subroutine_ok (lsProg_355 (Rust.withPanics ext))
      (blkPl_355).base
      (ct2SampledRecvNextEpochSpec M A lim F) := by
  simp only [ct2SampledRecvNextEpochSpec, lsProg_355] at hdrop ⊢
  wp_init x_st s0
  rcases x_st with ⟨⟨outA, stA, st, epoch, out⟩, st_b⟩
  dsimp only at *
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA›
    ‹s0.readReg64 (Reg.gpr 2#5) = epoch›
  obtain ⟨hep_ne, hep_add, hout_eq⟩ := ct2Sampled_recv_next_epoch_ok (by assumption)
  have hz2 : (s0.readReg64 (Reg.gpr 2#5) == 0#64) = false :=
    hep_add ▸ ep_add_one_beq_zero_false hep_ne
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left (memRegion_56_unfold (s0.readReg64 (Reg.gpr 0#5))))) ?_
  wp_pull_exists
  rename_i o0 o1 o2 o3 o4 o5 o6
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left (stackAt_4160_top_unfold s0.sp))) ?_
  wp_pull_exists
  rename_i w0 w1 w2 w3
  unfold chunkedCt2SampledAt unchunkedCt2SentAt
  rw [BitVec.add_assoc (s0.readReg64 (Reg.gpr 1#5)) 400#64 48#64,
      show (400#64 + 48#64 : BitVec 64) = 448#64 from rfl]
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left
        (polyEncoderAt_entails_tag_vecs_tail A.repAlloc (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct2))) ?_
  wp_pull_exists
  rename_i tag vecs
  wp_focus_pure; intro hvecs_len
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left
        (authenticatorAt_extract A.repAlloc (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc.auth))) ?_
  wp_pull_exists
  rename_i g
  rw [authWordsAt_expand (s0.readReg64 (Reg.gpr 1#5)) g]
  refine seq_vm_clean (mid := lsmpl.base 265)
    (P_mid :=
      vecGF16ListOf A.repAlloc (s0.readReg64 (Reg.gpr 1#5) + 8#64) vecs ∗
      A.pool lim st_b s0 ∗
      (stackAt (s0.sp - 32#64) dropGluePoly16Stack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 2#5)) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 2#5)) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
         ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)))) ∗
      (((s0.readReg64 (Reg.gpr 1#5) ↦₆₄ tag) ∗
        memRegion (s0.readReg64 (Reg.gpr 1#5) + 392#64) 8 ∗
        (((s0.readReg64 (Reg.gpr 1#5) + 400#64) ↦₆₄ g.v1.w0) ∗
         ((s0.readReg64 (Reg.gpr 1#5) + 408#64) ↦₆₄ g.v1.w1) ∗
         ((s0.readReg64 (Reg.gpr 1#5) + 416#64) ↦₆₄ g.v1.w2) ∗
         ((s0.readReg64 (Reg.gpr 1#5) + 424#64) ↦₆₄ g.v2.w0) ∗
         ((s0.readReg64 (Reg.gpr 1#5) + 432#64) ↦₆₄ g.v2.w1) ∗
         ((s0.readReg64 (Reg.gpr 1#5) + 440#64) ↦₆₄ g.v2.w2)) ∗
        ((s0.readReg64 (Reg.gpr 1#5) + 448#64) ↦₆₄ st.uc.epoch)) ∗
       (((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ g.v1.w0) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ g.v1.w1) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ g.v1.w2) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ g.v2.w0) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ g.v2.w1) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ g.v2.w2)) ∗
        relocatedHeap
          (fun dst => authenticatorAt A.repAlloc dst st.uc.auth)
          (wordsBytes (authWordsList g)) ∗
        ((s0.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 2#5)))))
    (Q := fun s1 =>
      s1.sp = s0.sp ∧
      s1.readReg64 Reg.lr = s0.readReg64 Reg.lr ∧
      s1.readReg64 Reg.x0 = s0.readReg64 (Reg.gpr 1#5) + 8#64 ∧
      s1.trace = s0.trace ∧
      CalleeSavedPreserved s0 s1)
    ?_ ?_
  · wp_steps_vm
  · intro s1 hpc1 hrun1 hvm1 ⟨hsp1, hlr1, hx0_1, htr1, hcs1⟩
    rw [← A.pool_of_vmPreserved hvm1]
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (sepConj_mono_left (cells4_restore_4160_bottom s0.sp _ _ _ _))) ?_
    refine call_dropGluePoly16_placed_budget hdrop (s0.readReg64 (Reg.gpr 1#5) + 8#64) vecs st_b
      hpc1 hrun1 hsp1 (by simpa only [State.spAligned] using ‹s0.spAligned = true›)
      hlr1 htr1 hx0_1 hvecs_len (by sep_ac_rfl)
      (fun sf evs hpc_sf hrun_sf hsp_sf hcs_sf htrace_sf _hacp hevs => ?_)
    have hcs_tot : CalleeSavedPreserved s0 sf := hcs1.trans hcs_sf
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (post_combine_recvNextEpoch A lim (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5))
          st (s0.readReg64 (Reg.gpr 2#5)) out hout_eq tag g st_b evs s0 sf)) ?_
    refine SepWP.done hpc_sf hrun_sf ⟨?_, hsp_sf, hcs_tot⟩
    intro hm
    rw [satisfies_sepExists]
    refine ⟨evs, ?_⟩
    simp only [sepConj_assoc] at hm ⊢
    rw [satisfies_pure_sepConj]
    exact ⟨⟨htrace_sf, hevs⟩, hm⟩

/-- Relocatable `<Ct2Sampled>::recv_next_epoch` (Block `355`, `31` insns) given a
    `withLsCodeLoaded` `subroutine_ok` hypothesis for `drop_glue::<[Poly; 16]>` at `lsmpl.base 265`. -/
theorem ct2_sampled_recv_next_epoch_placed_cl_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (lsProg_355 (Rust.withPanics ext))
      (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim))) :
    Ct2SampledRecvNextEpochPlacedOkX M A lim F ext := by
  unfold Ct2SampledRecvNextEpochPlacedOkX
  apply subroutine_ok_withLsCodeLoaded_of_left
  simp only [ct2SampledRecvNextEpochSpec, lsProg_355] at hdrop ⊢
  wp_init x_st s0
  rcases x_st with ⟨⟨outA, stA, st, epoch, out⟩, st_b⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA›
    ‹s0.readReg64 (Reg.gpr 2#5) = epoch›
  obtain ⟨hep_ne, hep_add, hout_eq⟩ := ct2Sampled_recv_next_epoch_ok (by assumption)
  have hz2 : (s0.readReg64 (Reg.gpr 2#5) == 0#64) = false :=
    hep_add ▸ ep_add_one_beq_zero_false hep_ne
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left (memRegion_56_unfold (s0.readReg64 (Reg.gpr 0#5))))) ?_
  wp_pull_exists
  rename_i o0 o1 o2 o3 o4 o5 o6
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left (stackAt_4160_top_unfold s0.sp))) ?_
  wp_pull_exists
  rename_i w0 w1 w2 w3
  unfold chunkedCt2SampledAt unchunkedCt2SentAt
  rw [BitVec.add_assoc (s0.readReg64 (Reg.gpr 1#5)) 400#64 48#64,
      show (400#64 + 48#64 : BitVec 64) = 448#64 from rfl]
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left
        (polyEncoderAt_entails_tag_vecs_tail A.repAlloc (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct2))) ?_
  wp_pull_exists
  rename_i tag vecs
  wp_focus_pure; intro hvecs_len
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left
        (authenticatorAt_extract A.repAlloc (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc.auth))) ?_
  wp_pull_exists
  rename_i g
  rw [authWordsAt_expand (s0.readReg64 (Reg.gpr 1#5)) g]
  refine seq_vm_lscl hcl0 (mid := lsmpl.base 265)
    (P_mid :=
      vecGF16ListOf A.repAlloc (s0.readReg64 (Reg.gpr 1#5) + 8#64) vecs ∗
      A.pool lim st_b s0 ∗
      (stackAt (s0.sp - 32#64) dropGluePoly16Stack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 2#5)) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 2#5)) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
         ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)))) ∗
      (((s0.readReg64 (Reg.gpr 1#5) ↦₆₄ tag) ∗
        memRegion (s0.readReg64 (Reg.gpr 1#5) + 392#64) 8 ∗
        (((s0.readReg64 (Reg.gpr 1#5) + 400#64) ↦₆₄ g.v1.w0) ∗
         ((s0.readReg64 (Reg.gpr 1#5) + 408#64) ↦₆₄ g.v1.w1) ∗
         ((s0.readReg64 (Reg.gpr 1#5) + 416#64) ↦₆₄ g.v1.w2) ∗
         ((s0.readReg64 (Reg.gpr 1#5) + 424#64) ↦₆₄ g.v2.w0) ∗
         ((s0.readReg64 (Reg.gpr 1#5) + 432#64) ↦₆₄ g.v2.w1) ∗
         ((s0.readReg64 (Reg.gpr 1#5) + 440#64) ↦₆₄ g.v2.w2)) ∗
        ((s0.readReg64 (Reg.gpr 1#5) + 448#64) ↦₆₄ st.uc.epoch)) ∗
       (((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ g.v1.w0) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ g.v1.w1) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ g.v1.w2) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ g.v2.w0) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ g.v2.w1) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ g.v2.w2)) ∗
        relocatedHeap
          (fun dst => authenticatorAt A.repAlloc dst st.uc.auth)
          (wordsBytes (authWordsList g)) ∗
        ((s0.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 2#5)))))
    (Q := fun s1 =>
      s1.sp = s0.sp ∧
      s1.readReg64 Reg.lr = s0.readReg64 Reg.lr ∧
      s1.readReg64 Reg.x0 = s0.readReg64 (Reg.gpr 1#5) + 8#64 ∧
      s1.trace = s0.trace ∧
      CalleeSavedPreserved s0 s1)
    ?_ ?_
  · wp_steps_vm
  · intro s1 hpc1 hrun1 hvm1 hcl1 ⟨hsp1, hlr1, hx0_1, htr1, hcs1⟩
    rw [← A.pool_of_vmPreserved hvm1]
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (sepConj_mono_left (cells4_restore_4160_bottom s0.sp _ _ _ _))) ?_
    refine sepWP_seq_lscl hcl1 (mid := lsmpl.base 265) ?_
    refine call_dropGluePoly16_cl hdrop (s0.readReg64 (Reg.gpr 1#5) + 8#64) vecs st_b
      (ret_pc := s0.readReg64 Reg.lr) (sp_call := s0.sp)
      hpc1 hrun1 hsp1 (by simpa only [State.spAligned] using ‹s0.spAligned = true›)
      hlr1 htr1 hx0_1 hvecs_len (by sep_ac_rfl)
      (fun sf evs hpc_sf hrun_sf hsp_sf hcs_sf htrace_sf _hacp hevs => ?_)
    have hcs_tot : CalleeSavedPreserved s0 sf := hcs1.trans hcs_sf
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (post_combine_recvNextEpoch A lim (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5))
          st (s0.readReg64 (Reg.gpr 2#5)) out hout_eq tag g st_b evs s0 sf)) ?_
    refine SepWP.done hpc_sf hrun_sf ⟨?_, hsp_sf, hcs_tot⟩
    intro hm
    rw [satisfies_sepExists]
    refine ⟨evs, ?_⟩
    simp only [sepConj_assoc] at hm ⊢
    rw [satisfies_pure_sepConj]
    exact ⟨⟨htrace_sf, hevs⟩, hm⟩

/-- Closed `[LibsignalPlacement]` contract for `<Ct2Sampled>::recv_next_epoch` (Block `355`)
    discharging `drop_glue::<[Poly; 16]>` (Block `265`) via `drop_glue_poly16_placed_ok`. -/
theorem ct2_sampled_recv_next_epoch_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    Ct2SampledRecvNextEpochPlacedOkX M A lim F ext :=
  ct2_sampled_recv_next_epoch_placed_cl_ext
    (ls_subroutine_ok_of_block (i := 355) (j := 265)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_poly16_placed_ok (spqr_hook_ok_of_mem hdealloc))))

/-- Envelope-parametric `[LibsignalPlacement]` contract for `<Ct2Sampled>::recv_next_epoch`
    whenever `FreeOnlyEvs ⊆ Env x` pointwise. -/
theorem ct2_sampled_recv_next_epoch_placed_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : Ct2SampledRecvNextEpochGhost F → List AllocEvent → Prop}
    (hsub : ∀ x evs, FreeOnlyEvs evs → Env x evs)
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    Ct2SampledRecvNextEpochPlacedOkXOfEnv M A lim F ext Env := by
  have hok := ct2_sampled_recv_next_epoch_placed_ok_x (F := F) hdealloc
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s0 hp => ?_) (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · obtain ⟨hcl, hpre⟩ := CryptoVerification.extract_withLsCodeLoaded hp
    dsimp only [ct2SampledRecvNextEpochSpecOfEnv] at hpre
    dsimp only [withLsCodeLoaded, ct2SampledRecvNextEpochSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1, hpre.1.2.2.2.1, hpre.1.2.2.2.2.2⟩, hpre.2⟩
  · dsimp only [withLsCodeLoaded, ct2SampledRecvNextEpochSpec,
      ct2SampledRecvNextEpochSpecOfEnv] at hq ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, hsub x evs hq.1.2⟩, hq.2⟩

/-! ## 3. Fixed-Base (`b : BitVec 64`) & `.inImage img` Contracts -/

/-- Fixed-base `<Ct2Sampled>::recv_next_epoch` (`0x5fa5c`, `31` insns) given a `subroutine_ok`
    hypothesis for `drop_glue::<[Poly; 16]>`. -/
theorem ct2_sampled_recv_next_epoch_ok_ext
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr dropGluePoly16Name)
      (dropGluePoly16SpecBase M A lim)) :
    subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct2SampledRecvNextEpochName)
      (ct2SampledRecvNextEpochSpecBase M A lim F) := by
  simp only [ct2SampledRecvNextEpochSpecBase]
  have hfn := (ls_lemma% fnOff ct2SampledRecvNextEpochName)
  have hdrop_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct2SampledRecvNextEpochName -
        bv% (ls_off% ct2SampledRecvNextEpochName - ls_off% dropGluePoly16Name))
      (dropGluePoly16SpecBase M A lim) := sub_ok_of_addr_eq
    (Program.fnAddr_back
      (d := num% (ls_off% ct2SampledRecvNextEpochName - ls_off% dropGluePoly16Name))
      (b := b) (X := Rust.withPanics ext)
      hfn (ls_lemma% fnOff dropGluePoly16Name) (by decide))
    hdrop
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.States.Leaves.spqrStatesLeavesBin
    b trapHooks hfn (ls_off% ct2SampledRecvNextEpochName) 124
  dsimp only [leavesProgAtExt, ct2SampledRecvNextEpochName,
    BitVec.ofNat_eq_ofNat] at hdrop_raw ⊢
  simp +singlePass only [Program.fnAddr_rebase] at *
  clear hfn hdrop
  generalize_entry (libsignalSessionCode.fnOff
    "<spqr::v1::chunked::send_ct::Ct2Sampled>::recv_next_epoch") = fnOffVal
    reverting [Program.fetch, subroutine_ok]
  generalize b + BitVec.ofNat 64 fnOffVal = entry at *
  clear fnOffVal
  generalize_entry libsignalSessionCode = codeProg
    reverting [Program.fetch, subroutine_ok]
  examples_hide_fetches
  wp_init x_st s0
  rcases x_st with ⟨⟨outA, stA, st, epoch, out⟩, st_b⟩
  dsimp only at *
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA›
    ‹s0.readReg64 (Reg.gpr 2#5) = epoch›
  obtain ⟨hep_ne, hep_add, hout_eq⟩ := ct2Sampled_recv_next_epoch_ok (by assumption)
  have hz2 : (s0.readReg64 (Reg.gpr 2#5) == 0#64) = false :=
    hep_add ▸ ep_add_one_beq_zero_false hep_ne
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left (memRegion_56_unfold (s0.readReg64 (Reg.gpr 0#5))))) ?_
  wp_pull_exists
  rename_i o0 o1 o2 o3 o4 o5 o6
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left (stackAt_4160_top_unfold s0.sp))) ?_
  wp_pull_exists
  rename_i w0 w1 w2 w3
  unfold chunkedCt2SampledAt unchunkedCt2SentAt
  rw [BitVec.add_assoc (s0.readReg64 (Reg.gpr 1#5)) 400#64 48#64,
      show (400#64 + 48#64 : BitVec 64) = 448#64 from rfl]
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left
        (polyEncoderAt_entails_tag_vecs_tail A.repAlloc (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct2))) ?_
  wp_pull_exists
  rename_i tag vecs
  wp_focus_pure; intro hvecs_len
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_left
        (authenticatorAt_extract A.repAlloc (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc.auth))) ?_
  wp_pull_exists
  rename_i g
  rw [authWordsAt_expand (s0.readReg64 (Reg.gpr 1#5)) g]
  refine seq_vm_clean
    (mid := entry + (- bv% (ls_off% ct2SampledRecvNextEpochName - ls_off% dropGluePoly16Name)))
    (P_mid :=
      vecGF16ListOf A.repAlloc (s0.readReg64 (Reg.gpr 1#5) + 8#64) vecs ∗
      A.pool lim st_b s0 ∗
      (stackAt (s0.sp - 32#64) dropGluePoly16Stack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 2#5)) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 2#5)) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
         ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)))) ∗
      (((s0.readReg64 (Reg.gpr 1#5) ↦₆₄ tag) ∗
        memRegion (s0.readReg64 (Reg.gpr 1#5) + 392#64) 8 ∗
        (((s0.readReg64 (Reg.gpr 1#5) + 400#64) ↦₆₄ g.v1.w0) ∗
         ((s0.readReg64 (Reg.gpr 1#5) + 408#64) ↦₆₄ g.v1.w1) ∗
         ((s0.readReg64 (Reg.gpr 1#5) + 416#64) ↦₆₄ g.v1.w2) ∗
         ((s0.readReg64 (Reg.gpr 1#5) + 424#64) ↦₆₄ g.v2.w0) ∗
         ((s0.readReg64 (Reg.gpr 1#5) + 432#64) ↦₆₄ g.v2.w1) ∗
         ((s0.readReg64 (Reg.gpr 1#5) + 440#64) ↦₆₄ g.v2.w2)) ∗
        ((s0.readReg64 (Reg.gpr 1#5) + 448#64) ↦₆₄ st.uc.epoch)) ∗
       (((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ g.v1.w0) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ g.v1.w1) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ g.v1.w2) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ g.v2.w0) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ g.v2.w1) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ g.v2.w2)) ∗
        relocatedHeap
          (fun dst => authenticatorAt A.repAlloc dst st.uc.auth)
          (wordsBytes (authWordsList g)) ∗
        ((s0.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 2#5)))))
    (Q := fun s1 =>
      s1.sp = s0.sp ∧
      s1.readReg64 Reg.lr = s0.readReg64 Reg.lr ∧
      s1.readReg64 Reg.x0 = s0.readReg64 (Reg.gpr 1#5) + 8#64 ∧
      s1.trace = s0.trace ∧
      CalleeSavedPreserved s0 s1)
    ?_ ?_
  · wp_steps_vm
  · intro s1 hpc1 hrun1 hvm1 ⟨hsp1, hlr1, hx0_1, htr1, hcs1⟩
    rw [← A.pool_of_vmPreserved hvm1]
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (sepConj_mono_left (cells4_restore_4160_bottom s0.sp _ _ _ _))) ?_
    refine call_dropGluePoly16_budget hdrop_raw (s0.readReg64 (Reg.gpr 1#5) + 8#64) vecs st_b
      (by rw [hpc1]; bv_omega) hrun1 hsp1 (by simpa only [State.spAligned] using ‹s0.spAligned = true›)
      hlr1 htr1 hx0_1 hvecs_len (by sep_ac_rfl)
      (fun sf evs hpc_sf hrun_sf hsp_sf hcs_sf htrace_sf _hacp hevs => ?_)
    have hcs_tot : CalleeSavedPreserved s0 sf := hcs1.trans hcs_sf
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (post_combine_recvNextEpoch A lim (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5))
          st (s0.readReg64 (Reg.gpr 2#5)) out hout_eq tag g st_b evs s0 sf)) ?_
    refine SepWP.done hpc_sf hrun_sf ⟨?_, hsp_sf, hcs_tot⟩
    intro hm
    rw [satisfies_sepExists]
    refine ⟨evs, ?_⟩
    simp only [sepConj_assoc] at hm ⊢
    rw [satisfies_pure_sepConj]
    exact ⟨⟨htrace_sf, hevs⟩, hm⟩

/-- Native-stack (`dropGluePoly16Stack`) `.inImage img` contract for `<Ct2Sampled>::recv_next_epoch`. -/
theorem ct2_sampled_recv_next_epoch_ok_inImage
    {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr dropGluePoly16Name)
      (dropGluePoly16SpecBase M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct2SampledRecvNextEpochName)
      ((ct2SampledRecvNextEpochSpecBase M A lim F).inImage img) :=
  sub_ok_inImage_of_sub_ok_ax img (ct2_sampled_recv_next_epoch_ok_ext hdrop)

/-- Grown-stack (`statesRecvCalleeStackXExt`, `35936` B) `.inImage img` contract for
    `<Ct2Sampled>::recv_next_epoch`. -/
theorem ct2_sampled_recv_next_epoch_ok_ax
    {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (leavesProgAtExt img.base ext)
      ((leavesProgAtExt img.base ext).fnAddr dropGluePoly16Name)
      (dropGluePoly16SpecBase M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct2SampledRecvNextEpochName)
      ((growToCalleeExt dropGluePoly16Stack
        (ct2SampledRecvNextEpochSpecBase M A lim F)).inImage img) :=
  sub_ok_inImage_growToCalleeExt_ax dropGluePoly16Stack
    (fun _ _ _ => Or.inl rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (ct2_sampled_recv_next_epoch_ok_inImage hdrop)

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochBudget
