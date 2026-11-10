/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledSteps
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Acknowledged` Arm (`AllocContractsX`, Part 1)

**Checked by Lean.** Lifts the `memcpy`-dependent entry copy (`+588 -> +608`) and exit paths
(`ct1Ack_noop_4516_ret`, `ct1Ack_still_4468_ret`, `ct1Ack_done_4468_ret`) of `.ct1Acknowledged`
to `AllocContractsX img A ext` (`extHookStack = 16384` B, `.inImage img`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff

private theorem ct1Ack_stackAt_statesRecvCallee_eq_extHook (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 3168 ∗ stackAt fsp extHookStack :=
  ProofLib.stackAt_split_bottom fsp extHookStack 3168 (by decide)

local elab "sep_ac_rfl_ct1Ack_ext" : tactic => do
  let g ← _root_.Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← _root_.Lean.instantiateMVars (← g.getType)).consumeMData
    let some (_, lhs, rhs) := ty.eq?
      | _root_.Lean.throwError "sep_ac_rfl_ct1Ack_ext: expected equality"
    if lhs == rhs then
      g.assign (← _root_.Lean.Meta.mkEqRefl lhs)
      _root_.Lean.Elab.Tactic.replaceMainGoal []
    else if let some (tbl, tA, tB) := ProofLib.SepSolver.synReifyPermTbl? lhs rhs then
      g.assign (← ProofLib.SepSolver.eqACOfTbl lhs rhs tbl tA tB)
      _root_.Lean.Elab.Tactic.replaceMainGoal []
    else
      _root_.Lean.Elab.Tactic.evalTactic (← `(tactic| sep_frame))

private theorem sepWP_weaken_mono_ct1Ack_ext {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post post' : State → SepProp → Prop}
    (h : SepWP prog target_pc s P' post')
    (hpost : ∀ sf Pf, sf.pc = target_pc → sf.status = .Running → post' sf Pf → post sf Pf)
    (hP : P = P' := by sep_ac_rfl_ct1Ack_ext) :
    SepWP prog target_pc s P post :=
  hP ▸ SepWP.mono h hpost

private theorem ct1Ack_memcpy_ok_at_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName :=
      by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (session2MemcpySpecX.inImage img) :=
  memcpy_ok_at2_ext_x hA (name := name) (k := k) hk

private theorem ct1Ack_call_memcpy_relocate_cs_inImage_stk {img : Obj.Image} {prog : Program}
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (session2MemcpySpecX.inImage img))
    {n stk k_stk : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F) (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hin : ImgCallInv img s) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hstk : stk = extHookStack + k_stk := by decide)
    (hle : extHookStack + k_stk ≤ 2 ^ 64 := by decide)
    (hsplit : P = (memRegion dst n ∗ F src ∗ stackAt sp_call stk) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 → ImgCallInv img sf →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n ∗ stackAt sp_call stk) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  apply SepWP.seq_inImage (mid := ret_pc) hin
  have hstk_split : stackAt sp_call stk =
      memRegion (sp_call - BitVec.ofNat 64 stk) k_stk ∗ stackAt sp_call extHookStack := by
    subst hstk; exact ProofLib.stackAt_split_bottom sp_call extHookStack k_stk hle
  have hsplit' : P = (memRegion dst n ∗ F src) ∗
      (stackAt sp_call extHookStack ∗ memRegion (sp_call - BitVec.ofNat 64 stk) k_stk ∗ Frame) := by
    rw [hsplit, hstk_split]; sep_ac_rfl_ct1Ack_ext
  rw [hsplit']
  refine SepWP.fold (Leaves.relocate_pre_entails hrel dst src
    (stackAt sp_call extHookStack ∗ memRegion (sp_call - BitVec.ofNat 64 stk) k_stk ∗ Frame))
    (sepConj_emp _).symm ?_
  rw [sepConj_emp]; wp_pull_exists; rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := relocatedHeap F bs ∗ memRegion (sp_call - BitVec.ofNat 64 stk) k_stk ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [Spec.inImage, session2MemcpySpecX]
    rw [hsp, hlen, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hin.1, hin.2⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl_ct1Ack_ext)) hm⟩
  · dsimp only [Spec.inImage, session2MemcpySpecX]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    have hcomm :
        ((dst ↦ₛ bs) ∗ ((src ↦ₛ bs) ∗ stackAt sp_call extHookStack)) ∗
          (relocatedHeap F bs ∗ memRegion (sp_call - BitVec.ofNat 64 stk) k_stk ∗ Frame) =
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗
          (relocatedHeap F bs ∗ (stackAt sp_call stk ∗ Frame)) := by
      rw [hstk_split]; sep_ac_rfl_ct1Ack_ext
    rw [hcomm]
    refine SepWP.fold (Leaves.relocate_post_entails dst src hlen (stackAt sp_call stk ∗ Frame))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp, show (F dst ∗ memRegion src n) ∗ (stackAt sp_call stk ∗ Frame) =
        (F dst ∗ memRegion src n ∗ stackAt sp_call stk) ∗ Frame by sep_ac_rfl_ct1Ack_ext]
    exact SepWP.done hpc_sf hrun_sf fun hinv_sf =>
      hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
        ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hinv_sf

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48

set_option maxHeartbeats 1200000 in
private theorem ct1Ack_states_recv_writeback_59e88_step {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    {F_tail : BitVec 64 → SepProp} (hrel : Relocatable 376 F_tail)
    (s0 s : State) (outA : BitVec 64) (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true) (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗ F_tail ((s0.sp - 4240#64) + 576#64) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
      (fun sm Pm => ImgCallInv img sm →
        SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sm Pm
          (fun sf Pf =>
            (Pf ⊢ P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 s sp) ∗
              F_tail (outA + 512#64) ∗ memRegion (outA + 888#64) 40 ∗
              ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗ ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗
              ((outA + 944#64) ↦₁₂₈ sp.q200) ∗ stackAt s0.sp statesRecvStackX) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) := by
  have hmemcpy_raw := ct1Ack_memcpy_ok_at_ext hA statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
  have hepilogue := @states_recv_epilogue_59fd0 img.base ext s0
  states_recv_fetches_range img.base (Rust.withPanics ext) 18996 328
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hepilogue hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  refine SepWP.fold (memRegion_960_entails_writebackOut outA) (by sep_focus) ?_
  wp_pull_exists; rename_i v0 w_init q888 q904 w920 w928 w936 q944
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.done rfl (by simp only [arm64_norm, wp_norm]; exact hrun) fun hinv_call => ?_
  refine ct1Ack_call_memcpy_relocate_cs_inImage_stk (ret_pc := entry + 19284#64) (sp_call := sp0 - 4240#64)
    (stk := statesRecvCalleeStackX) (k_stk := 3168) hmemcpy_raw hrel (outA + 512#64) (sp0 - 3664#64)
    hinv_call rfl (by simp only [arm64_norm, wp_norm]; exact hrun)
    (by simp only [arm64_norm, wp_norm]; exact hsp) hfsp_align rfl
    (by exact ⟨by simp only [arm64_norm, wp_norm]; exact htr.1, by simp only [arm64_norm, wp_norm]; exact htr.2⟩)
    rfl rfl rfl (by decide) (by decide) (by sep_focus) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1 _hinv1
  have hx19_1 : sf1.readReg64 .x19 = outA :=
    hcs1.1.trans (by simp only [arm64_norm, wp_norm]; exact hx19)
  have hx20_1 : sf1.readReg64 .x20 = s.readReg64 .x20 :=
    hcs1.2.1.trans (by simp only [arm64_norm, wp_norm])
  wp_steps
  subst hsp0
  refine SepWP.fold
    (F := P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 s sp) ∗
      F_tail (outA + 512#64) ∗ ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗
      ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗ ((outA + 944#64) ↦₁₂₈ sp.q200) ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0)
    (sepConj_mono (q2_w1_entails_memRegion_40 (outA + 888#64) sp.q210 sp.q220 sp.w230)
      (sendEkFrame_entails_memRegion_4144 (s0.sp - 4240#64) sp)) ?_ ?_
  · dsimp only [words63At, writebackWords63, sendEkSpillsAt, words10At, Reg.x0, Reg.x1, Reg.x2,
      Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13,
      Reg.x14, Reg.x15, Reg.x16, Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
      Reg.x26, Reg.x27, Reg.x28, Reg.x30]
    simp only [pointsTo128_eq_pair64_recv, arm64_norm]; sep_ac_rfl_ct1Ack_ext
  · refine sepWP_weaken_mono_ct1Ack_ext
      (hepilogue _ (P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 s sp) ∗
        F_tail (outA + 512#64) ∗ memRegion (outA + 888#64) 40 ∗ ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗
        ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗ ((outA + 944#64) ↦₁₂₈ sp.q200))
        rfl hrun1 hsp1 hsp_align htr1)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl_ct1Ack_ext)), hsp_sf, hcs_sf, htr_sf⟩)

private theorem ct1Ack_states_recv_writeback_59e88_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    {F_tail : BitVec 64 → SepProp} (hrel : Relocatable 376 F_tail)
    (s0 s : State) (outA : BitVec 64) (sp : SendEkSpills) (P_rest : SepProp)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true) (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗ F_tail ((s0.sp - 4240#64) + 576#64) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 s sp) ∗
          F_tail (outA + 512#64) ∗ memRegion (outA + 888#64) 40 ∗
          ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗ ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗
          ((outA + 944#64) ↦₁₂₈ sp.q200) ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  SepWP.seq_inImage hinv
    (ct1Ack_states_recv_writeback_59e88_step hA hrel s0 s outA sp P_rest
      hpc hrun hsp hsp_align hx19 htr)

private theorem ct1Ack_seq_clean_inImage {prog : Program} {img : Obj.Image} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → ImgCallInv img sm → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  SepWP.seq_inImage hinv
    (SepWP.mono h1 fun sm Pm hpcm hrunm ⟨hPm, hQ⟩ hinv_m =>
      SepWP.weaken_pre hPm (h2 sm hpcm hrunm hinv_m hQ))

theorem ct1Ack_sepWPp_seq_clean_inImage {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {Q_ok Q_pan : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → ImgCallInv img sm → Q sm →
      SepWPp prog ret sm P_mid Q_ok Q_pan) :
    SepWPp prog ret s P Q_ok Q_pan :=
  CryptoVerification.SepWPp.of_sepWP_frozen hinv.1 hinv.2
    (SepWP.mono h1 fun sm Pm hpcm hrunm ⟨hPm, hQ⟩ hF hsym =>
      SepWPp.weaken_pre hPm (h2 sm hpcm hrunm ⟨hF, hsym⟩ hQ))

theorem call_memcpy_words66_cs_ext {img : Obj.Image} {prog : Program}
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (session2MemcpySpecX.inImage img))
    (dst src : BitVec 64) (w : Words66)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hin : ImgCallInv img s)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = 528)
    (hsplit : P = (memRegion dst 528 ∗ words66At src w ∗ stackAt sp_call statesRecvCalleeStackX) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace → ImgCallInv img sf →
      SepWP prog target_pc sf
        ((words66At dst w ∗ words66At src w ∗ stackAt sp_call statesRecvCalleeStackX) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  apply SepWP.seq_inImage (mid := ret_pc) hin
  have hsplit' : P =
      (memRegion dst 528 ∗ (src ↦ₛ wordsBytes (words66List w)) ∗ stackAt sp_call extHookStack) ∗
        (memRegion (sp_call - 19552#64) 3168 ∗ Frame) := by
    rw [hsplit, ct1Ack_stackAt_statesRecvCallee_eq_extHook sp_call, words66At_eq_pointsToBytes src w]
    sep_ac_rfl_ct1Ack_ext
  rw [hsplit']
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, wordsBytes (words66List w)))
    (F := memRegion (sp_call - 19552#64) 3168 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [Spec.inImage, session2MemcpySpecX]
    rw [hsp, length_wordsBytes_words66List, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hin.1, hin.2⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl_ct1Ack_ext)) hm⟩
  · dsimp only [Spec.inImage, session2MemcpySpecX]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    have hpost_eq :
        ((dst ↦ₛ wordsBytes (words66List w)) ∗
          ((src ↦ₛ wordsBytes (words66List w)) ∗ stackAt sp_call extHookStack)) ∗
          (memRegion (sp_call - 19552#64) 3168 ∗ Frame) =
        (words66At dst w ∗ words66At src w ∗ stackAt sp_call statesRecvCalleeStackX) ∗ Frame := by
      rw [ct1Ack_stackAt_statesRecvCallee_eq_extHook sp_call,
          words66At_eq_pointsToBytes dst w, words66At_eq_pointsToBytes src w]
      sep_ac_rfl_ct1Ack_ext
    rw [hpost_eq]
    exact SepWP.done hpc_sf hrun_sf fun hinv_sf =>
      hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hinv_sf

theorem ct1Ack_step_588_608_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (s : State) (fsp out selfA msgA : BitVec 64) (w : Words66) (Frame : SepProp)
    (hinv : ImgCallInv img s)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = out)
    (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 608#64) s
      (memRegion (fsp + 976#64) 528 ∗
       words66At (selfA + 8#64) w ∗
       stackAt fsp statesRecvCalleeStackX ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          words66At (fsp + 976#64) w ∗
          words66At (selfA + 8#64) w ∗
          stackAt fsp statesRecvCalleeStackX ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = selfA ∧
        sm.readReg64 .x24 = msgA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx1 hx19 hx24
  have hmemcpy_raw := ct1Ack_memcpy_ok_at_ext hAx statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
  apply SepWP.seq_inImage
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName +
      bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) hinv
  states_recv_fetches_range img.base (Rust.withPanics ext) 588 20
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done rfl (by simp only [arm64_norm, wp_norm]; exact hrun) fun hinv_call => ?_
  refine call_memcpy_words66_cs_ext (s0 := s) (ret_pc := entry + 608#64) (sp_call := s.sp)
    hmemcpy_raw (s.sp + 976#64) (s.readReg64 .x1 + 8#64) w
    hinv_call rfl (by simp only [arm64_norm, wp_norm]; exact hrun)
    (by simp only [arm64_norm, wp_norm]) hfsp_align rfl
    (by simp only [arm64_norm, wp_norm]) rfl rfl rfl (by sep_ac_rfl_ct1Ack_ext) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1 _hinv1
  have hx19_1 : sf1.readReg64 .x19 = s.readReg64 .x19 :=
    hcs1.1.trans (by simp only [arm64_norm, wp_norm])
  have hx20_1 : sf1.readReg64 .x20 = s.readReg64 .x1 :=
    hcs1.2.1.trans (by simp only [arm64_norm, wp_norm])
  have hx24_1 : sf1.readReg64 .x24 = s.readReg64 .x24 :=
    hcs1.2.2.2.2.2.1.trans (by simp only [arm64_norm, wp_norm])
  have hx29_1 : sf1.readReg64 .x29 = s.readReg64 .x29 :=
    hcs1.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, wp_norm])
  wp_done

theorem ct1Ack_noop_4516_ret_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (s0 s1 : State) (outA selfA : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (w : Words66) (sp : SendEkSpills) (P_rest : SepProp)
    (hinv1 : ImgCallInv img s1)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 4516#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = s0.sp - 4240#64)
    (hx9 : s1.readReg64 .x9 = w.b1.w5) (hx19 : s1.readReg64 .x19 = outA)
    (hx20 : s1.readReg64 .x20 = selfA) (htr : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      (P_rest ∗ memRegion outA v1RecvSize ∗ (selfA ↦₆₄ 11#64) ∗ words66At (selfA + 8#64) w ∗
        memRegion (selfA + 536#64) 392 ∗ words66At (s0.sp - 4240#64 + 976#64) w ∗
        relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
        memRegion (s0.sp - 4240#64 + 1504#64) 352 ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗ memRegion (s0.sp - 4240#64 + 576#64) 376 ∗
        memRegion (s0.sp - 4240#64 + 1856#64) 880 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Acknowledged st }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine SepWP.fold (memRegion_576_376_split_ekTail fsp) (by sep_focus) ?_
  wp_pull_exists; rename_i q576_old w592_old
  set sp1 := ct1AckSpills4516 sp w
  refine ct1Ack_seq_clean_inImage hinv1
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 4924#64)
    (P_mid := P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
      stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
      ekTail376 w.q63 w.w65 (fsp + 576#64) ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s2 =>
      s2.sp = fsp ∧ s2.readReg64 .x0 = w.b5.w5 ∧ s2.readReg64 .x1 = w.b0.w0 ∧
      s2.readReg64 .x2 = w.b5.w7 ∧ s2.readReg64 .x3 = w.b2.w9 ∧
      s2.readReg64 .x4 = w.b4.w9 ∧ s2.readReg64 .x5 = w.b4.w8 ∧
      s2.readReg64 .x6 = w.b5.w0 ∧ s2.readReg64 .x7 = w.b1.w9 ∧
      s2.readReg64 .x10 = w.b1.w6 ∧ s2.readReg64 .x11 = w.b5.w4 ∧
      s2.readReg64 .x12 = w.b4.w0 ∧ s2.readReg64 .x13 = w.b5.w1 ∧
      s2.readReg64 .x15 = w.b2.w7 ∧ s2.readReg64 .x16 = w.b4.w7 ∧
      s2.readReg64 .x17 = w.b4.w5 ∧ s2.readReg64 .x18 = w.b5.w3 ∧
      s2.readReg64 .x19 = outA ∧ s2.readReg64 .x22 = w.b5.w2 ∧
      s2.readReg64 .x24 = w.b3.w1 ∧ s2.readReg64 .x25 = w.b3.w9 ∧
      s2.readReg64 .x26 = w.b0.w5 ∧ s2.readReg64 .x30 = w.b5.w9 ∧ TraceCalleeSaved s2 s0)
    ?_ ?_
  · have hstep1 := ct1Ack_step_4516_4924 s1 fsp selfA w592_old q576_old w sp
      (P_rest ∗ memRegion outA v1RecvSize ∗ (selfA ↦₆₄ 11#64) ∗
       words10At (selfA + 8#64) w.b0 ∗ words10At (selfA + 88#64) w.b1 ∗
       words10At (selfA + 168#64) w.b2 ∗ words10At (selfA + 248#64) w.b3 ∗
       words10At (selfA + 328#64) w.b4 ∗ words10At (selfA + 408#64) w.b5 ∗
       ((selfA + 504#64) ↦₆₄ w.w62) ∗ memRegion (selfA + 536#64) 392 ∗
       relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
       memRegion (fsp + 1504#64) 352 ∗ stackAt fsp statesRecvCalleeStackX ∗
       memRegion (fsp + 600#64) 352 ∗ memRegion (fsp + 1856#64) 880 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp hx9 hx20
    refine SepWP.weaken_pre (Entails.of_eq ?_) (SepWP.mono hstep1 ?_)
    · dsimp only [words66At]; simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]; sep_ac_rfl_ct1Ack_ext
    · intro s2 Pm _ _ ⟨hPm, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
        h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19, h2_22,
        h2_24, h2_25, h2_26, _, h2_30, htr2⟩
      refine ⟨Entails.trans hPm ?_, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
        h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19.trans hx19, h2_22,
        h2_24, h2_25, h2_26, h2_30, htr2.trans htr⟩
      have hself := selfA_ct1Acknowledged_entails_memRegion selfA w
      have h976 := words66At_976_352_entails_memRegion_880 fsp w
      refine Entails.trans (Entails.of_eq (show _ =
        (((selfA ↦₆₄ 11#64) ∗ words66At (selfA + 8#64) w ∗ memRegion (selfA + 536#64) 392) ∗
         (words66At (fsp + 976#64) w ∗ memRegion (fsp + 1504#64) 352)) ∗
        (P_rest ∗ memRegion outA v1RecvSize ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
         stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
         ekTail376 w.q63 w.w65 (fsp + 576#64) ∗ memRegion (fsp + 1856#64) 880 ∗
         sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by
          dsimp only [words66At, ekTail376]; simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]; sep_ac_rfl_ct1Ack_ext)) ?_
      exact Entails.trans (sepConj_mono_left (sepConj_mono hself h976)) (Entails.of_eq (by sep_ac_rfl_ct1Ack_ext))
  · intro s2 hpc2 hrun2 hinv2 ⟨hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
      h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19, h2_22,
      h2_24, h2_25, h2_26, h2_30, htr2⟩
    set sp2 := ct1AckSpills4924 s2 sp1
    refine ct1Ack_seq_clean_inImage hinv2
      (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64)
      (P_mid := (P_rest ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w))) ∗
        memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp2 ∗
        ekTail376 w.q63 w.w65 (fsp + 576#64) ∗ memRegion (fsp + 976#64) 880 ∗
        memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = outA ∧
        writebackWords63 s3 sp2 =
          { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
            q60 := w.q60, w62 := w.w62 } ∧ TraceCalleeSaved s3 s0)
      ?_ ?_
    · have hstep2 := ct1Ack_step_4924_18996 s2 fsp sp1
        (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
         stackAt fsp statesRecvCalleeStackX ∗ ekTail376 w.q63 w.w65 (fsp + 576#64) ∗
         memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
         sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
        hfsp_align hpc2 hrun2 hsp2
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl_ct1Ack_ext)) (SepWP.mono hstep2 ?_)
      intro s3 Pm _ _ ⟨hPm, hsp3, h3_0, h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7,
        h3_8, h3_9, h3_10, h3_11, h3_12, h3_13, h3_14, h3_15, h3_16, h3_17, h3_19,
        h3_20, h3_21, h3_22, h3_23, h3_24, h3_25, h3_26, h3_27, h3_28, _, h3_30, htr3⟩
      have hwb := writebackWords63_ct1Ack_noop s2 s3 sp w
        h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6 h2_7 h2_10 h2_11 h2_12 h2_13
        h2_15 h2_16 h2_17 h2_18 h2_22 h2_24 h2_25 h2_26 h2_30
        h3_0 h3_1 h3_2 h3_3 h3_4 h3_5 h3_6 h3_7 h3_8 h3_9 h3_10 h3_11 h3_12
        h3_13 h3_14 h3_15 h3_16 h3_17 h3_20 h3_21 h3_22 h3_23 h3_24 h3_25
        h3_26 h3_27 h3_28 h3_30
      refine ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl_ct1Ack_ext)), hsp3, h3_19.trans h2_19, hwb, htr3.trans htr2⟩
    · intro s3 hpc3 hrun3 hinv3 ⟨hsp3, h3_19, hwb, htr3⟩
      have hwrite := ct1Ack_states_recv_writeback_59e88_ext hAx (relocatable_ekTail376 w.q63 w.w65)
        s0 s3 outA sp2
        (P_rest ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)))
        hinv3 hpc3 hrun3 hsp3 hsp0_align h3_19 htr3
      refine SepWP.mono hwrite ?_
      intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      have htag : sp2.b2.w7 = 11#64 := rfl
      have hnone : sp2.b2.w8 = noneCap := rfl
      rw [htag, hnone, hwb]
      have hout := ct1Ack_noop_out_entails_resultV1RecvAt A (F := F) outA st w (s3.readReg64 .x20) sp2.q200
      refine Entails.trans (Entails.of_eq (show _ =
        P_rest ∗ ((outA ↦₆₄ 11#64) ∗
         words63At (outA + 8#64)
           { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
             q60 := w.q60, w62 := w.w62 } ∗
         ekTail376 w.q63 w.w65 (outA + 512#64) ∗ memRegion (outA + 888#64) 40 ∗
         ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s3.readReg64 .x20) ∗
         ((outA + 944#64) ↦₁₂₈ sp2.q200) ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w))) ∗
        memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX by sep_ac_rfl_ct1Ack_ext)) ?_
      exact sepConj_mono_right (sepConj_mono_left hout)

theorem ct1Ack_still_4468_ret_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (s0 s1 : State) (outA selfA : BitVec 64)
    (outSt : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hinv1 : ImgCallInv img s1)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 4468#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = outA) (hx20 : s1.readReg64 .x20 = (s0.sp - 4240#64) + 1856#64)
    (htr : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        ct1AcknowledgedRecvEkChunkResAt A (F := F) ((s0.sp - 4240#64) + 1856#64) (.ok (.stillReceiving outSt)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 2384#64) 352 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Acknowledged outSt }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  dsimp only [ct1AcknowledgedRecvEkChunkResAt]
  refine SepWP.fold (chunkedCt1AcknowledgedAt_extract66 A (fsp + 1856#64) outSt) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.fold (memRegion_576_376_split_ekTail fsp) (by sep_focus) ?_
  wp_pull_exists; rename_i q576_old w592_old
  refine SepWP.fold (sendEkUnusedAt_split_e40 fsp) (by sep_focus) ?_
  wp_pull_exists; rename_i qe40 we50 qe60
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ⌜w.b0.w0.toNat < 2 ^ 63 ∧ w.b1.w5 = outSt.uc.epoch⌝ ∗
    (words66At (fsp + 1856#64) w ∗ sendEkSpillsAt fsp sp ∗
     ((fsp + 576#64) ↦₁₂₈ q576_old) ∗ ((fsp + 592#64) ↦₆₄ w592_old) ∗
     ((fsp + 3648#64) ↦₁₂₈ qe40) ∗ ((fsp + 3664#64) ↦₆₄ we50) ∗ ((fsp + 3680#64) ↦₁₂₈ qe60) ∗
     (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst outSt) (wordsBytes (words66List w)) ∗
      stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 600#64) 352 ∗
      memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
      ct1AckUnusedRestAt fsp ∗ statesRecvSavedCells s0)) by sep_ac_rfl_ct1Ack_ext)) ?_
  refine SepWP.pure_elim fun ⟨hcap, _⟩ => ?_
  set sp1 := ct1AckSpillsStill4924 sp w
  refine ct1Ack_seq_clean_inImage hinv1
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 4924#64)
    (P_mid := P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst outSt) (wordsBytes (words66List w)) ∗
      stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
      ekTail376 w.q63 w.w65 (fsp + 576#64) ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s2 =>
      s2.sp = fsp ∧ s2.readReg64 .x0 = w.b5.w5 ∧ s2.readReg64 .x1 = w.b0.w0 ∧
      s2.readReg64 .x2 = w.b5.w7 ∧ s2.readReg64 .x3 = w.b2.w9 ∧
      s2.readReg64 .x4 = w.b4.w9 ∧ s2.readReg64 .x5 = w.b4.w8 ∧
      s2.readReg64 .x6 = w.b5.w0 ∧ s2.readReg64 .x7 = w.b1.w9 ∧
      s2.readReg64 .x10 = w.b1.w6 ∧ s2.readReg64 .x11 = w.b5.w4 ∧
      s2.readReg64 .x12 = w.b4.w0 ∧ s2.readReg64 .x13 = w.b5.w1 ∧
      s2.readReg64 .x15 = w.b2.w7 ∧ s2.readReg64 .x16 = w.b4.w7 ∧
      s2.readReg64 .x17 = w.b4.w5 ∧ s2.readReg64 .x18 = w.b5.w3 ∧
      s2.readReg64 .x19 = outA ∧ s2.readReg64 .x22 = w.b5.w2 ∧
      s2.readReg64 .x24 = w.b3.w1 ∧ s2.readReg64 .x25 = w.b3.w9 ∧
      s2.readReg64 .x26 = w.b0.w5 ∧ s2.readReg64 .x30 = w.b5.w9 ∧ TraceCalleeSaved s2 s0)
    ?_ ?_
  · have hstep1 := ct1Ack_step_4468_still_4924 s1 fsp w592_old we50 q576_old qe40 qe60 w sp
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst outSt) (wordsBytes (words66List w)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 600#64) 352 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
       ct1AckUnusedRestAt fsp ∗ statesRecvSavedCells s0)
      hcap hfsp_align hpc hrun hsp hx20
    refine SepWP.mono hstep1 ?_
    intro s2 Pm _ _ ⟨hPm, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
      h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19, h2_22,
      h2_24, h2_25, h2_26, _, h2_30, htr2⟩
    refine ⟨Entails.trans hPm ?_, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
      h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19.trans hx19, h2_22,
      h2_24, h2_25, h2_26, h2_30, htr2.trans htr⟩
    have h880 := words66At_352_entails_memRegion_880 fsp w
    have hunused := ct1AckUnusedRest_entails_sendEkUnusedAt fsp w.q63 w.w65 w.q60
    refine Entails.trans (Entails.of_eq (show _ =
      ((words66At (fsp + 1856#64) w ∗ memRegion (fsp + 2384#64) 352) ∗
       (((fsp + 3648#64) ↦₁₂₈ w.q63) ∗ ((fsp + 3664#64) ↦₆₄ w.w65) ∗
        ((fsp + 3680#64) ↦₁₂₈ w.q60) ∗ ct1AckUnusedRestAt fsp)) ∗
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst outSt) (wordsBytes (words66List w)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
       ekTail376 w.q63 w.w65 (fsp + 576#64) ∗ memRegion (fsp + 976#64) 880 ∗ statesRecvSavedCells s0) by
        dsimp only [ekTail376]; simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]; sep_ac_rfl_ct1Ack_ext)) ?_
    exact Entails.trans (sepConj_mono_left (sepConj_mono h880 hunused)) (Entails.of_eq (by sep_ac_rfl_ct1Ack_ext))
  · intro s2 hpc2 hrun2 hinv2 ⟨hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
      h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19, h2_22,
      h2_24, h2_25, h2_26, h2_30, htr2⟩
    set sp2 := ct1AckSpills4924 s2 sp1
    refine ct1Ack_seq_clean_inImage hinv2
      (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64)
      (P_mid := (P_rest ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst outSt) (wordsBytes (words66List w))) ∗
        memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp2 ∗
        ekTail376 w.q63 w.w65 (fsp + 576#64) ∗ memRegion (fsp + 976#64) 880 ∗
        memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = outA ∧
        writebackWords63 s3 sp2 =
          { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
            q60 := w.q60, w62 := w.w62 } ∧ TraceCalleeSaved s3 s0)
      ?_ ?_
    · have hstep2 := ct1Ack_step_4924_18996 s2 fsp sp1
        (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst outSt) (wordsBytes (words66List w)) ∗
         stackAt fsp statesRecvCalleeStackX ∗ ekTail376 w.q63 w.w65 (fsp + 576#64) ∗
         memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
         sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
        hfsp_align hpc2 hrun2 hsp2
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl_ct1Ack_ext)) (SepWP.mono hstep2 ?_)
      intro s3 Pm _ _ ⟨hPm, hsp3, h3_0, h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7,
        h3_8, h3_9, h3_10, h3_11, h3_12, h3_13, h3_14, h3_15, h3_16, h3_17, h3_19,
        h3_20, h3_21, h3_22, h3_23, h3_24, h3_25, h3_26, h3_27, h3_28, _, h3_30, htr3⟩
      have hwb := writebackWords63_ct1Ack_still s2 s3 sp w
        h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6 h2_7 h2_10 h2_11 h2_12 h2_13
        h2_15 h2_16 h2_17 h2_18 h2_22 h2_24 h2_25 h2_26 h2_30
        h3_0 h3_1 h3_2 h3_3 h3_4 h3_5 h3_6 h3_7 h3_8 h3_9 h3_10 h3_11 h3_12
        h3_13 h3_14 h3_15 h3_16 h3_17 h3_20 h3_21 h3_22 h3_23 h3_24 h3_25
        h3_26 h3_27 h3_28 h3_30
      refine ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl_ct1Ack_ext)), hsp3, h3_19.trans h2_19, hwb, htr3.trans htr2⟩
    · intro s3 hpc3 hrun3 hinv3 ⟨hsp3, h3_19, hwb, htr3⟩
      have hwrite := ct1Ack_states_recv_writeback_59e88_ext hAx (relocatable_ekTail376 w.q63 w.w65)
        s0 s3 outA sp2
        (P_rest ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst outSt) (wordsBytes (words66List w)))
        hinv3 hpc3 hrun3 hsp3 hsp0_align h3_19 htr3
      refine SepWP.mono hwrite ?_
      intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      have htag : sp2.b2.w7 = 11#64 := rfl
      have hnone : sp2.b2.w8 = noneCap := rfl
      rw [htag, hnone, hwb]
      have hout := ct1Ack_noop_out_entails_resultV1RecvAt A (F := F) outA outSt w (s3.readReg64 .x20) sp2.q200
      refine Entails.trans (Entails.of_eq (show _ =
        P_rest ∗ ((outA ↦₆₄ 11#64) ∗
         words63At (outA + 8#64)
           { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
             q60 := w.q60, w62 := w.w62 } ∗
         ekTail376 w.q63 w.w65 (outA + 512#64) ∗ memRegion (outA + 888#64) 40 ∗
         ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s3.readReg64 .x20) ∗
         ((outA + 944#64) ↦₁₂₈ sp2.q200) ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst outSt) (wordsBytes (words66List w))) ∗
        memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX by sep_ac_rfl_ct1Ack_ext)) ?_
      exact sepConj_mono_right (sepConj_mono_left hout)

theorem ct1Ack_done_4468_ret_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hAx : AllocContractsX img A ext)
    (s0 s1 : State) (outA selfA : BitVec 64)
    (outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hinv1 : ImgCallInv img s1)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 4468#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = outA) (hx20 : s1.readReg64 .x20 = (s0.sp - 4240#64) + 1856#64)
    (htr : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      ((P_rest ∗ unchunkedSendCt2RoAt img.base) ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        ct1AcknowledgedRecvEkChunkResAt A (F := F) ((s0.sp - 4240#64) + 1856#64) (.ok (.done outSt)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 2384#64) 352 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ (P_rest ∗ unchunkedSendCt2RoAt img.base) ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct2Sampled outSt }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine SepWP.fold (ct1Ack_done_1856_split (A := A) (F := F) fsp outSt) (by sep_focus) ?_
  wp_pull_exists; rename_i w d58 d59 dq60 dw62 dq63 dw65
  refine SepWP.fold (sendEkUnusedAt_split_e40 fsp) (by sep_focus) ?_
  wp_pull_exists; rename_i qe40 we50 qe60
  set sp1 := ct1AckSpillsDone4924 sp w d58 d59 dw62
  refine ct1Ack_seq_clean_inImage hinv1
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 4924#64)
    (P_mid := (P_rest ∗ unchunkedSendCt2RoAt img.base) ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)) ∗
      stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
      memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s2 =>
      s2.sp = fsp ∧ s2.readReg64 .x0 = w.w55 ∧ s2.readReg64 .x1 = w.b0.w0 ∧
      s2.readReg64 .x2 = w.b1.w2 ∧ s2.readReg64 .x3 = w.b2.w9 ∧
      s2.readReg64 .x4 = w.b4.w9 ∧ s2.readReg64 .x5 = w.b4.w8 ∧
      s2.readReg64 .x6 = w.w50 ∧ s2.readReg64 .x7 = w.b1.w9 ∧
      s2.readReg64 .x10 = w.b1.w6 ∧ s2.readReg64 .x11 = w.w54 ∧
      s2.readReg64 .x12 = w.b4.w0 ∧ s2.readReg64 .x13 = w.w51 ∧
      s2.readReg64 .x15 = w.b2.w7 ∧ s2.readReg64 .x16 = w.b4.w7 ∧
      s2.readReg64 .x17 = w.b4.w5 ∧ s2.readReg64 .x18 = w.w53 ∧
      s2.readReg64 .x19 = outA ∧ s2.readReg64 .x22 = w.w52 ∧
      s2.readReg64 .x24 = w.b3.w1 ∧ s2.readReg64 .x25 = w.b3.w9 ∧
      s2.readReg64 .x26 = w.b0.w5 ∧ s2.readReg64 .x30 = w.b3.w8 ∧ TraceCalleeSaved s2 s0)
    ?_ ?_
  · have hstep1 := ct1Ack_step_4468_done_4924 hb s1 fsp d58 d59 dw62 dw65 we50
      dq60 dq63 qe40 qe60 w sp
      (P_rest ∗ ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
       memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
       ct1AckUnusedRestAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp hx20
    refine SepWP.weaken_pre (Entails.of_eq ?_) (SepWP.mono hstep1 ?_)
    · dsimp only [unchunkedSendCt2RoAt]; sep_ac_rfl_ct1Ack_ext
    · intro s2 Pm _ _ ⟨hPm, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
        h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19, h2_22,
        h2_24, h2_25, h2_26, _, h2_30, htr2⟩
      refine ⟨Entails.trans hPm ?_, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
        h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19.trans hx19, h2_22,
        h2_24, h2_25, h2_26, h2_30, htr2.trans htr⟩
      have h880 := ct1Ack_done_1856_rejoin_880 fsp d58 d59 dw62 dw65 dq60 dq63 w
      have hunused := ct1AckUnusedRest_entails_sendEkUnusedAt fsp dq63 dw65 dq60
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 1856#64) ↦₆₄ noneCap) ∗ words57At (fsp + 1864#64) w ∗
         ((fsp + 2320#64) ↦₆₄ d58) ∗ ((fsp + 2328#64) ↦₆₄ d59) ∗
         ((fsp + 2336#64) ↦₁₂₈ dq60) ∗ ((fsp + 2352#64) ↦₆₄ dw62) ∗
         ((fsp + 2360#64) ↦₁₂₈ dq63) ∗ ((fsp + 2376#64) ↦₆₄ dw65) ∗ memRegion (fsp + 2384#64) 352) ∗
        (((fsp + 3648#64) ↦₁₂₈ dq63) ∗ ((fsp + 3664#64) ↦₆₄ dw65) ∗
         ((fsp + 3680#64) ↦₁₂₈ dq60) ∗ ct1AckUnusedRestAt fsp) ∗
        ((P_rest ∗ unchunkedSendCt2RoAt img.base) ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)) ∗
         stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
         memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗ statesRecvSavedCells s0) by
          dsimp only [unchunkedSendCt2RoAt]; sep_ac_rfl_ct1Ack_ext)) ?_
      exact Entails.trans (sepConj_mono h880 (sepConj_mono_left hunused))
        (Entails.of_eq (by sep_ac_rfl_ct1Ack_ext))
  · intro s2 hpc2 hrun2 hinv2 ⟨hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
      h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19, h2_22,
      h2_24, h2_25, h2_26, h2_30, htr2⟩
    set sp2 := ct1AckSpills4924 s2 sp1
    refine ct1Ack_seq_clean_inImage hinv2
      (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64)
      (P_mid := ((P_rest ∗ unchunkedSendCt2RoAt img.base) ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w))) ∗
        memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp2 ∗
        memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
        memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = outA ∧
        writebackWords63 s3 sp2 =
          { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4,
            b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56, w.b1.w2, d58, w.b3.w8⟩,
            q60 := sp.q3c0, w62 := dw62 } ∧ TraceCalleeSaved s3 s0)
      ?_ ?_
    · have hstep2 := ct1Ack_step_4924_18996 s2 fsp sp1
        ((P_rest ∗ unchunkedSendCt2RoAt img.base) ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)) ∗
         stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
         memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
         sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
        hfsp_align hpc2 hrun2 hsp2
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl_ct1Ack_ext)) (SepWP.mono hstep2 ?_)
      intro s3 Pm _ _ ⟨hPm, hsp3, h3_0, h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7,
        h3_8, h3_9, h3_10, h3_11, h3_12, h3_13, h3_14, h3_15, h3_16, h3_17, h3_19,
        h3_20, h3_21, h3_22, h3_23, h3_24, h3_25, h3_26, h3_27, h3_28, _, h3_30, htr3⟩
      have hwb := writebackWords63_ct1Ack_done s2 s3 sp w d58 d59 dw62
        h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6 h2_7 h2_10 h2_11 h2_12 h2_13
        h2_15 h2_16 h2_17 h2_18 h2_22 h2_24 h2_25 h2_26 h2_30
        h3_0 h3_1 h3_2 h3_3 h3_4 h3_5 h3_6 h3_7 h3_8 h3_9 h3_10 h3_11 h3_12
        h3_13 h3_14 h3_15 h3_16 h3_17 h3_20 h3_21 h3_22 h3_23 h3_24 h3_25
        h3_26 h3_27 h3_28 h3_30
      refine ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl_ct1Ack_ext)), hsp3, h3_19.trans h2_19, hwb, htr3.trans htr2⟩
    · intro s3 hpc3 hrun3 hinv3 ⟨hsp3, h3_19, hwb, htr3⟩
      have hwrite := ct1Ack_states_recv_writeback_59e88_ext hAx (Relocatable.of_memRegion 376)
        s0 s3 outA sp2
        ((P_rest ∗ unchunkedSendCt2RoAt img.base) ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)))
        hinv3 hpc3 hrun3 hsp3 hsp0_align h3_19 htr3
      refine SepWP.mono hwrite ?_
      intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      have htag : sp2.b2.w7 = 12#64 := rfl
      have hnone : sp2.b2.w8 = noneCap := rfl
      rw [htag, hnone, hwb]
      have hout := ek_ack_out_entails_resultV1RecvAt A (F := F) outA outSt w
        w.b1.w2 d58 w.b3.w8 sp.q3c0 dw62 (s3.readReg64 .x20) sp2.q200
      refine Entails.trans (Entails.of_eq (show _ =
        (P_rest ∗ unchunkedSendCt2RoAt img.base) ∗ ((outA ↦₆₄ 12#64) ∗
         words63At (outA + 8#64)
           { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4,
             b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56, w.b1.w2, d58, w.b3.w8⟩,
             q60 := sp.q3c0, w62 := dw62 } ∗
         memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ∗
         ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s3.readReg64 .x20) ∗
         ((outA + 944#64) ↦₁₂₈ sp2.q200) ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w))) ∗
        memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX by sep_ac_rfl_ct1Ack_ext)) ?_
      exact Entails.trans (sepConj_mono_right (sepConj_mono_left hout)) (Entails.of_eq (by sep_ac_rfl_ct1Ack_ext))

end CryptoVerification.SpqrV1.States.Recv
