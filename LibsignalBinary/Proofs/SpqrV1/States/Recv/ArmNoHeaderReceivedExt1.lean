/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceived1
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.noHeaderReceived` Arm (`AllocContractsX`, Part 1)

**Checked by Lean.** Lifts the `memcpy`, shared `Ok(V1Recv)` writeback (`+18996`), and
`msg.epoch > st.uc.epoch` deallocation/drop helpers for `.noHeaderReceived` to
`AllocContractsX img A ext` (`extHookStack = 16384` B, `.inImage img`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout

theorem nhr_stackAt_statesRecvCallee_eq_extHook (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 3168 ∗ stackAt fsp extHookStack :=
  ProofLib.stackAt_split_bottom fsp extHookStack 3168 (by decide)

theorem nhr_stackAt_statesRecvCallee_eq_dropStack32X (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 3136 ∗ stackAt fsp dropStack32X :=
  ProofLib.stackAt_split_bottom fsp dropStack32X 3136 (by decide)

local elab "sep_ac_rfl_nhr_ext" : tactic => do
  let g ← _root_.Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← _root_.Lean.instantiateMVars (← g.getType)).consumeMData
    let some (_, lhs, rhs) := ty.eq?
      | _root_.Lean.throwError "sep_ac_rfl_nhr_ext: expected equality"
    if lhs == rhs then
      g.assign (← _root_.Lean.Meta.mkEqRefl lhs)
      _root_.Lean.Elab.Tactic.replaceMainGoal []
    else if let some (tbl, tA, tB) := ProofLib.SepSolver.synReifyPermTbl? lhs rhs then
      g.assign (← ProofLib.SepSolver.eqACOfTbl lhs rhs tbl tA tB)
      _root_.Lean.Elab.Tactic.replaceMainGoal []
    else
      _root_.Lean.Elab.Tactic.evalTactic (← `(tactic| sep_frame))

private theorem sepWP_weaken_mono_nhr_ext {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post post' : State → SepProp → Prop}
    (h : SepWP prog target_pc s P' post')
    (hpost : ∀ sf Pf, sf.pc = target_pc → sf.status = .Running → post' sf Pf → post sf Pf)
    (hP : P = P' := by sep_ac_rfl_nhr_ext) :
    SepWP prog target_pc s P post :=
  hP ▸ SepWP.mono h hpost

theorem nhr_memcpy_ok_at_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName :=
      by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (session2MemcpySpecX.inImage img) :=
  memcpy_ok_at2_ext_x hA (name := name) (k := k) hk

theorem nhr_call_memcpy_relocate_cs_inImage_stk {img : Obj.Image} {prog : Program}
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
    rw [hsplit, hstk_split]; sep_ac_rfl_nhr_ext
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
    exact ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl_nhr_ext)) hm⟩
  · dsimp only [Spec.inImage, session2MemcpySpecX]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    have hcomm :
        ((dst ↦ₛ bs) ∗ ((src ↦ₛ bs) ∗ stackAt sp_call extHookStack)) ∗
          (relocatedHeap F bs ∗ memRegion (sp_call - BitVec.ofNat 64 stk) k_stk ∗ Frame) =
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗
          (relocatedHeap F bs ∗ (stackAt sp_call stk ∗ Frame)) := by
      rw [hstk_split]; sep_ac_rfl_nhr_ext
    rw [hcomm]
    refine SepWP.fold (Leaves.relocate_post_entails dst src hlen (stackAt sp_call stk ∗ Frame))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp, show (F dst ∗ memRegion src n) ∗ (stackAt sp_call stk ∗ Frame) =
        (F dst ∗ memRegion src n ∗ stackAt sp_call stk) ∗ Frame by sep_ac_rfl_nhr_ext]
    exact SepWP.done hpc_sf hrun_sf fun hinv_sf =>
      hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
        ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hinv_sf

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48

set_option maxHeartbeats 1200000 in
private theorem nhr_states_recv_writeback_59e88_step {img : Obj.Image} {A : RustAlloc}
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
  have hmemcpy_raw := nhr_memcpy_ok_at_ext hA statesRecvName
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
  refine nhr_call_memcpy_relocate_cs_inImage_stk (ret_pc := entry + 19284#64) (sp_call := sp0 - 4240#64)
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
    simp only [pointsTo128_eq_pair64_recv, arm64_norm]; sep_ac_rfl_nhr_ext
  · refine sepWP_weaken_mono_nhr_ext
      (hepilogue _ (P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 s sp) ∗
        F_tail (outA + 512#64) ∗ memRegion (outA + 888#64) 40 ∗ ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗
        ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗ ((outA + 944#64) ↦₁₂₈ sp.q200))
        rfl hrun1 hsp1 hsp_align htr1)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl_nhr_ext)), hsp_sf, hcs_sf, htr_sf⟩)

theorem nhr_states_recv_writeback_59e88_ext {img : Obj.Image} {A : RustAlloc}
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
    (nhr_states_recv_writeback_59e88_step hA hrel s0 s outA sp P_rest
      hpc hrun hsp hsp_align hx19 htr)

theorem nhr_seq_clean_inImage {prog : Program} {img : Obj.Image} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → ImgCallInv img sm → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  SepWP.seq_inImage hinv
    (SepWP.mono h1 fun sm Pm hpcm hrunm ⟨hPm, hQ⟩ hinv_m =>
      SepWP.weaken_pre hPm (h2 sm hpcm hrunm hinv_m hQ))

theorem nhr_sepWPp_seq_clean_inImage {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {Q_ok Q_pan : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → ImgCallInv img sm → Q sm →
      SepWPp prog ret sm P_mid Q_ok Q_pan) :
    SepWPp prog ret s P Q_ok Q_pan :=
  CryptoVerification.SepWPp.of_sepWP_frozen hinv.1 hinv.2
    (SepWP.mono h1 fun sm Pm hpcm hrunm ⟨hPm, hQ⟩ hF hsym =>
      SepWPp.weaken_pre hPm (h2 sm hpcm hrunm ⟨hF, hsym⟩ hQ))

theorem nhr_call_memcpy_words57_ext {img : Obj.Image} {prog : Program}
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (session2MemcpySpecX.inImage img))
    (dst src : BitVec 64) (w : Words57)
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
    (hx2 : (s.readReg64 Reg.x2).toNat = 456)
    (hsplit : P = (memRegion dst 456 ∗ words57At src w ∗ stackAt sp_call statesRecvCalleeStackX) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace → ImgCallInv img sf →
      SepWP prog target_pc sf
        ((words57At dst w ∗ words57At src w ∗ stackAt sp_call statesRecvCalleeStackX) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  apply SepWP.seq_inImage (mid := ret_pc) hin
  have hsplit' : P =
      (memRegion dst 456 ∗ (src ↦ₛ wordsBytes (words57List w)) ∗ stackAt sp_call extHookStack) ∗
        (memRegion (sp_call - 19552#64) 3168 ∗ Frame) := by
    rw [hsplit, nhr_stackAt_statesRecvCallee_eq_extHook sp_call, words57At_eq_pointsToBytes src w]
    sep_ac_rfl_nhr_ext
  rw [hsplit']
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, wordsBytes (words57List w)))
    (F := memRegion (sp_call - 19552#64) 3168 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [Spec.inImage, session2MemcpySpecX]
    rw [hsp, length_wordsBytes_words57List, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hin.1, hin.2⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl_nhr_ext)) hm⟩
  · dsimp only [Spec.inImage, session2MemcpySpecX]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    have hpost_eq :
        ((dst ↦ₛ wordsBytes (words57List w)) ∗
          ((src ↦ₛ wordsBytes (words57List w)) ∗ stackAt sp_call extHookStack)) ∗
          (memRegion (sp_call - 19552#64) 3168 ∗ Frame) =
        (words57At dst w ∗ words57At src w ∗ stackAt sp_call statesRecvCalleeStackX) ∗ Frame := by
      rw [nhr_stackAt_statesRecvCallee_eq_extHook sp_call,
          words57At_eq_pointsToBytes dst w, words57At_eq_pointsToBytes src w]
      sep_ac_rfl_nhr_ext
    rw [hpost_eq]
    exact SepWP.done hpc_sf hrun_sf fun hinv_sf =>
      hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hinv_sf

set_option maxHeartbeats 800000 in
theorem nhr_step_2132_2180_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s : State) (fsp out st_ptr msg_ptr msg_ep w62_old : BitVec 64)
    (w : Words57) (Frame : SepProp)
    (hinv : ImgCallInv img s)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 2132#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = st_ptr) (hx19 : s.readReg64 .x19 = out) (hx24 : s.readReg64 .x24 = msg_ptr) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 2180#64) s
      (memRegion (fsp + 2752#64) 456 ∗ words57At (st_ptr + 8#64) w ∗
       (msg_ptr ↦₆₄ msg_ep) ∗ ((fsp + 504#64) ↦₆₄ w62_old) ∗
       stackAt fsp statesRecvCalleeStackX ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          words57At (fsp + 2752#64) w ∗ words57At (st_ptr + 8#64) w ∗
          (msg_ptr ↦₆₄ msg_ep) ∗ ((fsp + 504#64) ↦₆₄ w.b0.w6) ∗
          stackAt fsp statesRecvCalleeStackX ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = msg_ep ∧
        sm.readReg64 .x21 = st_ptr ∧
        sm.readReg64 .x24 = msg_ptr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x8 = BitVec.zeroExtend 64 (ekCmpW8 (subsPState64 msg_ep w.b0.w6)) ∧
        sm.pstate.z = (ekCmpW8 (subsPState64 msg_ep w.b0.w6) == 0#32) ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx1 hx19 hx24
  have hmemcpy_raw := nhr_memcpy_ok_at_ext hA statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
  apply SepWP.seq_inImage
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName +
      bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) hinv
  states_recv_fetches_range img.base (Rust.withPanics ext) 2132 48
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done rfl (by simp only [arm64_norm, wp_norm]; exact hrun) fun hinv_call => ?_
  refine nhr_call_memcpy_words57_ext (s0 := s) (ret_pc := entry + 2152#64) (sp_call := s.sp)
    hmemcpy_raw (s.sp + 2752#64) (s.readReg64 .x1 + 8#64) w
    hinv_call rfl (by simp only [arm64_norm, wp_norm]; exact hrun)
    (by simp only [arm64_norm, wp_norm]) hfsp_align rfl
    (by simp only [arm64_norm, wp_norm]) rfl rfl rfl (by sep_ac_rfl_nhr_ext) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1 _hinv1
  have hx19_1 : sf1.readReg64 .x19 = s.readReg64 .x19 :=
    hcs1.1.trans (by simp only [arm64_norm, wp_norm])
  have hx21_1 : sf1.readReg64 .x21 = s.readReg64 .x1 :=
    hcs1.2.2.1.trans (by simp only [arm64_norm, wp_norm])
  have hx24_1 : sf1.readReg64 .x24 = s.readReg64 .x24 :=
    hcs1.2.2.2.2.2.1.trans (by simp only [arm64_norm, wp_norm])
  have hx29_1 : sf1.readReg64 .x29 = s.readReg64 .x29 :=
    hcs1.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, wp_norm])
  wp_simp_pre [words57At, words10At, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [words57At, words10At, ekCmpW8, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_done

set_option maxHeartbeats 800000 in
theorem nhr_step_8568_hdr_8612_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s : State) (fsp out st_ptr msg_ptr msg_ep : BitVec 64)
    (chunk : Chunk) (w : Words57) (Frame : SepProp)
    (hinv : ImgCallInv img s)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 8568#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = msg_ep)
    (hx21 : s.readReg64 .x21 = st_ptr) (hx24 : s.readReg64 .x24 = msg_ptr) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 8612#64) s
      (memRegion (fsp + 976#64) 456 ∗ words57At (st_ptr + 8#64) w ∗
       messagePayloadAt spqrPolyApi msg_ptr (.hdr chunk) ∗
       stackAt fsp statesRecvCalleeStackX ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          words57At (fsp + 976#64) w ∗ words57At (st_ptr + 8#64) w ∗
          messagePayloadAt spqrPolyApi msg_ptr (.hdr chunk) ∗
          stackAt fsp statesRecvCalleeStackX ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1856#64 ∧
        sm.readReg64 .x1 = fsp + 976#64 ∧
        sm.readReg64 .x2 = msg_ep ∧
        sm.readReg64 .x3 = msg_ptr + 10#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = msg_ep ∧
        sm.readReg64 .x21 = st_ptr ∧
        sm.readReg64 .x24 = msg_ptr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19 hx20 hx21 hx24
  have hmemcpy_raw := nhr_memcpy_ok_at_ext hA statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
  apply SepWP.seq_inImage
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName +
      bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) hinv
  states_recv_fetches_range img.base (Rust.withPanics ext) 8568 44
  dsimp only [tripleRatchetProgAtExt, statesRecvName, messagePayloadAt, BitVec.ofNat_eq_ofNat]
    at hmemcpy_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_simp_pre [sepConj_assoc]
  wp_steps
  refine SepWP.done rfl (by simp only [arm64_norm, wp_norm]; exact hrun) fun hinv_call => ?_
  refine nhr_call_memcpy_words57_ext (s0 := s) (ret_pc := entry + 8596#64) (sp_call := s.sp)
    hmemcpy_raw (s.sp + 976#64) (s.readReg64 .x21 + 8#64) w
    hinv_call rfl (by simp only [arm64_norm, wp_norm]; exact hrun)
    (by simp only [arm64_norm, wp_norm]) hfsp_align rfl
    (by simp only [arm64_norm, wp_norm]) rfl rfl rfl (by sep_focus) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1 _hinv1
  have hx19_1 : sf1.readReg64 .x19 = s.readReg64 .x19 :=
    hcs1.1.trans (by simp only [arm64_norm, wp_norm])
  have hx20_1 : sf1.readReg64 .x20 = s.readReg64 .x20 :=
    hcs1.2.1.trans (by simp only [arm64_norm, wp_norm])
  have hx21_1 : sf1.readReg64 .x21 = s.readReg64 .x21 :=
    hcs1.2.2.1.trans (by simp only [arm64_norm, wp_norm])
  have hx24_1 : sf1.readReg64 .x24 = s.readReg64 .x24 :=
    hcs1.2.2.2.2.2.1.trans (by simp only [arm64_norm, wp_norm])
  have hx29_1 : sf1.readReg64 .x29 = s.readReg64 .x29 :=
    hcs1.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, wp_norm])
  wp_steps
  simp only [sepConj_assoc]
  wp_done

theorem nhr_8984_ret_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s0 s1 : State) (outA : BitVec 64) (sp1 : SendEkSpills) (w63 : Words63)
    (P_rest Q_out : SepProp) (hinv1 : ImgCallInv img s1) (hsp0_align : s0.spAligned = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 8984#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = outA) (htr1 : TraceCalleeSaved s1 s0)
    (hw63 : writebackAt8984 s1 sp1 = w63)
    (hout : ∀ (w936 : BitVec 64) (q944 : BitVec 128),
      P_rest ∗ (outA ↦₆₄ sp1.b2.w7) ∗ words63At (outA + 8#64) w63 ∗
        memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ∗
        ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944) ∗
        stackAt s0.sp statesRecvStackX ⊢ Q_out) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      (P_rest ∗ memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ Q_out) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine nhr_seq_clean_inImage hinv1
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64)
    (P_mid := P_rest ∗ memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
      sendEkSpillsAt fsp (nhrSpills8984 s1 sp1) ∗
      memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s2 =>
      s2.sp = fsp ∧ s2.readReg64 .x19 = outA ∧
      writebackWords63 s2 (nhrSpills8984 s1 sp1) = w63 ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · have hstep := nhr_step_8984_18996 s1 fsp sp1
      (P_rest ∗ memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
       memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc1 hrun1 hsp1
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl_nhr_ext)) (SepWP.mono hstep ?_)
    intro s2 Pm _ _ ⟨hPm, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7, h2_8, h2_9,
      h2_10, h2_11, h2_12, h2_13, h2_14, h2_15, h2_16, h2_17, h2_19, h2_20, h2_21, h2_22,
      h2_23, h2_24, h2_25, h2_26, h2_27, h2_28, _, h2_30, htr2⟩
    have hwb := (writebackWords63_at_8984 s1 s2 sp1
      h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6 h2_7 h2_8 h2_9 h2_10 h2_11 h2_12 h2_13 h2_14 h2_15 h2_16 h2_17
      h2_20 h2_21 h2_22 h2_23 h2_24 h2_25 h2_26 h2_27 h2_28 h2_30).trans hw63
    exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl_nhr_ext)), hsp2, h2_19.trans hx19, hwb, htr2.trans htr1⟩
  · intro s2 hpc2 hrun2 hinv2 ⟨hsp2, h2_19, hwb, htr2⟩
    have hwrite := nhr_states_recv_writeback_59e88_ext hA (Relocatable.of_memRegion 376)
      s0 s2 outA (nhrSpills8984 s1 sp1) P_rest
      hinv2 hpc2 hrun2 hsp2 hsp0_align h2_19 htr2
    refine SepWP.mono hwrite ?_
    intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
    refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
    have htag : (nhrSpills8984 s1 sp1).b2.w7 = sp1.b2.w7 := rfl
    have hnone : (nhrSpills8984 s1 sp1).b2.w8 = noneCap := rfl
    rw [htag, hnone, hwb]
    exact hout (s2.readReg64 .x20) (nhrSpills8984 s1 sp1).q200

theorem nhr_noop_8664_ret_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s0 s : State) (outA selfA : BitVec 64)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (w : Words57) (sp : SendEkSpills) (P_rest : SepProp)
    (hinv : ImgCallInv img s) (hsp0_align : s0.spAligned = true) (hw62 : sp.w62 = w.b0.w6)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 8664#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64)
    (hx19 : s.readReg64 .x19 = outA) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        words57At ((s0.sp - 4240#64) + 2752#64) w ∗
        nhrUnusedRestAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .noHeaderReceived st }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine nhr_seq_clean_inImage hinv
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 8984#64)
    (P_mid := (P_rest ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w))) ∗
      memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
      sendEkSpillsAt fsp (nhrSpills8664 sp w) ∗
      memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s1 =>
      s1.sp = fsp ∧ s1.readReg64 .x19 = outA ∧
      writebackAt8984 s1 (nhrSpills8664 sp w) =
        { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4
          b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56,
                 sp.b1.w0, sp.b3.w0, sp.b1.w7⟩
          q60 := sp.q3c0, w62 := sp.b3.w1 } ∧
      TraceCalleeSaved s1 s0)
    ?_ ?_
  · have hstep1 := nhr_step_8664_8984 s fsp w sp
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
       nhrUnusedRestAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl_nhr_ext)) (SepWP.mono hstep1 ?_)
    intro s1 Pm _ _ ⟨hPm, hsp1, h1_0, h1_1, h1_2, h1_3, h1_4, h1_5, h1_6, h1_7,
      h1_9, h1_10, h1_11, h1_12, h1_13, h1_14, h1_15, h1_16, h1_17, h1_18, h1_19,
      h1_20, h1_22, h1_23, h1_24, h1_25, h1_26, h1_27, h1_28, _, h1_30, htr1⟩
    have hwb := writebackAt8984_nhr_noop s1 sp w hw62
      h1_0 h1_1 h1_2 h1_3 h1_4 h1_5 h1_6 h1_7 h1_9 h1_10 h1_11 h1_12 h1_13 h1_14 h1_15 h1_16 h1_17 h1_18
      h1_20 h1_22 h1_23 h1_24 h1_25 h1_26 h1_27 h1_28 h1_30
    refine ⟨Entails.trans hPm ?_, hsp1, h1_19.trans hx19, hwb, htr1.trans htr⟩
    have hunused := words57At_nhrUnusedRest_entails_sendEkUnusedAt fsp w
    refine Entails.trans (Entails.of_eq (show _ =
      (words57At (fsp + 2752#64) w ∗ nhrUnusedRestAt fsp) ∗
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp (nhrSpills8664 sp w) ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
       memRegion (fsp + 1856#64) 880 ∗ statesRecvSavedCells s0) by sep_ac_rfl_nhr_ext)) ?_
    exact Entails.trans (sepConj_mono_left hunused) (Entails.of_eq (by sep_ac_rfl_nhr_ext))
  · intro s1 hpc1 hrun1 hinv1 ⟨hsp1, h1_19, hwb, htr1⟩
    refine nhr_8984_ret_ext hA s0 s1 outA (nhrSpills8664 sp w) _
      (P_rest ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)))
      _ hinv1 hsp0_align hpc1 hrun1 hsp1 h1_19 htr1 hwb ?_
    intro w936 q944
    have htag : (nhrSpills8664 sp w).b2.w7 = 7#64 := rfl
    rw [htag]
    have hout := nhr_stillReceiving_out_entails_resultV1RecvAt A (F := F) outA st w
      sp.b1.w0 sp.b3.w0 sp.b1.w7 sp.q3c0 sp.b3.w1 w936 q944
    refine Entails.trans (Entails.of_eq (show _ =
      P_rest ∗
      ((outA ↦₆₄ 7#64) ∗
       words63At (outA + 8#64)
         { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4
           b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56,
                  sp.b1.w0, sp.b3.w0, sp.b1.w7⟩
           q60 := sp.q3c0, w62 := sp.b3.w1 } ∗
       memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ∗
       ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944) ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w))) ∗
      memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX by sep_ac_rfl_nhr_ext)) ?_
    exact sepConj_mono_right (sepConj_mono_left hout)

theorem nhr_still_15296_ret_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s0 s1 : State) (outA selfA : BitVec 64)
    (outSt : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (w_out : Words57) (sp sp1 : SendEkSpills) (P_rest : SepProp)
    (hinv1 : ImgCallInv img s1) (hsp0_align : s0.spAligned = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 15296#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = outA)
    (hps1 : s1.pstate = addsPState64 noneCap 1#64)
    (htr1 : TraceCalleeSaved s1 s0)
    (hwb1 : writebackStillAt15296 s1 sp1 =
      { b0 := w_out.b0, b1 := w_out.b1, b2 := w_out.b2, b3 := w_out.b3, b4 := w_out.b4
        b5 := ⟨w_out.w50, w_out.w51, w_out.w52, w_out.w53, w_out.w54, w_out.w55, w_out.w56,
               sp.b1.w0, sp.b3.w0, sp.b1.w7⟩
        q60 := sp.q3c0, w62 := sp.b3.w1 }) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .noHeaderReceived outSt }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine nhr_seq_clean_inImage hinv1
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 8984#64)
    (P_mid := (P_rest ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out))) ∗
      memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
      sendEkSpillsAt fsp (nhrSpillsStill8984 s1 sp1) ∗
      memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = outA ∧
      writebackAt8984 s2 (nhrSpillsStill8984 s1 sp1) =
        { b0 := w_out.b0, b1 := w_out.b1, b2 := w_out.b2, b3 := w_out.b3, b4 := w_out.b4
          b5 := ⟨w_out.w50, w_out.w51, w_out.w52, w_out.w53, w_out.w54, w_out.w55, w_out.w56,
                 sp.b1.w0, sp.b3.w0, sp.b1.w7⟩, q60 := sp.q3c0, w62 := sp.b3.w1 } ∧ TraceCalleeSaved s2 s0) ?_ ?_
  · have hstep2 := nhr_step_15296_still_8984 s1 fsp sp1
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
       memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc1 hrun1 hsp1 hps1
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl_nhr_ext)) (SepWP.mono hstep2 ?_)
    intro s2 Pm _ _ ⟨hPm, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
      h2_8, h2_9, h2_10, h2_11, h2_12, h2_13, h2_14, h2_15, h2_16, h2_17, h2_18, h2_19,
      h2_20, h2_21, h2_22, h2_23, h2_24, h2_25, h2_26, h2_27, h2_28, _, h2_30, htr2⟩
    have hwb := (writebackAt8984_of_still15296 s1 s2 sp1
      h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6 h2_7 h2_8 h2_9 h2_10 h2_11 h2_12 h2_13 h2_14 h2_15 h2_16 h2_17 h2_18
      h2_20 h2_21 h2_22 h2_23 h2_24 h2_25 h2_26 h2_27 h2_28 h2_30).trans hwb1
    exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl_nhr_ext)), hsp2, h2_19.trans hx19, hwb, htr2.trans htr1⟩
  · intro s2 hpc2 hrun2 hinv2 ⟨hsp2, h2_19, hwb, htr2⟩
    refine nhr_8984_ret_ext hA s0 s2 outA (nhrSpillsStill8984 s1 sp1) _
      (P_rest ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out)))
      _ hinv2 hsp0_align hpc2 hrun2 hsp2 h2_19 htr2 hwb (fun w936 q944 => ?_)
    have htag : (nhrSpillsStill8984 s1 sp1).b2.w7 = 7#64 := rfl
    rw [htag]
    have hout := nhr_stillReceiving_out_entails_resultV1RecvAt A (F := F) outA outSt w_out
      sp.b1.w0 sp.b3.w0 sp.b1.w7 sp.q3c0 sp.b3.w1 w936 q944
    refine Entails.trans (Entails.of_eq (show _ = P_rest ∗
      ((outA ↦₆₄ 7#64) ∗ words63At (outA + 8#64)
         { b0 := w_out.b0, b1 := w_out.b1, b2 := w_out.b2, b3 := w_out.b3, b4 := w_out.b4
           b5 := ⟨w_out.w50, w_out.w51, w_out.w52, w_out.w53, w_out.w54, w_out.w55, w_out.w56,
                  sp.b1.w0, sp.b3.w0, sp.b1.w7⟩, q60 := sp.q3c0, w62 := sp.b3.w1 } ∗
       memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ∗
       ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944) ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out))) ∗
      memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX by sep_ac_rfl_nhr_ext)) ?_
    exact sepConj_mono_right (sepConj_mono_left hout)

theorem nhr_still_8616_ret_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s0 s : State) (outA selfA w58 w59 : BitVec 64)
    (outSt : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (w_out : Words57) (sp : SendEkSpills) (P_rest : SepProp)
    (hinv : ImgCallInv img s) (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 8616#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64)
    (hx19 : s.readReg64 .x19 = outA) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        words60At ((s0.sp - 4240#64) + 1856#64) (mkWords60_still w_out w58 w59) ∗
        memRegion ((s0.sp - 4240#64) + 2336#64) 400 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .noHeaderReceived outSt }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  set w60 := mkWords60_still w_out w58 w59
  refine nhr_seq_clean_inImage hinv
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 15296#64)
    (P_mid := P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out)) ∗
      stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp (nhrSpills15296 sp w60) ∗
      memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = outA ∧ s1.pstate = addsPState64 noneCap 1#64 ∧
      writebackStillAt15296 s1 (nhrSpills15296 sp w60) =
        { b0 := w_out.b0, b1 := w_out.b1, b2 := w_out.b2, b3 := w_out.b3, b4 := w_out.b4
          b5 := ⟨w_out.w50, w_out.w51, w_out.w52, w_out.w53, w_out.w54, w_out.w55, w_out.w56,
                 sp.b1.w0, sp.b3.w0, sp.b1.w7⟩, q60 := sp.q3c0, w62 := sp.b3.w1 } ∧ TraceCalleeSaved s1 s0) ?_ ?_
  · have hstep1 := nhr_step_8616_ok_15296 s fsp w60 sp
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2336#64) 400 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align (show noneCap ≠ 0xfffffffffffffffe#64 by decide) hpc hrun hsp
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl_nhr_ext)) (SepWP.mono hstep1 ?_)
    intro s1 Pm _ _ ⟨hPm, hsp1, h1_0, h1_1, h1_2, h1_4, h1_5, h1_6, h1_7, h1_8,
      h1_9, h1_10, h1_11, h1_12, h1_13, h1_14, h1_15, h1_16, h1_17, h1_18, h1_19,
      h1_20, h1_21, h1_22, h1_23, _, _, h1_26, h1_27, _, _, h1_30, hps1, htr1⟩
    have hwb1 := writebackStillAt15296_of_8616 s1 sp w_out w58 w59
      h1_0 h1_1 h1_2 h1_4 h1_5 h1_6 h1_7 h1_8 h1_9 h1_10 h1_11 h1_12 h1_13 h1_14 h1_15 h1_16 h1_17 h1_18
      h1_20 h1_21 h1_22 h1_23 h1_26 h1_27 h1_30
    refine ⟨Entails.trans hPm ?_, hsp1, h1_19.trans hx19, hps1, hwb1, htr1.trans htr⟩
    have h880 := words60At_1856_400_entails_memRegion_880 fsp w60
    refine Entails.trans (Entails.of_eq (show _ =
      (words60At (fsp + 1856#64) w60 ∗ memRegion (fsp + 2336#64) 400) ∗
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp (nhrSpills15296 sp w60) ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by sep_ac_rfl_nhr_ext)) ?_
    exact Entails.trans (sepConj_mono_left h880) (Entails.of_eq (by sep_ac_rfl_nhr_ext))
  · intro s1 hpc1 hrun1 hinv1 ⟨hsp1, h1_19, hps1, hwb1, htr1⟩
    exact nhr_still_15296_ret_ext hA s0 s1 outA selfA outSt w_out sp (nhrSpills15296 sp w60) P_rest
      hinv1 hsp0_align hpc1 hrun1 hsp1 h1_19 hps1 htr1 hwb1

theorem nhr_done_15296_ret_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContractsX img A ext)
    (s0 s1 : State) (outA selfA : BitVec 64)
    (outSt : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (w_out : Words60) (sp sp1 : SendEkSpills) (P_rest : SepProp)
    (hinv1 : ImgCallInv img s1) (hsp0_align : s0.spAligned = true) (hw0_ne_none : w_out.b0.w0 ≠ noneCap)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 15296#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = outA) (hps1 : s1.pstate = addsPState64 w_out.b0.w0 1#64)
    (htr1 : TraceCalleeSaved s1 s0)
    (hwb1 : writebackDoneAt15296 s1 sp1 w_out.b5.w8 w_out.b5.w9 =
      { b0 := w_out.b0, b1 := w_out.b1, b2 := w_out.b2, b3 := w_out.b3, b4 := w_out.b4, b5 := w_out.b5,
        q60 := sp.q3c0, w62 := sp.b3.w1 }) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      (((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        (((s0.sp - 4240#64) + 2320#64) ↦₆₄ w_out.b5.w8) ∗ (((s0.sp - 4240#64) + 2328#64) ↦₆₄ w_out.b5.w9) ∗
        nhrRest1856At (s0.sp - 4240#64) w_out ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerReceived outSt }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine nhr_seq_clean_inImage hinv1
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 8984#64)
    (P_mid := (((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ P_rest ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out))) ∗
      memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
      sendEkSpillsAt fsp (nhrSpillsDone8984 s1 sp1 w_out.b5.w8 w_out.b5.w9) ∗
      memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = outA ∧
      writebackAt8984 s2 (nhrSpillsDone8984 s1 sp1 w_out.b5.w8 w_out.b5.w9) =
        { b0 := w_out.b0, b1 := w_out.b1, b2 := w_out.b2, b3 := w_out.b3, b4 := w_out.b4, b5 := w_out.b5,
          q60 := sp.q3c0, w62 := sp.b3.w1 } ∧ TraceCalleeSaved s2 s0) ?_ ?_
  · have hstep2 := nhr_step_15296_done_8984 hb s1 fsp w_out.b0.w0 w_out.b5.w8 w_out.b5.w9 sp1
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
       nhrRest1856At fsp w_out ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hw0_ne_none hpc1 hrun1 hsp1 hps1
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl_nhr_ext)) (SepWP.mono hstep2 ?_)
    intro s2 Pm _ _ ⟨hPm, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
      h2_8, h2_9, h2_10, h2_11, h2_12, h2_13, h2_14, h2_15, h2_16, h2_17, h2_18, h2_19,
      h2_20, h2_21, h2_22, h2_23, h2_24, h2_25, h2_26, h2_27, h2_28, _, h2_30, htr2⟩
    have hwb := (writebackAt8984_of_done15296 s1 s2 sp1 w_out.b5.w8 w_out.b5.w9
      h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6 h2_7 h2_8 h2_9 h2_10 h2_11 h2_12 h2_13 h2_14 h2_15 h2_16 h2_17 h2_18
      h2_20 h2_21 h2_22 h2_23 h2_24 h2_25 h2_26 h2_27 h2_28 h2_30).trans hwb1
    refine ⟨Entails.trans hPm ?_, hsp2, h2_19.trans hx19, hwb, htr2.trans htr1⟩
    have h880 := nhrRest1856At_rejoin_880 fsp w_out
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 2320#64) ↦₆₄ w_out.b5.w8) ∗ ((fsp + 2328#64) ↦₆₄ w_out.b5.w9) ∗ nhrRest1856At fsp w_out) ∗
      (((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp (nhrSpillsDone8984 s1 sp1 w_out.b5.w8 w_out.b5.w9) ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by sep_ac_rfl_nhr_ext)) ?_
    exact Entails.trans (sepConj_mono_left h880) (Entails.of_eq (by sep_ac_rfl_nhr_ext))
  · intro s2 hpc2 hrun2 hinv2 ⟨hsp2, h2_19, hwb, htr2⟩
    refine nhr_8984_ret_ext hA s0 s2 outA (nhrSpillsDone8984 s1 sp1 w_out.b5.w8 w_out.b5.w9) _
      (((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ P_rest ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)))
      _ hinv2 hsp0_align hpc2 hrun2 hsp2 h2_19 htr2 hwb (fun w936 q944 => ?_)
    have htag : (nhrSpillsDone8984 s1 sp1 w_out.b5.w8 w_out.b5.w9).b2.w7 = 8#64 := rfl
    rw [htag]
    have hout := nhr_done_out_entails_resultV1RecvAt A (F := F) outA outSt w_out
      sp.q3c0 sp.b3.w1 w936 q944
    refine Entails.trans (Entails.of_eq (show _ = ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ P_rest ∗
      ((outA ↦₆₄ 8#64) ∗ words63At (outA + 8#64)
         { b0 := w_out.b0, b1 := w_out.b1, b2 := w_out.b2, b3 := w_out.b3, b4 := w_out.b4, b5 := w_out.b5,
           q60 := sp.q3c0, w62 := sp.b3.w1 } ∗
       memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ∗
       ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944) ∗
       relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out))) ∗
      memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX by sep_ac_rfl_nhr_ext)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hout))

theorem nhr_done_8616_ret_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContractsX img A ext)
    (s0 s : State) (outA selfA : BitVec 64)
    (outSt : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (w_out : Words60) (sp : SendEkSpills) (P_rest : SepProp)
    (hinv : ImgCallInv img s) (hsp0_align : s0.spAligned = true)
    (hw0_ne_err : w_out.b0.w0 ≠ 0xfffffffffffffffe#64) (hw0_ne_none : w_out.b0.w0 ≠ noneCap)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 8616#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64)
    (hx19 : s.readReg64 .x19 = outA) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        words60At ((s0.sp - 4240#64) + 1856#64) w_out ∗ memRegion ((s0.sp - 4240#64) + 2336#64) 400 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerReceived outSt }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine nhr_seq_clean_inImage hinv
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 15296#64)
    (P_mid := ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)) ∗
      stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp (nhrSpills15296 sp w_out) ∗
      memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
      ((fsp + 2320#64) ↦₆₄ w_out.b5.w8) ∗ ((fsp + 2328#64) ↦₆₄ w_out.b5.w9) ∗
      nhrRest1856At fsp w_out ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = outA ∧ s1.pstate = addsPState64 w_out.b0.w0 1#64 ∧
      writebackDoneAt15296 s1 (nhrSpills15296 sp w_out) w_out.b5.w8 w_out.b5.w9 =
        { b0 := w_out.b0, b1 := w_out.b1, b2 := w_out.b2, b3 := w_out.b3, b4 := w_out.b4, b5 := w_out.b5,
          q60 := sp.q3c0, w62 := sp.b3.w1 } ∧ TraceCalleeSaved s1 s0) ?_ ?_
  · have hstep1 := nhr_step_8616_ok_15296 s fsp w_out sp
      (((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2336#64) 400 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hw0_ne_err hpc hrun hsp
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl_nhr_ext)) (SepWP.mono hstep1 ?_)
    intro s1 Pm _ _ ⟨hPm, hsp1, h1_0, h1_1, h1_2, h1_4, h1_5, h1_6, h1_7, h1_8,
      h1_9, h1_10, h1_11, h1_12, h1_13, h1_14, h1_15, h1_16, h1_17, h1_18, h1_19,
      h1_20, h1_21, h1_22, h1_23, _, _, h1_26, h1_27, _, _, h1_30, hps1, htr1⟩
    have hwb1 := writebackDoneAt15296_of_8616 s1 sp w_out
      h1_0 h1_1 h1_2 h1_4 h1_5 h1_6 h1_7 h1_8 h1_9 h1_10 h1_11 h1_12 h1_13 h1_14 h1_15 h1_16 h1_17 h1_18
      h1_20 h1_21 h1_22 h1_23 h1_26 h1_27 h1_30
    refine ⟨Entails.trans hPm ?_, hsp1, h1_19.trans hx19, hps1, hwb1, htr1.trans htr⟩
    have hsplit := words60At_1856_400_split fsp w_out
    refine Entails.trans (Entails.of_eq (show _ =
      (words60At (fsp + 1856#64) w_out ∗ memRegion (fsp + 2336#64) 400) ∗
      (((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp (nhrSpills15296 sp w_out) ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by sep_ac_rfl_nhr_ext)) ?_
    exact Entails.trans (sepConj_mono_left hsplit) (Entails.of_eq (by sep_ac_rfl_nhr_ext))
  · intro s1 hpc1 hrun1 hinv1 ⟨hsp1, h1_19, hps1, hwb1, htr1⟩
    exact nhr_done_15296_ret_ext hb hA s0 s1 outA selfA outSt w_out sp (nhrSpills15296 sp w_out) P_rest
      hinv1 hsp0_align hw0_ne_none hpc1 hrun1 hsp1 h1_19 hps1 htr1 hwb1

end CryptoVerification.SpqrV1.States.Recv
