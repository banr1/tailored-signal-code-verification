/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv`: `SendEk` Shared Writeback Helpers under `AllocContractsX`

**Checked by Lean.** `AllocContractsX` (`extHookStack = 16384` B) `Relocatable` `memcpy` rule
and shared `Ok(V1Recv)` writeback epilogue (`0x59e88..0x59ff0`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv

/-! ## Shared AC-Framing & `.inImage img` Combinators -/

open Lean Meta Elab Tactic in
elab "sep_ac_rfl_recv_ext" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    let some (_, lhs, rhs) := ty.eq?
      | throwError "sep_ac_rfl_recv_ext: expected equality"
    if lhs == rhs then
      g.assign (← mkEqRefl lhs)
      replaceMainGoal []
    else if let some (tbl, tA, tB) := ProofLib.SepSolver.synReifyPermTbl? lhs rhs then
      g.assign (← ProofLib.SepSolver.eqACOfTbl lhs rhs tbl tA tB)
      replaceMainGoal []
    else
      evalTactic (← `(tactic| sep_frame))

theorem sepWP_weaken_mono_recv_ext {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post post' : State → SepProp → Prop}
    (h : SepWP prog target_pc s P' post')
    (hpost : ∀ sf Pf, sf.pc = target_pc → sf.status = .Running → post' sf Pf → post sf Pf)
    (hP : P = P' := by sep_ac_rfl_recv_ext) :
    SepWP prog target_pc s P post :=
  hP ▸ SepWP.mono h hpost

theorem sepWPp_weaken_inImage_recv_ext {img : Obj.Image} {prog : Program}
    {mid_pc target_pc : BitVec 64} {s : State} {P P' : SepProp}
    {Q_post Q_panic : State → SepProp → Prop} (hinv : ImgCallInv img s)
    (h : SepWP prog mid_pc s P'
      (fun sm Pm => ImgCallInv img sm → SepWPp prog target_pc sm Pm Q_post Q_panic))
    (hP : P = P' := by sep_ac_rfl_recv_ext) :
    SepWPp prog target_pc s P Q_post Q_panic :=
  hP ▸ SepWPp.of_sepWP_inImage hinv h

theorem sepWPp_seq_clean_inImage_sendek {prog : Program} {img : Obj.Image}
    {mid ret : BitVec 64} {s : State} {P P' : SepProp} {φ : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P') ∧ φ sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → ImgCallInv img sm → φ sm →
      SepWPp prog ret sm P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.of_sepWP_frozen (mid := mid) hinv.1 hinv.2 ?_
  refine SepWP.mono h1 ?_
  intro sm Pm hpc hrun ⟨hPm, hφ⟩ hF hsym
  exact SepWPp.weaken_pre hPm (h2 sm hpc hrun ⟨hF, hsym⟩ hφ)

/-! ## `AllocContractsX`-Backed `memcpy` Relocation Helper -/

abbrev sessionMemcpyRegionSpecExt : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withStack sessionMemcpyRegionSpec extHookStack

theorem session_memcpy_region_ok_at_ext_of_alloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName :=
      by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemcpyRegionSpecExt.inImage img) :=
  hA.session_memcpy_region_ok_at name k extHookStack (by decide) (by decide) hk

/-- Framed `.inImage img` `memcpy` call rule under `AllocContractsX` (`extHookStack = 16384` B)
    that relocates any `Relocatable n F` predicate from `src` to `dst`, leaving `memRegion src n`
    at `src`, and forwards `CalleeSavedPreserved s sf`, `TraceCalleeSaved sf s0`, and
    `ImgCallInv img sf`. -/
theorem call_memcpy_relocate_cs_inImage_stk_ext {img : Obj.Image} {prog : Program}
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sessionMemcpyRegionSpecExt.inImage img))
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
    rw [hsplit, hstk_split]; sep_ac_rfl_recv_ext
  rw [hsplit']
  refine SepWP.fold (relocate_pre_entails hrel dst src
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
    dsimp only [Spec.inImage, sessionMemcpyRegionSpecExt, withStack, sessionMemcpyRegionSpec,
      memcpyRegionSpec]
    rw [hsp, hlen, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hin.1, hin.2⟩, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl_recv_ext)) hm⟩
  · dsimp only [Spec.inImage, sessionMemcpyRegionSpecExt, withStack, sessionMemcpyRegionSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    have hcomm :
        ((dst ↦ₛ bs ∗ src ↦ₛ bs) ∗ stackAt sp_call extHookStack ∗
          relocatedHeap F bs ∗ memRegion (sp_call - BitVec.ofNat 64 stk) k_stk ∗ Frame) =
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗
          (relocatedHeap F bs ∗ (stackAt sp_call stk ∗ Frame)) := by
      rw [hstk_split]; sep_ac_rfl_recv_ext
    rw [hcomm]
    refine SepWP.fold (relocate_post_entails dst src hlen (stackAt sp_call stk ∗ Frame))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp, show (F dst ∗ memRegion src n) ∗ (stackAt sp_call stk ∗ Frame) =
        (F dst ∗ memRegion src n ∗ stackAt sp_call stk) ∗ Frame by sep_ac_rfl_recv_ext]
    exact SepWP.done hpc_sf hrun_sf fun hinv_sf =>
      hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
        ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hinv_sf

/-! ## Shared `Ok(V1Recv)` Writeback + Epilogue (`0x59e88..0x59ff0`) under `AllocContractsX` -/

set_option maxHeartbeats 1200000 in
theorem states_recv_writeback_59e88_step_to_memcpy_ext {img : Obj.Image} {A : RustAlloc}
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
  have hmemcpy_raw := session_memcpy_region_ok_at_ext_of_alloc hA statesRecvName
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
  refine SepWP.done rfl (by exact hrun) fun hinv_call => ?_
  refine call_memcpy_relocate_cs_inImage_stk_ext (ret_pc := entry + 19284#64)
    (stk := statesRecvCalleeStackX) (k_stk := 3168) hmemcpy_raw hrel (outA + 512#64) (sp0 - 3664#64)
    hinv_call rfl (by exact hrun) (by exact hsp) hfsp_align rfl (by exact htr) rfl rfl rfl
    (by decide) (by decide) (by sep_frame) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1 _hinv1
  have hx19_1 : sf1.readReg64 .x19 = outA := hcs1.1.trans hx19
  have hx20_1 : sf1.readReg64 .x20 = s.readReg64 .x20 := hcs1.2.1
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
    simp only [pointsTo128_eq_pair64_recv, arm64_norm]; sep_ac_rfl_recv_ext
  · refine sepWP_weaken_mono_recv_ext
      (hepilogue _ (P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 s sp) ∗
        F_tail (outA + 512#64) ∗ memRegion (outA + 888#64) 40 ∗ ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗
        ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗ ((outA + 944#64) ↦₁₂₈ sp.q200))
        rfl hrun1 hsp1 hsp_align htr1)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl_recv_ext)), hsp_sf, hcs_sf, htr_sf⟩)

theorem states_recv_writeback_59e88_ext {img : Obj.Image} {A : RustAlloc}
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
    (states_recv_writeback_59e88_step_to_memcpy_ext hA hrel s0 s outA sp P_rest
      hpc hrun hsp hsp_align hx19 htr)

/-! ## `statesRecvCalleeStackXExt` (`35936` B) Callee Stack-Growth Helpers -/

/-- `abbrev` definitionally equal (`rfl`) to `DispatchExt.growToCalleeExt`, growing any callee
    `Spec α` at stack budget `oldStack ≤ statesRecvCalleeStackXExt` up to `statesRecvCalleeStackXExt`
    (`35936` B) without importing `DispatchExt`. -/
abbrev growToCalleeExtSendEk {α : Type} (oldStack : Nat) (spec : Spec α) : Spec α :=
  { pre := fun x s =>
      spec.pre x s ∗
        memRegion (s.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
          (statesRecvCalleeStackXExt - oldStack)
    post := fun x s0 sf =>
      spec.post x s0 sf ∗
        memRegion (s0.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
          (statesRecvCalleeStackXExt - oldStack)
    onPanic := spec.onPanic }

theorem stackAt_statesRecvCalleeExt_split (sp_call : BitVec 64) (oldStack : Nat)
    (hle : oldStack ≤ statesRecvCalleeStackXExt := by decide) :
    stackAt sp_call statesRecvCalleeStackXExt =
      memRegion (sp_call - BitVec.ofNat 64 statesRecvCalleeStackXExt)
        (statesRecvCalleeStackXExt - oldStack) ∗
      stackAt sp_call oldStack := by
  have hadd : oldStack + (statesRecvCalleeStackXExt - oldStack) = statesRecvCalleeStackXExt :=
    Nat.add_sub_of_le hle
  have hbound : oldStack + (statesRecvCalleeStackXExt - oldStack) ≤ 2 ^ 64 := by
    rw [hadd]; decide
  simpa [hadd] using
    ProofLib.stackAt_split_bottom sp_call oldStack (statesRecvCalleeStackXExt - oldStack) hbound

theorem states_recv_writeback_59e88_stk_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    {F_tail : BitVec 64 → SepProp} (hrel : Relocatable 376 F_tail)
    (s0 s : State) (outA : BitVec 64) (sp : SendEkSpills) (P_rest : SepProp)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true) (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗ F_tail ((s0.sp - 4240#64) + 576#64) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 s sp) ∗
          F_tail (outA + 512#64) ∗ memRegion (outA + 888#64) 40 ∗
          ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗ ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗
          ((outA + 944#64) ↦₁₂₈ sp.q200) ∗ stackAt s0.sp statesRecvStackXExt) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hpre :
      P_rest ∗ memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗ F_tail ((s0.sp - 4240#64) + 576#64) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0 =
      (P_rest ∗ memRegion (s0.sp - 40176#64) 16384) ∗ memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗ F_tail ((s0.sp - 4240#64) + 576#64) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0 := by
    rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]; sep_ac_rfl_recv_ext
  rw [hpre]
  refine SepWP.mono
    (states_recv_writeback_59e88_ext hA hrel s0 s outA sp
      (P_rest ∗ memRegion (s0.sp - 40176#64) 16384) hinv hpc hrun hsp hsp_align hx19 htr)
    (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
      ⟨Entails.trans hPf
        (Entails.of_eq (by rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; sep_ac_rfl_recv_ext)),
       hsp_sf, hcs_sf, htr_sf⟩)

end CryptoVerification.SpqrV1.States.Recv
