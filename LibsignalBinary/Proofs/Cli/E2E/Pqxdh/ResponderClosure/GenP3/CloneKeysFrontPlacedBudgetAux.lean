/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysBasePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysBase
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Step & Substage Helpers for Placed Segment 1 (Block `518`)

Pool-transporting `SepWP`/`SepWPp` combinators, `VmPreserved` basic-block steps
(`+0x1778 .. +0x19b0`), budget-threaded `__rust_alloc(sz, 1)` wrappers, and substage clone
theorems for `local_identity_public`, `remote_identity_public`, `root_key`, and `sender_chain`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (RootKey SenderChain)
open CryptoVerification (LibsignalPlacement lsMemcpySym ls_subroutine_ok_of_block lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (OptSenderChainCloneRel genP3SenderInlineWords)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkLib_eq_518 blkPl_518 lsProg_518)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpyRegionSpec sessionShimSpec)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (OptSenderChainInline bytes104OfW6Q optSenderChainAt_entails_chunks104W6Q optSenderChainHeap)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (cap_add_one_ne_zero chunks104W6QAt_entails_memRegion eq_nil_or_length_pos ofNat_ne_zero_of_pos optSenderChainAt_some_eq_cap optSenderChainSomeRest vecGhostAt_eq_of_nil vecGhostAt_eq_of_pos vecU8At_eq_of_pos vecU8Buf_nil_eq vecU8Buf_pos_eq)
open CryptoVerification.LibsignalTripleRatchetRepr (SenderChainGhost noneCap optSenderChainAt)
open CryptoVerification.RustHeap (allocHookStack vecU8At vecU8Buf)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (
  SenderChainCloneGhost chainCloneStack
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1 (
  cat128_hi cat128_lo chunks104W6QAt_sp_0x3e0 entails_pure_3rd
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
  VmPreserved rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  withStack subroutine_ok_withStack_of_subroutine_ok
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  SenderChainCloneEnv senderChainCloneEvents senderChainCloneSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget (
  SenderChainClone3OkPlaced
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-! ## 1. Polymorphic `SepWPp` & Pool-Transporting Segment Combinators -/

theorem sepWPp_done_any {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = ret) (hrun : s.status = .Running) (hQ : Q s P) :
    SepWPp prog ret s P Q Qp :=
  fun _ hm _ => ⟨s, Steps.refl s, Or.inl ⟨hpc, hrun, P, hm, hQ⟩⟩

theorem sepWPp_weaken_pre_any {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R hm hL => h R (Satisfies.mono (sepConj_mono_left hent) hm) hL

theorem sepWPp_weaken_frame_any {prog : Program} {ret : BitVec 64} {s : State}
    {P T T' F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : T ⊢ T') (hP : P = T ∗ F)
    (h : SepWPp prog ret s (T' ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  sepWPp_weaken_pre_any (hP ▸ sepConj_mono_left hent) h

theorem sepWPp_pure_elim_any {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

theorem sepWPp_exists_elim_any {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Φ : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ x : α, SepWPp prog ret s (Φ x) Q Qp) :
    SepWPp prog ret s (∃∗ x : α, Φ x) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hmx⟩
  exact h x R hmx hL

theorem sepWPp_pure_3rd_any {prog : Program} {ret : BitVec 64} {s : State}
    {A1 A2 R : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A1 ∗ A2 ∗ R) Q Qp) :
    SepWPp prog ret s (A1 ∗ A2 ∗ ⌜φ⌝ ∗ R) Q Qp := by
  have heq : (A1 ∗ A2 ∗ ⌜φ⌝ ∗ R) = (⌜φ⌝ ∗ (A1 ∗ A2 ∗ R)) := by sep_ac_rfl
  rw [heq]
  exact sepWPp_pure_elim_any h

theorem sepWPp_pure_4th_any {prog : Program} {ret : BitVec 64} {s : State}
    {A1 A2 A3 R : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A1 ∗ A2 ∗ A3 ∗ R) Q Qp) :
    SepWPp prog ret s (A1 ∗ A2 ∗ A3 ∗ ⌜φ⌝ ∗ R) Q Qp := by
  have heq : (A1 ∗ A2 ∗ A3 ∗ ⌜φ⌝ ∗ R) = (⌜φ⌝ ∗ (A1 ∗ A2 ∗ A3 ∗ R)) := by sep_ac_rfl
  rw [heq]
  exact sepWPp_pure_elim_any h

theorem sepWPp_bind_frame_any {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_stage F : SepProp} {Q_mid Q Qp : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage Q_mid (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm P_m, sm.pc = mid → sm.status = .Running → Q_mid sm P_m →
      SepWPp prog ret sm (P_m ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hqm⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm P_m hpcm hrunm hqm R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact False.elim hpan
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem sepWPp_bind_frame_dep_any {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step : SepProp} {P_post : State → SepProp} {F : SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hstep : SepWPp prog mid s P_step
      (fun sm P_m => (P_m ⊢ P_post sm) ∧ Q_regs sm) (fun _ _ => False))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm (P_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩⟩ :=
    hstep (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_post sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact False.elim hpan
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem bind_sepWP_vm_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_m => VmPreserved s sm ∧ (P_m ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = (P_step ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → VmPreserved s sm → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ (A.pool lim st sm ∗ F)) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hstep' : SepWP prog mid s P_step
      (fun sm P_m => (P_m ⊢ P_step_post) ∧ VmPreserved s sm ∧ Q_regs sm) := by
    apply SepWP.of_reaches_pc
    intro R hm hL
    obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hvmp, hent, hq⟩ | ⟨_, hoom⟩⟩ :=
      SepWP.to_reaches_pc hstep hm hL
    · exact ⟨sm, hsteps, Or.inl ⟨hpc, hrun, Pm, hmm, hent, hvmp, hq⟩⟩
    · exact False.elim (not_satisfies_false_sepConj hoom)
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.bind_sepWP_lscro_frame_placed hcro hstep' (by rw [hP, sepConj_assoc])
    fun sm hpcm hrunm hcrom ⟨hvmp, hregs⟩ => ?_
  rw [← A.pool_of_vmPreserved hvmp]
  exact hnext sm hpcm hrunm hcrom hvmp hregs

theorem ret_sepWP_vm_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {ret : BitVec 64}
    {s : State} {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog ret s P_step
      (fun s1 P_f => VmPreserved s s1 ∧ (P_f ⊢ P_step_post) ∧ Q_regs s1))
    (hP : P = (P_step ∗ A.pool lim st s) ∗ F)
    (hpost : ∀ s1 : State, s1.pc = ret → s1.status = .Running →
      LibsignalCodeRoLoaded lsmpl s1.mem → VmPreserved s s1 → Q_regs s1 →
      Q s1 (P_step_post ∗ (A.pool lim st s1 ∗ F))) :
    SepWPp prog ret s P Q Qp :=
  bind_sepWP_vm_pool_placed hcro hstep hP fun s1 hpc1 hrun1 hcro1 hvmp1 hregs =>
    sepWPp_done_any hpc1 hrun1 (hpost s1 hpc1 hrun1 hcro1 hvmp1 hregs)

theorem senderChainClone3_at_518_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hscc : SenderChainClone3OkPlaced A lim ext) :
    subroutine_ok (lsProg_518 ext) (lsmpl.base 524)
      (withLsCodeLoaded lsmpl (senderChainCloneSpec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_518 ext)
    (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl) hscc) (by decide)

/-! ## 2. `VmPreserved` Step Helpers on Block `518` (`+0x1778 .. +0x19b0`) -/

set_option maxHeartbeats 400000 in
theorem seg1a_placed_wp_vm [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hshim_raw : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsShimSym) sessionShimBudgetSpec)
    (s : State) (coroPtr locIdPtr locIdLen u_d0 : BitVec 64)
    (sessionVer u_7c : BitVec 32)
    (hlen_nz : locIdLen ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x1778#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x179c#64) s
      (((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗
       ((coroPtr + 0x108#64) ↦₆₄ locIdLen) ∗
       ((coroPtr + 0x240#64) ↦₃₂ sessionVer) ∗
       ((s.sp + 0x7c#64) ↦₃₂ u_7c) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢
          ((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗
          ((coroPtr + 0x108#64) ↦₆₄ locIdLen) ∗
          ((coroPtr + 0x240#64) ↦₃₂ sessionVer) ∗
          ((s.sp + 0x7c#64) ↦₃₂ sessionVer) ∗
          ((s.sp + 0xd0#64) ↦₆₄ locIdLen)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = locIdLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = locIdPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hshim := hshim_raw
  dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim
  have hlen_beq : (locIdLen == 0#64) = false := beq_eq_false_iff_ne.mpr hlen_nz
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException ext)) blkLib_eq_518 blkLib_518_noSvc0
    (mid := lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsShimSym)
  intro m_strip
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun m_real hnsp => ?_
  have hvmp0 : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  simp only [State.setMem_setMem] at hvmp0 ⊢
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp only [arm64_norm]; exact hvmp0.trans (by assumption),
    Entails.of_eq (by sep_ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem seg1b_4k_placed_wp_vm [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hmemcpy_raw : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (s : State) (coroPtr locIdPtr newLocIdPtr : BitVec 64)
    (locIdBytes : List (BitVec 8))
    (hnew_nz : newLocIdPtr ≠ 0#64)
    (hlen_lt : locIdBytes.length < 2 ^ 64)
    (hpc : s.pc = (blkPl_518).base + 0x17a0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newLocIdPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = locIdPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x18e0#64) s
      (((s.sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 locIdBytes.length) ∗
       (locIdPtr ↦ₛ locIdBytes) ∗
       memRegion newLocIdPtr locIdBytes.length ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢
          ((s.sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 locIdBytes.length) ∗
          (locIdPtr ↦ₛ locIdBytes) ∗
          (newLocIdPtr ↦ₛ locIdBytes) ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x23 = newLocIdPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy := subroutine_ok_withStack_of_subroutine_ok hmemcpy_raw allocHookStack
  dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
    sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hmemcpy
  have hnew_beq : (newLocIdPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hnew_nz
  have hx0' : s.readReg64 (Reg.gpr 0#5) = newLocIdPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = locIdPtr := hx21
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException ext)) blkLib_eq_518 blkLib_518_noSvc0
    (mid := lsρ lsMemcpySym)
  intro m_strip
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun m_real hnsp => ?_
  have hvmp0 : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  simp only [State.setMem_setMem] at hvmp0 ⊢
  wp_call hmemcpy (newLocIdPtr, locIdPtr, locIdBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp only [arm64_norm]; exact hvmp0.trans (by assumption),
    Entails.of_eq (by sep_ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem seg2a_placed_wp_vm [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hshim_raw : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsShimSym) sessionShimBudgetSpec)
    (s : State) (coroPtr remIdPtr remIdLen : BitVec 64)
    (hlen_nz : remIdLen ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x18e0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x18fc#64) s
      (((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗
       ((coroPtr + 0x120#64) ↦₆₄ remIdLen))
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢
          ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗
          ((coroPtr + 0x120#64) ↦₆₄ remIdLen)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = remIdLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = remIdPtr ∧
        s1.readReg64 .x22 = s.sp + 0x930#64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = remIdLen ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hshim := hshim_raw
  dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim
  have hlen_beq : (remIdLen == 0#64) = false := beq_eq_false_iff_ne.mpr hlen_nz
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException ext)) blkLib_eq_518 blkLib_518_noSvc0
    (mid := lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsShimSym)
  intro m_strip
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun m_real hnsp => ?_
  have hvmp0 : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  simp only [State.setMem_setMem] at hvmp0 ⊢
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp only [arm64_norm]; exact hvmp0.trans (by assumption),
    Entails.of_eq (by sep_ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem seg2b_4k_placed_wp_vm [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hmemcpy_raw : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (s : State) (coroPtr remIdPtr newRemIdPtr : BitVec 64)
    (remIdBytes : List (BitVec 8))
    (hnew_nz : newRemIdPtr ≠ 0#64)
    (hlen_lt : remIdBytes.length < 2 ^ 64)
    (hpc : s.pc = (blkPl_518).base + 0x1900#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newRemIdPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = remIdPtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 remIdBytes.length) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x191c#64) s
      ((remIdPtr ↦ₛ remIdBytes) ∗
       memRegion newRemIdPtr remIdBytes.length ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢
          (remIdPtr ↦ₛ remIdBytes) ∗
          (newRemIdPtr ↦ₛ remIdBytes) ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 remIdBytes.length ∧
        s1.readReg64 .x25 = newRemIdPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy := subroutine_ok_withStack_of_subroutine_ok hmemcpy_raw allocHookStack
  dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
    sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hmemcpy
  have hnew_beq : (newRemIdPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hnew_nz
  have hx0' : s.readReg64 (Reg.gpr 0#5) = newRemIdPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = remIdPtr := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 remIdBytes.length := hx24
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException ext)) blkLib_eq_518 blkLib_518_noSvc0
    (mid := lsρ lsMemcpySym)
  intro m_strip
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun m_real hnsp => ?_
  have hvmp0 : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  simp only [State.setMem_setMem] at hvmp0 ⊢
  wp_call hmemcpy (newRemIdPtr, remIdPtr, remIdBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp only [arm64_norm]; exact hvmp0.trans (by assumption),
    Entails.of_eq (by sep_ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem seg3a_placed_wp_vm [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hshim_raw : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsShimSym) sessionShimBudgetSpec)
    (s : State) (coroPtr rootKeyPtr rootKeyLen u_98 : BitVec 64)
    (hlen_nz : rootKeyLen ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x191c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1938#64) s
      (((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗
       ((coroPtr + 0x138#64) ↦₆₄ rootKeyLen) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98))
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢
          ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗
          ((coroPtr + 0x138#64) ↦₆₄ rootKeyLen) ∗
          ((s.sp + 0x98#64) ↦₆₄ rootKeyLen)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = rootKeyLen ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = rootKeyPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = rootKeyLen ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hshim := hshim_raw
  dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim
  have hlen_beq : (rootKeyLen == 0#64) = false := beq_eq_false_iff_ne.mpr hlen_nz
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException ext)) blkLib_eq_518 blkLib_518_noSvc0
    (mid := lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsShimSym)
  intro m_strip
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun m_real hnsp => ?_
  have hvmp0 : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  simp only [State.setMem_setMem] at hvmp0 ⊢
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp only [arm64_norm]; exact hvmp0.trans (by assumption),
    Entails.of_eq (by sep_ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem seg3b_4k_placed_wp_vm [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hmemcpy_raw : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (s : State) (coroPtr rootKeyPtr newRootKeyPtr u_50 : BitVec 64)
    (rootKeyBytes : List (BitVec 8))
    (hnew_nz : newRootKeyPtr ≠ 0#64)
    (hlen_lt : rootKeyBytes.length < 2 ^ 64)
    (hpc : s.pc = (blkPl_518).base + 0x193c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = newRootKeyPtr)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = rootKeyPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 rootKeyBytes.length) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x195c#64) s
      (((s.sp + 0x50#64) ↦₆₄ u_50) ∗
       (rootKeyPtr ↦ₛ rootKeyBytes) ∗
       memRegion newRootKeyPtr rootKeyBytes.length ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢
          ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
          (rootKeyPtr ↦ₛ rootKeyBytes) ∗
          (newRootKeyPtr ↦ₛ rootKeyBytes) ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy := subroutine_ok_withStack_of_subroutine_ok hmemcpy_raw allocHookStack
  dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
    sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hmemcpy
  have hnew_beq : (newRootKeyPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hnew_nz
  have hx0' : s.readReg64 (Reg.gpr 0#5) = newRootKeyPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = rootKeyPtr := hx21
  have hx26' : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 rootKeyBytes.length := hx26
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException ext)) blkLib_eq_518 blkLib_518_noSvc0
    (mid := lsρ lsMemcpySym)
  intro m_strip
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun m_real hnsp => ?_
  have hvmp0 : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  simp only [State.setMem_setMem] at hvmp0 ⊢
  wp_call hmemcpy (newRootKeyPtr, rootKeyPtr, rootKeyBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp only [arm64_norm]; exact hvmp0.trans (by assumption),
    Entails.of_eq (by sep_ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem seg4a1_placed_wp_vm [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr sc0 : BitVec 64)
    (prevCounter u_5c : BitVec 32)
    (hsc_ne : sc0 + 1#64 ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x195c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 524) s
      (((coroPtr + 0x188#64) ↦₆₄ sc0) ∗
       ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
       ((s.sp + 0x5c#64) ↦₃₂ u_5c))
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢
          ((coroPtr + 0x188#64) ↦₆₄ sc0) ∗
          ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
          ((s.sp + 0x5c#64) ↦₃₂ prevCounter)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x1 = coroPtr + 0x188#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x197c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsc_beq : (sc0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hsc_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨by simp_all [arm64_norm], Entails.of_eq (by sep_ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem seg4a2_placed_wp_vm [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr u_48
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x197c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = s.sp + 0x930#64)
    (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x19b0#64) s
      (((s.sp + 0x48#64) ↦₆₄ u_48) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ c0) ∗ ((s.sp + 0x3e8#64) ↦₆₄ c1) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ c2) ∗ ((s.sp + 0x3f8#64) ↦₆₄ c3) ∗
       ((s.sp + 0x400#64) ↦₆₄ c4) ∗ ((s.sp + 0x408#64) ↦₆₄ c5) ∗
       ((s.sp + 0x410#64) ↦₆₄ c6) ∗ ((s.sp + 0x418#64) ↦₆₄ c7) ∗
       ((s.sp + 0x420#64) ↦₆₄ c8) ∗ ((s.sp + 0x428#64) ↦₆₄ c9) ∗
       ((s.sp + 0x430#64) ↦₆₄ c10) ∗ ((s.sp + 0x438#64) ↦₆₄ c11) ∗
       ((s.sp + 0x440#64) ↦₆₄ c12) ∗
       ((s.sp + 0x930#64) ↦₆₄ u930) ∗ ((s.sp + 0x938#64) ↦₆₄ u938) ∗
       ((s.sp + 0x940#64) ↦₆₄ u940) ∗ ((s.sp + 0x948#64) ↦₆₄ u948) ∗
       ((s.sp + 0x950#64) ↦₆₄ u950) ∗ ((s.sp + 0x958#64) ↦₆₄ u958) ∗
       ((s.sp + 0x960#64) ↦₆₄ u960) ∗ ((s.sp + 0x968#64) ↦₆₄ u968) ∗
       ((s.sp + 0x970#64) ↦₆₄ u970) ∗ ((s.sp + 0x978#64) ↦₆₄ u978) ∗
       ((s.sp + 0x980#64) ↦₆₄ u980) ∗ ((s.sp + 0x988#64) ↦₆₄ u988))
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢
          ((s.sp + 0x48#64) ↦₆₄ c0) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ c0) ∗ ((s.sp + 0x3e8#64) ↦₆₄ c1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ c2) ∗ ((s.sp + 0x3f8#64) ↦₆₄ c3) ∗
          ((s.sp + 0x400#64) ↦₆₄ c4) ∗ ((s.sp + 0x408#64) ↦₆₄ c5) ∗
          ((s.sp + 0x410#64) ↦₆₄ c6) ∗ ((s.sp + 0x418#64) ↦₆₄ c7) ∗
          ((s.sp + 0x420#64) ↦₆₄ c8) ∗ ((s.sp + 0x428#64) ↦₆₄ c9) ∗
          ((s.sp + 0x430#64) ↦₆₄ c10) ∗ ((s.sp + 0x438#64) ↦₆₄ c11) ∗
          ((s.sp + 0x440#64) ↦₆₄ c12) ∗
          ((s.sp + 0x930#64) ↦₆₄ c1) ∗ ((s.sp + 0x938#64) ↦₆₄ c2) ∗
          ((s.sp + 0x940#64) ↦₆₄ c3) ∗ ((s.sp + 0x948#64) ↦₆₄ c4) ∗
          ((s.sp + 0x950#64) ↦₆₄ c5) ∗ ((s.sp + 0x958#64) ↦₆₄ c6) ∗
          ((s.sp + 0x960#64) ↦₆₄ c7) ∗ ((s.sp + 0x968#64) ↦₆₄ c8) ∗
          ((s.sp + 0x970#64) ↦₆₄ c9) ∗ ((s.sp + 0x978#64) ↦₆₄ c10) ∗
          ((s.sp + 0x980#64) ↦₆₄ c11) ∗ ((s.sp + 0x988#64) ↦₆₄ c12)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.sp + 0x370#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = s.sp + 0x930#64 := hx22
  have hx27' : s.readReg64 (Reg.gpr 27#5) = s.sp + 0x370#64 := hx27
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨by simp_all [arm64_norm], Entails.of_eq (by sep_ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem seg2_nil_placed_wp_vm [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x18e0#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x191c#64) s
      ((coroPtr + 0x120#64) ↦₆₄ 0#64)
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢ ((coroPtr + 0x120#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.sp + 0x930#64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = 0#64 ∧
        s1.readReg64 .x25 = 1#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨by simp_all [arm64_norm], Entails.of_eq (by sep_ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem seg4_none_placed_wp_vm [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr u_48 : BitVec 64)
    (prevCounter u_5c : BitVec 32)
    (hpc : s.pc = (blkPl_518).base + 0x195c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x19b0#64) s
      (((coroPtr + 0x188#64) ↦₆₄ noneCap) ∗
       ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
       ((s.sp + 0x48#64) ↦₆₄ u_48) ∗
       ((s.sp + 0x5c#64) ↦₃₂ u_5c))
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢
          ((coroPtr + 0x188#64) ↦₆₄ noneCap) ∗
          ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
          ((s.sp + 0x48#64) ↦₆₄ noneCap) ∗
          ((s.sp + 0x5c#64) ↦₃₂ prevCounter)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [noneCap] at hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨by simp_all [arm64_norm], Entails.of_eq (by sep_ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm]⟩

/-! ## 3. Budget-Threaded `__rust_alloc(sz, 1)` Call Wrappers (`+0x179c`, `+0x18fc`, `+0x1938`) -/

set_option maxHeartbeats 400000 in
theorem alloc_call_placed_budget_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (s : State) (ret_off : BitVec 64) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hfits : FitsEvents M lim stB (rustAllocEvents sz 1))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbl : SepWP (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsAllocSym) s emp
      (fun s1 P_f =>
        VmPreserved s s1 ∧ (P_f ⊢ emp) ∧ s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = BitVec.ofNat 64 sz ∧ s1.readReg64 .x1 = 1#64 ∧
        CalleeSavedPreserved s s1 ∧
        s1.readReg64 .x30 = (blkPl_518).base + ret_off))
    (hlr_ls : LsRetAddr624 ((blkPl_518).base + ret_off) := by
      simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + ret_off) s
      ((A.pool lim stB s ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢
          (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
           A.pool lim (M.stepEvents (rustAllocEvents sz 1) stB) s2 ∗
           stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ LibsignalCodeRoLoaded lsmpl s2.mem)
      Qp := by
  have halloc_no := subroutine_ok_allocNoOom_of_budget halloc
  refine bind_sepWP_vm_pool_placed (A := A) (lim := lim) (st := stB)
    (F := stackAt s.sp allocHookStack ∗ F) hcro hbl
    (by simp only [emp_sepConj, sepConj_assoc])
    fun s1 hpc1 hrun1 hcro1 _ ⟨hsp1, htr1, hx0_1, hx1_1, hcs1, hlr1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  have hsz_nat : (BitVec.ofNat 64 sz).toNat = sz := Nat.mod_eq_of_lt (by omega)
  have hlay : RustLayoutOk sz 1 := ⟨⟨hsz_pos, ⟨0, rfl⟩, by omega⟩, by decide⟩
  have hφ : (s1.readReg64 .x0).toNat = sz ∧ (s1.readReg64 .x1).toNat = 1 ∧
      RustLayoutOk sz 1 ∧ FitsEvents M lim stB (rustAllocEvents sz 1) ∧
      LsRetAddr624 (s1.readReg64 .lr) :=
    ⟨by rw [hx0_1, hsz_nat], by rw [hx1_1]; rfl, hlay, hfits,
     by rw [show s1.readReg64 .lr = (blkPl_518).base + ret_off from hlr1]; exact hlr_ls⟩
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.call_raw_nopanic_placed (spec := rustCliAllocNoOomSpec M A lim false)
    (x := (sz, 1, stB))
    (T := A.pool lim stB s1 ∗ stackAt s.sp allocHookStack) (F := F)
    hcro1 halloc_no hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [rustCliAllocNoOomSpec]; rw [hsp1])
    hφ (by simp only [emp_sepConj, sepConj_assoc])
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hcs : CalleeSavedPreserved s s2 := CalleeSavedPreserved.trans hcs1 hcs2
  dsimp only [rustCliAllocNoOomSpec]
  simp only [Bool.false_eq_true, ↓reduceIte, hsp1, sepConj_assoc]
  refine sepWPp_pure_elim_any fun ⟨hacp, hnz, _⟩ => ?_
  exact sepWPp_done_any hpc2 hrun2
    ⟨Entails.of_eq (by sep_ac_rfl), hnz, hsp2, hacp.2.1.trans htr1, hcs, hcro2⟩

set_option maxHeartbeats 400000 in
theorem alloc_179c_placed_budget_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hfits : FitsEvents M lim stB (rustAllocEvents sz 1))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x179c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x17a0#64) s
      ((A.pool lim stB s ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢
          (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
           A.pool lim (M.stepEvents (rustAllocEvents sz 1) stB) s2 ∗
           stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ LibsignalCodeRoLoaded lsmpl s2.mem)
      Qp := by
  refine alloc_call_placed_budget_ok ext halloc s 0x17a0#64 sz F
    hsz_pos hsz_lt hfits hcro hsp_align ?_
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨by simp_all [arm64_norm], Entails.refl _, rfl, rfl,
       by simp_all [arm64_norm], by simp_all [arm64_norm],
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem alloc_18fc_placed_budget_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hfits : FitsEvents M lim stB (rustAllocEvents sz 1))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x18fc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1900#64) s
      ((A.pool lim stB s ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢
          (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
           A.pool lim (M.stepEvents (rustAllocEvents sz 1) stB) s2 ∗
           stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ LibsignalCodeRoLoaded lsmpl s2.mem)
      Qp := by
  refine alloc_call_placed_budget_ok ext halloc s 0x1900#64 sz F
    hsz_pos hsz_lt hfits hcro hsp_align ?_
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨by simp_all [arm64_norm], Entails.refl _, rfl, rfl,
       by simp_all [arm64_norm], by simp_all [arm64_norm],
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem alloc_1938_placed_budget_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hfits : FitsEvents M lim stB (rustAllocEvents sz 1))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1938#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x193c#64) s
      ((A.pool lim stB s ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢
          (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
           A.pool lim (M.stepEvents (rustAllocEvents sz 1) stB) s2 ∗
           stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ LibsignalCodeRoLoaded lsmpl s2.mem)
      Qp := by
  refine alloc_call_placed_budget_ok ext halloc s 0x193c#64 sz F
    hsz_pos hsz_lt hfits hcro hsp_align ?_
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨by simp_all [arm64_norm], Entails.refl _, rfl, rfl,
       by simp_all [arm64_norm], by simp_all [arm64_norm],
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp_all [arm64_norm]⟩

/-! ## 4. Budget-Threaded Substage Clone Theorems (`+0x1778 → +0x19b0`) -/

/-- Exact allocator events emitted by `seg_senderChain_placed_budget_ok`. -/
def optSenderChainCloneEvents (scG : Option SenderChainGhost) (scM : Option SenderChain) :
    List AllocEvent :=
  match scG, scM with
  | some sg, some sc => senderChainCloneEvents sg sc
  | _, _ => []

set_option maxHeartbeats 400000 in
theorem seg_locId_placed_budget_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (s0 s : State) (coroPtr u_d0 : BitVec 64) (sessionVer u_7c : BitVec 32)
    (locIk : VecGhost) (hpos : 0 < locIk.bytes.length)
    (hfits : FitsEvents M lim stB (rustAllocEvents locIk.bytes.length 1))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1778#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x18e0#64) s
      (A.pool lim stB s ∗ stackAt s.sp allocHookStack ∗
        vecGhostAt A.repAlloc locIk (coroPtr + 0xf8#64) ∗
        ((coroPtr + 0x240#64) ↦₃₂ sessionVer) ∗
        ((s.sp + 0x7c#64) ↦₃₂ u_7c) ∗
        ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        ∃ newLocIdPtr : BitVec 64,
          (P_f ⊢
            A.pool lim (M.stepEvents (rustAllocEvents locIk.bytes.length 1) stB) s1 ∗
            stackAt s.sp allocHookStack ∗
            vecGhostAt A.repAlloc locIk (coroPtr + 0xf8#64) ∗
            vecU8Buf A.repAlloc (BitVec.ofNat 64 locIk.bytes.length) newLocIdPtr locIk.bytes ∗
            ((coroPtr + 0x240#64) ↦₃₂ sessionVer) ∗
            ((s.sp + 0x7c#64) ↦₃₂ sessionVer) ∗
            ((s.sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 locIk.bytes.length)) ∧
          s1.sp = s.sp ∧ s1.trace = s0.trace ∧ LibsignalCodeRoLoaded lsmpl s1.mem ∧
          s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x23 = newLocIdPtr ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp := by
  have h100 : coroPtr + 0xf8#64 + 8#64 = coroPtr + 0x100#64 := by bv_arith
  have h108 : coroPtr + 0xf8#64 + 16#64 = coroPtr + 0x108#64 := by bv_arith
  rw [vecGhostAt_eq_of_pos A.repAlloc locIk (coroPtr + 0xf8#64) hpos, h100, h108]
  simp only [sepConj_assoc]
  refine sepWPp_pure_3rd_any fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
  have hlen_lt63 : locIk.bytes.length < 2 ^ 63 := Nat.lt_of_le_of_lt hlen_le hcap_lt
  have hlen_lt64 : locIk.bytes.length < 2 ^ 64 := by omega
  have hlen_nz : BitVec.ofNat 64 locIk.bytes.length ≠ 0#64 :=
    ofNat_ne_zero_of_pos hpos hlen_lt64
  refine bind_sepWP_vm_pool_placed (A := A) (lim := lim) (st := stB) hcro
    (seg1a_placed_wp_vm ext hshim s coroPtr locIk.ptr (BitVec.ofNat 64 locIk.bytes.length) u_d0
      sessionVer u_7c hlen_nz hpc hrun hsp_align hx19)
    (by sep_focus)
    fun s1 hpc1 hrun1 hcro1 _
      ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, hx21_1, hx27_1, hx29_1, hvregs1⟩ => ?_
  have hsp1_al : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  refine sepWPp_bind_frame_dep_any
    (alloc_179c_placed_budget_ok (Qp := fun _ _ => False) ext halloc s1 locIk.bytes.length emp
      hpos hlen_lt63 hfits hcro1 hpc1 hrun1 hsp1_al hx0_1 hx1_1)
    (by rw [hsp1]; sep_focus)
    fun s2 hpc2 hrun2 ⟨hnew_nz, hsp2, htr2, hcs2, hcro2⟩ => ?_
  set newLocIdPtr := s2.readReg64 .x0
  have hsp2' : s2.sp = s.sp := hsp2.trans hsp1
  have hsp2_al : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2']; exact hsp_align
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2.1.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = locIk.ptr := hcs2.2.2.1.trans hx21_1
  have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hcs2.2.2.2.2.2.2.2.2.1.trans hx27_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
  have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s :=
    hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
  refine ret_sepWP_vm_pool_placed (A := A) (lim := lim)
    (st := M.stepEvents (rustAllocEvents locIk.bytes.length 1) stB) hcro2
    (seg1b_4k_placed_wp_vm ext hmemcpy s2 coroPtr locIk.ptr newLocIdPtr locIk.bytes
      hnew_nz hlen_lt64 hpc2 hrun2 hsp2_al rfl hx19_2 hx21_2)
    (by simp only [hsp1, hsp2']; sep_focus)
    fun s3 _ _ hcro3 _ ⟨hsp3, htr3, hx19_3, hx23_3, hx27_3, hx29_3, hvregs3⟩ => ?_
  refine ⟨newLocIdPtr, ?_, hsp3.trans hsp2', by rw [htr3, htr2, htr1, htr], hcro3,
    hx19_3, hx23_3, hx27_3.trans hx27_2, hx29_3.trans hx29_2, hvregs3.trans hvregs2⟩
  rw [vecU8Buf_pos_eq A.repAlloc newLocIdPtr locIk.bytes hpos hlen_lt63 hnew_nz]
  simp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, sepConj_assoc, hsp1, hsp2']
  exact entails_pure_3rd ⟨hlen_le, hcap_lt, hptr⟩ (Entails.of_eq (by sep_ac_rfl))

set_option maxHeartbeats 400000 in
theorem seg_remId_placed_budget_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (s0 s : State) (coroPtr : BitVec 64) (remIk : VecGhost)
    (hfits : FitsEvents M lim stB
      (if remIk.bytes.length = 0 then [] else rustAllocEvents remIk.bytes.length 1))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x18e0#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x191c#64) s
      (A.pool lim stB s ∗ stackAt s.sp allocHookStack ∗
        vecGhostAt A.repAlloc remIk (coroPtr + 0x110#64))
      (fun s1 P_f =>
        ∃ newRemIdPtr : BitVec 64,
          (P_f ⊢
            A.pool lim
              (M.stepEvents
                (if remIk.bytes.length = 0 then [] else rustAllocEvents remIk.bytes.length 1) stB)
              s1 ∗
            stackAt s.sp allocHookStack ∗
            vecGhostAt A.repAlloc remIk (coroPtr + 0x110#64) ∗
            vecU8Buf A.repAlloc (BitVec.ofNat 64 remIk.bytes.length) newRemIdPtr remIk.bytes) ∧
          s1.sp = s.sp ∧ s1.trace = s0.trace ∧ LibsignalCodeRoLoaded lsmpl s1.mem ∧
          s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.sp + 0x930#64 ∧
          s1.readReg64 .x23 = s.readReg64 .x23 ∧
          s1.readReg64 .x24 = BitVec.ofNat 64 remIk.bytes.length ∧
          s1.readReg64 .x25 = newRemIdPtr ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp := by
  have h118 : coroPtr + 0x110#64 + 8#64 = coroPtr + 0x118#64 := by bv_arith
  have h120 : coroPtr + 0x110#64 + 16#64 = coroPtr + 0x120#64 := by bv_arith
  rcases eq_nil_or_length_pos remIk.bytes with hnil | hpos
  · rw [vecGhostAt_eq_of_nil A.repAlloc remIk (coroPtr + 0x110#64) hnil, h118, h120]
    simp only [sepConj_assoc]
    refine sepWPp_pure_3rd_any fun ⟨hcap_lt, hptr⟩ => ?_
    refine ret_sepWP_vm_pool_placed (A := A) (lim := lim) (st := stB) hcro
      (seg2_nil_placed_wp_vm ext s coroPtr hpc hrun hsp_align hx19)
      (by sep_focus)
      fun s1 _ _ hcro1 _
        ⟨hsp1, htr1, hx19_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx29_1, hvregs1⟩ => ?_
    refine ⟨1#64, ?_, hsp1, htr1.trans htr, hcro1,
      hx19_1, hx22_1, hx23_1, by simpa [hnil] using hx24_1, hx25_1, hx27_1, hx29_1, hvregs1⟩
    simp only [hnil, List.length_nil, ↓reduceIte, LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
      BitVec.ofNat_eq_ofNat, vecU8Buf_nil_eq A.repAlloc,
      sepConj_emp, emp_sepConj, sepConj_assoc]
    exact entails_pure_3rd ⟨hcap_lt, hptr⟩ (Entails.of_eq (by sep_ac_rfl))
  · have hlen_ne : remIk.bytes.length ≠ 0 := Nat.ne_of_gt hpos
    simp only [hlen_ne, ↓reduceIte] at hfits ⊢
    rw [vecGhostAt_eq_of_pos A.repAlloc remIk (coroPtr + 0x110#64) hpos, h118, h120]
    simp only [sepConj_assoc]
    refine sepWPp_pure_3rd_any fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hlen_lt63 : remIk.bytes.length < 2 ^ 63 := Nat.lt_of_le_of_lt hlen_le hcap_lt
    have hlen_lt64 : remIk.bytes.length < 2 ^ 64 := by omega
    have hlen_nz : BitVec.ofNat 64 remIk.bytes.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hpos hlen_lt64
    refine bind_sepWP_vm_pool_placed (A := A) (lim := lim) (st := stB) hcro
      (seg2a_placed_wp_vm ext hshim s coroPtr remIk.ptr (BitVec.ofNat 64 remIk.bytes.length)
        hlen_nz hpc hrun hsp_align hx19)
      (by sep_focus)
      fun s1 hpc1 hrun1 hcro1 _
        ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1, hx27_1, hx29_1,
          hvregs1⟩ => ?_
    have hsp1_al : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    refine sepWPp_bind_frame_dep_any
      (alloc_18fc_placed_budget_ok (Qp := fun _ _ => False) ext halloc s1 remIk.bytes.length emp
        hpos hlen_lt63 hfits hcro1 hpc1 hrun1 hsp1_al hx0_1 hx1_1)
      (by rw [hsp1]; sep_focus)
      fun s2 hpc2 hrun2 ⟨hnew_nz, hsp2, htr2, hcs2, hcro2⟩ => ?_
    set newRemIdPtr := s2.readReg64 .x0
    have hsp2' : s2.sp = s.sp := hsp2.trans hsp1
    have hsp2_al : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2']; exact hsp_align
    have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2.1.trans hx19_1
    have hx21_2 : s2.readReg64 .x21 = remIk.ptr := hcs2.2.2.1.trans hx21_1
    have hx22_2 : s2.readReg64 .x22 = s.sp + 0x930#64 := hcs2.2.2.2.1.trans hx22_1
    have hx23_2 : s2.readReg64 .x23 = s.readReg64 .x23 := hcs2.2.2.2.2.1.trans hx23_1
    have hx24_2 : s2.readReg64 .x24 = BitVec.ofNat 64 remIk.bytes.length :=
      hcs2.2.2.2.2.2.1.trans hx24_1
    have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hcs2.2.2.2.2.2.2.2.2.1.trans hx27_1
    have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s :=
      hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    refine ret_sepWP_vm_pool_placed (A := A) (lim := lim)
      (st := M.stepEvents (rustAllocEvents remIk.bytes.length 1) stB) hcro2
      (seg2b_4k_placed_wp_vm ext hmemcpy s2 coroPtr remIk.ptr newRemIdPtr remIk.bytes
        hnew_nz hlen_lt64 hpc2 hrun2 hsp2_al rfl hx19_2 hx21_2 hx24_2)
      (by simp only [hsp1, hsp2']; sep_focus)
      fun s3 _ _ hcro3 _
        ⟨hsp3, htr3, hx19_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx29_3, hvregs3⟩ => ?_
    refine ⟨newRemIdPtr, ?_, hsp3.trans hsp2', by rw [htr3, htr2, htr1, htr], hcro3,
      hx19_3, hx22_3.trans hx22_2, hx23_3.trans hx23_2, hx24_3, hx25_3,
      hx27_3.trans hx27_2, hx29_3.trans hx29_2, hvregs3.trans hvregs2⟩
    rw [vecU8Buf_pos_eq A.repAlloc newRemIdPtr remIk.bytes hpos hlen_lt63 hnew_nz]
    simp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, sepConj_assoc, hsp1, hsp2']
    exact entails_pure_3rd ⟨hlen_le, hcap_lt, hptr⟩ (Entails.of_eq (by sep_ac_rfl))

set_option maxHeartbeats 400000 in
theorem seg_rootKey_placed_budget_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (s0 s : State) (coroPtr rootCap rootPtr u_50 u_98 : BitVec 64)
    (rootKey : RootKey)
    (hfits : FitsEvents M lim stB (rustAllocEvents 32 1))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x191c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x195c#64) s
      (A.pool lim stB s ∗ stackAt s.sp allocHookStack ∗
        vecU8At A.repAlloc (coroPtr + 0x128#64) rootCap rootPtr (keyToBytes32 rootKey) ∗
        ((s.sp + 0x50#64) ↦₆₄ u_50) ∗
        ((s.sp + 0x98#64) ↦₆₄ u_98))
      (fun s1 P_f =>
        ∃ newRootKeyPtr : BitVec 64,
          (P_f ⊢
            A.pool lim (M.stepEvents (rustAllocEvents 32 1) stB) s1 ∗
            stackAt s.sp allocHookStack ∗
            vecU8At A.repAlloc (coroPtr + 0x128#64) rootCap rootPtr (keyToBytes32 rootKey) ∗
            vecU8Buf A.repAlloc 32#64 newRootKeyPtr (keyToBytes32 rootKey) ∗
            ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
            ((s.sp + 0x98#64) ↦₆₄ 32#64)) ∧
          s1.sp = s.sp ∧ s1.trace = s0.trace ∧ LibsignalCodeRoLoaded lsmpl s1.mem ∧
          s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
          s1.readReg64 .x23 = s.readReg64 .x23 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
          s1.readReg64 .x25 = s.readReg64 .x25 ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp := by
  have h130 : coroPtr + 0x128#64 + 8#64 = coroPtr + 0x130#64 := by bv_arith
  have h138 : coroPtr + 0x128#64 + 16#64 = coroPtr + 0x138#64 := by bv_arith
  have hlen : (keyToBytes32 rootKey).length = 32 := by simp [keyToBytes32]
  have hpos : 0 < (keyToBytes32 rootKey).length := by omega
  have hlt63 : (keyToBytes32 rootKey).length < 2 ^ 63 := by omega
  have hlt64 : (keyToBytes32 rootKey).length < 2 ^ 64 := by omega
  have hbv32 : BitVec.ofNat 64 (keyToBytes32 rootKey).length = 32#64 := by rw [hlen]
  rw [vecU8At_eq_of_pos A.repAlloc (coroPtr + 0x128#64) rootCap rootPtr (keyToBytes32 rootKey) hpos,
      h130, h138, hbv32]
  simp only [sepConj_assoc]
  refine sepWPp_pure_3rd_any fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
  refine bind_sepWP_vm_pool_placed (A := A) (lim := lim) (st := stB) hcro
    (seg3a_placed_wp_vm ext hshim s coroPtr rootPtr 32#64 u_98 (by decide) hpc hrun hsp_align hx19)
    (by sep_focus)
    fun s1 hpc1 hrun1 hcro1 _
      ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1,
        hx27_1, hx29_1, hvregs1⟩ => ?_
  have hsp1_al : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  refine sepWPp_bind_frame_dep_any
    (alloc_1938_placed_budget_ok (Qp := fun _ _ => False) ext halloc s1 32 emp (by decide) (by decide)
      hfits hcro1 hpc1 hrun1 hsp1_al hx0_1 hx1_1)
    (by rw [hsp1]; sep_focus)
    fun s2 hpc2 hrun2 ⟨hnew_nz, hsp2, htr2, hcs2, hcro2⟩ => ?_
  set newRootKeyPtr := s2.readReg64 .x0
  have hsp2' : s2.sp = s.sp := hsp2.trans hsp1
  have hsp2_al : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2']; exact hsp_align
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2.1.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = rootPtr := hcs2.2.2.1.trans hx21_1
  have hx22_2 : s2.readReg64 .x22 = s.readReg64 .x22 := hcs2.2.2.2.1.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = s.readReg64 .x23 := hcs2.2.2.2.2.1.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = s.readReg64 .x24 := hcs2.2.2.2.2.2.1.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = s.readReg64 .x25 := hcs2.2.2.2.2.2.2.1.trans hx25_1
  have hx26_2 : s2.readReg64 .x26 = BitVec.ofNat 64 (keyToBytes32 rootKey).length := by
    rw [hbv32]; exact hcs2.2.2.2.2.2.2.2.1.trans hx26_1
  have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hcs2.2.2.2.2.2.2.2.2.1.trans hx27_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
  have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s :=
    hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
  refine ret_sepWP_vm_pool_placed (A := A) (lim := lim)
    (st := M.stepEvents (rustAllocEvents 32 1) stB) hcro2
    (seg3b_4k_placed_wp_vm ext hmemcpy s2 coroPtr rootPtr newRootKeyPtr u_50 (keyToBytes32 rootKey)
      hnew_nz hlt64 hpc2 hrun2 hsp2_al rfl hx19_2 hx21_2 hx26_2)
    (by simp only [hsp1, hsp2', hlen]; sep_focus)
    fun s3 _ _ hcro3 _
      ⟨hsp3, htr3, hx19_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx29_3, hvregs3⟩ => ?_
  have hbuf32 :
      vecU8Buf A.repAlloc 32#64 newRootKeyPtr (keyToBytes32 rootKey) =
        A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ keyToBytes32 rootKey) := by
    have h := vecU8Buf_pos_eq A.repAlloc newRootKeyPtr (keyToBytes32 rootKey) hpos hlt63 hnew_nz
    rwa [hlen, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at h
  refine ⟨newRootKeyPtr, ?_, hsp3.trans hsp2', by rw [htr3, htr2, htr1, htr], hcro3,
    hx19_3, hx22_3.trans hx22_2, hx23_3.trans hx23_2, hx24_3.trans hx24_2,
    hx25_3.trans hx25_2, hx27_3.trans hx27_2, hx29_3.trans hx29_2, hvregs3.trans hvregs2⟩
  rw [hbuf32]
  simp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, sepConj_assoc, hsp1, hsp2', hlen]
  exact entails_pure_3rd ⟨hlen_le, hcap_lt, hptr⟩ (Entails.of_eq (by sep_ac_rfl))

set_option maxHeartbeats 400000 in
theorem seg_senderChain_placed_budget_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hscc : SenderChainClone3OkPlaced A lim ext)
    (s0 s : State) (coroPtr u_48
      u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64)
    (prevCounter u_5c : BitVec 32)
    (scG : Option SenderChainGhost) (scM : Option SenderChain)
    (hfits : FitsEvents M lim stB (optSenderChainCloneEvents scG scM))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x195c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = s.sp + 0x930#64)
    (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x19b0#64) s
      (A.pool lim stB s ∗ stackAt s.sp chainCloneStack ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
        optSenderChainAt A.repAlloc (coroPtr + 0x188#64) scG scM ∗
        ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
        ((s.sp + 0x48#64) ↦₆₄ u_48) ∗
        ((s.sp + 0x5c#64) ↦₃₂ u_5c) ∗
        ((s.sp + 0x930#64) ↦₆₄ u930) ∗ ((s.sp + 0x938#64) ↦₆₄ u938) ∗
        ((s.sp + 0x940#64) ↦₆₄ u940) ∗ ((s.sp + 0x948#64) ↦₆₄ u948) ∗
        ((s.sp + 0x950#64) ↦₆₄ u950) ∗ ((s.sp + 0x958#64) ↦₆₄ u958) ∗
        ((s.sp + 0x960#64) ↦₆₄ u960) ∗ ((s.sp + 0x968#64) ↦₆₄ u968) ∗
        ((s.sp + 0x970#64) ↦₆₄ u970) ∗ ((s.sp + 0x978#64) ↦₆₄ u978) ∗
        ((s.sp + 0x980#64) ↦₆₄ u980) ∗ ((s.sp + 0x988#64) ↦₆₄ u988))
      (fun s1 P_f =>
        ∃ (sender' : Option SenderChainGhost) (c0 : BitVec 64)
          (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
          OptSenderChainCloneRel scG scM sender' ∧
          OptSenderChainInline sender' scM (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) ∧
          (P_f ⊢
            A.pool lim (M.stepEvents (optSenderChainCloneEvents scG scM) stB) s1 ∗
            stackAt s.sp chainCloneStack ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
            optSenderChainAt A.repAlloc (coroPtr + 0x188#64) scG scM ∗
            optSenderChainHeap A.repAlloc sender' scM ∗
            ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
            ((s.sp + 0x48#64) ↦₆₄ c0) ∗
            ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗
            genP3SenderInlineWords s.sp sq0 sq1 sq2 sq3 sq4 sq5) ∧
          s1.sp = s.sp ∧ s1.trace = s0.trace ∧ LibsignalCodeRoLoaded lsmpl s1.mem ∧
          s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x23 = s.readReg64 .x23 ∧
          s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
          s1.readReg64 .x27 = s.sp + 0x370#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp := by
  cases scG with
  | none =>
    cases scM with
    | none =>
      dsimp only [optSenderChainAt, optSenderChainCloneEvents]
      refine ret_sepWP_vm_pool_placed (A := A) (lim := lim) (st := stB) hcro
        (seg4_none_placed_wp_vm ext s coroPtr u_48 prevCounter u_5c hpc hrun hsp_align hx19)
        (by sep_focus)
        fun s1 _ _ hcro1 _
          ⟨hsp1, htr1, hx19_1, hx23_1, hx24_1, hx25_1, hx27_1, hx29_1, hvregs1⟩ => ?_
      let sq0 : BitVec 128 := u938 ++ u930
      let sq1 : BitVec 128 := u948 ++ u940
      let sq2 : BitVec 128 := u958 ++ u950
      let sq3 : BitVec 128 := u968 ++ u960
      let sq4 : BitVec 128 := u978 ++ u970
      let sq5 : BitVec 128 := u988 ++ u980
      refine ⟨none, noneCap, sq0, sq1, sq2, sq3, sq4, sq5, trivial,
        CryptoVerification.LibsignalTripleRatchet.RawByteMove.OptSenderChainInline.none_of_chunks96 sq0 sq1 sq2 sq3 sq4 sq5, ?_,
        hsp1, htr1.trans htr, hcro1,
        hx19_1, hx23_1, hx24_1, hx25_1, hx27_1.trans hx27, hx29_1, hvregs1⟩
      dsimp only [optSenderChainAt, optSenderChainHeap, genP3SenderInlineWords,
        LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl, sq0, sq1, sq2, sq3, sq4, sq5]
      simp only [cat128_lo, cat128_hi, emp_sepConj, sepConj_emp, sepConj_assoc]
      exact Entails.of_eq (by sep_ac_rfl)
    | some _ =>
      dsimp only [optSenderChainAt]
      exact sepWPp_pure_4th_any False.elim
  | some sg =>
    cases scM with
    | none =>
      dsimp only [optSenderChainAt]
      exact sepWPp_pure_4th_any False.elim
    | some sc =>
      dsimp only [optSenderChainCloneEvents] at hfits ⊢
      have hfits_env : FitsEnv M lim stB (SenderChainCloneEnv sg sc) :=
        fun _ hevs => hevs ▸ hfits
      refine sepWPp_weaken_pre_any
        (Entails.of_eq (by rw [optSenderChainAt_some_eq_cap A.repAlloc (coroPtr + 0x188#64) sg sc])) ?_
      simp only [sepConj_assoc]
      refine sepWPp_pure_4th_any fun ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ => ?_
      have hsc_ne : sg.srk.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hsrk_cap_lt
      refine bind_sepWP_vm_pool_placed (A := A) (lim := lim) (st := stB) hcro
        (seg4a1_placed_wp_vm ext s coroPtr sg.srk.cap prevCounter u_5c hsc_ne hpc hrun hsp_align hx19)
        (by sep_focus)
        fun s1 hpc1 hrun1 hcro1 _
          ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx29_1,
            hx30_1, hvregs1⟩ => ?_
      have hsp1_al : s1.spAligned = true := by
        change (s1.sp &&& 15#64 == 0#64) = true
        rw [hsp1]; exact hsp_align
      have hopt_reasm :
          (((coroPtr + 0x188#64) ↦₆₄ sg.srk.cap) ∗
            optSenderChainSomeRest A.repAlloc (coroPtr + 0x188#64) sg sc) ⊢
          optSenderChainAt A.repAlloc (coroPtr + 0x188#64) (some sg) (some sc) := by
        rw [optSenderChainAt_some_eq_cap A.repAlloc (coroPtr + 0x188#64) sg sc]
        exact Entails.pure_right ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ (Entails.refl _)
      refine sepWPp_weaken_frame_any hopt_reasm (by sep_focus) ?_
      refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1.call_lscl_nopanic_placed
        (spec := senderChainCloneSpec M A lim)
        (x := ((⟨s.sp + 0x3e0#64, coroPtr + 0x188#64, sg, sc⟩ : SenderChainCloneGhost), stB))
        (φ := s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x1 = coroPtr + 0x188#64 ∧
          FitsEnv M lim stB (SenderChainCloneEnv sg sc))
        (T := memRegion (s.sp + 0x3e0#64) 104 ∗
          optSenderChainAt A.repAlloc (coroPtr + 0x188#64) (some sg) (some sc) ∗
          A.pool lim stB s1 ∗ stackAt s1.sp chainCloneStack)
        hcro1 (senderChainClone3_at_518_budget ext hscc) hpc1 hrun1 hsp1_al hx30_1
        rfl ⟨hx0_1, hx1_1, hfits_env⟩ (by rw [hsp1]; sep_focus)
        (hnext := fun s2 hpc2 hrun2 hsp2 _ hcs2 hcro2 => ?_)
      dsimp only [senderChainCloneSpec]
      rw [sepExists_sepConj_left]
      refine sepWPp_exists_elim_any fun evs => ?_
      simp only [sepConj_assoc]
      refine sepWPp_pure_elim_any fun ⟨htr2, hevs⟩ => ?_
      change evs = senderChainCloneEvents sg sc at hevs
      subst hevs
      rw [sepExists_sepConj_left]
      refine sepWPp_exists_elim_any fun sg' => ?_
      simp only [sepConj_assoc]
      refine sepWPp_pure_elim_any fun ⟨hsrk', hpriv'⟩ => ?_
      have hsp2' : s2.sp = s.sp := hsp2.trans hsp1
      have hsp2_al : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2']; exact hsp_align
      have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2.1.trans hx19_1
      have hx22_2 : s2.readReg64 .x22 = s2.sp + 0x930#64 := by
        rw [hcs2.2.2.2.1, hx22_1, hx22, hsp2']
      have hx23_2 : s2.readReg64 .x23 = s.readReg64 .x23 := hcs2.2.2.2.2.1.trans hx23_1
      have hx24_2 : s2.readReg64 .x24 = s.readReg64 .x24 := hcs2.2.2.2.2.2.1.trans hx24_1
      have hx25_2 : s2.readReg64 .x25 = s.readReg64 .x25 := hcs2.2.2.2.2.2.2.1.trans hx25_1
      have hx27_2 : s2.readReg64 .x27 = s2.sp + 0x370#64 := by
        rw [hcs2.2.2.2.2.2.2.2.2.1, hx27_1, hx27, hsp2']
      have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 :=
        hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
      have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s :=
        hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
      refine sepWPp_weaken_pre_any
        (sepConj_mono_left
          (optSenderChainAt_entails_chunks104W6Q A.repAlloc (s.sp + 0x3e0#64) (some sg') (some sc))) ?_
      simp only [sepExists_sepConj_left]
      refine sepWPp_exists_elim_any fun c0 =>
        sepWPp_exists_elim_any fun sq0 => sepWPp_exists_elim_any fun sq1 =>
        sepWPp_exists_elim_any fun sq2 => sepWPp_exists_elim_any fun sq3 =>
        sepWPp_exists_elim_any fun sq4 => sepWPp_exists_elim_any fun sq5 => ?_
      simp only [sepConj_assoc]
      refine sepWPp_pure_elim_any fun hsc_inl => ?_
      rw [chunks104W6QAt_sp_0x3e0 s.sp c0 sq0 sq1 sq2 sq3 sq4 sq5]
      refine ret_sepWP_vm_pool_placed (A := A) (lim := lim)
        (st := M.stepEvents (senderChainCloneEvents sg sc) stB) hcro2
        (seg4a2_placed_wp_vm ext s2 coroPtr u_48
          c0 (sq0.extractLsb' 0 64) (sq0.extractLsb' 64 64)
          (sq1.extractLsb' 0 64) (sq1.extractLsb' 64 64)
          (sq2.extractLsb' 0 64) (sq2.extractLsb' 64 64)
          (sq3.extractLsb' 0 64) (sq3.extractLsb' 64 64)
          (sq4.extractLsb' 0 64) (sq4.extractLsb' 64 64)
          (sq5.extractLsb' 0 64) (sq5.extractLsb' 64 64)
          u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988
          hpc2 hrun2 hsp2_al hx19_2 hx22_2 hx27_2)
        (by simp only [hsp1, hsp2']; sep_focus)
        fun s3 _ _ hcro3 _ ⟨hsp3, htr3, hx19_3, hx23_3, hx24_3, hx25_3, hx27_3, hx29_3, hvregs3⟩ => ?_
      refine ⟨some sg', c0, sq0, sq1, sq2, sq3, sq4, sq5,
        ⟨hsrk', hpriv'⟩, hsc_inl, ?_,
        hsp3.trans hsp2', by rw [htr3, htr2, htr1, htr], hcro3,
        hx19_3, hx23_3.trans hx23_2, hx24_3.trans hx24_2, hx25_3.trans hx25_2,
        by rw [hx27_3, hsp2'], hx29_3.trans hx29_2, hvregs3.trans hvregs2⟩
      have h104 : ∀ R_tail : SepProp,
          ((s.sp + 0x3e0#64) ↦₆₄ c0) ∗
            ((s.sp + 0x3e8#64) ↦₆₄ sq0.extractLsb' 0 64) ∗
            ((s.sp + 0x3f0#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
            ((s.sp + 0x3f8#64) ↦₆₄ sq1.extractLsb' 0 64) ∗
            ((s.sp + 0x400#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
            ((s.sp + 0x408#64) ↦₆₄ sq2.extractLsb' 0 64) ∗
            ((s.sp + 0x410#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
            ((s.sp + 0x418#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
            ((s.sp + 0x420#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
            ((s.sp + 0x428#64) ↦₆₄ sq4.extractLsb' 0 64) ∗
            ((s.sp + 0x430#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
            ((s.sp + 0x438#64) ↦₆₄ sq5.extractLsb' 0 64) ∗
            ((s.sp + 0x440#64) ↦₆₄ sq5.extractLsb' 64 64) ∗ R_tail ⊢
          memRegion (s.sp + 0x3e0#64) 104 ∗ R_tail := by
        intro R_tail
        have h104_eq := congrArg (· ∗ R_tail)
          (chunks104W6QAt_sp_0x3e0 s.sp c0 sq0 sq1 sq2 sq3 sq4 sq5)
        simp only [sepConj_assoc] at h104_eq
        rw [← h104_eq]
        exact sepConj_mono_left (chunks104W6QAt_entails_memRegion _ _ _ _ _ _ _ _)
      let R_tail : SepProp :=
        A.pool lim (M.stepEvents (senderChainCloneEvents sg sc) stB) s3 ∗
          stackAt s.sp chainCloneStack ∗
          optSenderChainAt A.repAlloc (coroPtr + 0x188#64) (some sg) (some sc) ∗
          optSenderChainHeap A.repAlloc (some sg') (some sc) ∗
          ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
          ((s.sp + 0x48#64) ↦₆₄ c0) ∗
          ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗
          genP3SenderInlineWords s.sp sq0 sq1 sq2 sq3 sq4 sq5
      dsimp only [genP3SenderInlineWords] at *
      simp only [hsp1, hsp2', sepConj_assoc]
      exact Entails.trans
        (Entails.of_eq (by dsimp only [R_tail, genP3SenderInlineWords]; sep_ac_rfl))
        (Entails.trans (h104 R_tail)
          (Entails.of_eq (by dsimp only [R_tail, genP3SenderInlineWords]; sep_ac_rfl)))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudgetAux
