/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegTrustPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlacedBudgetFd
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public meta import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Heap.IfaceLemmas
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# File-Descriptor-Threaded `SegTrust` Call and Tail Proofs

Threads `ikit.fdsOk` across `trustShim`, `trustPoll`, `trustFutDrop`, and `dealloc`, preserving
`sf.fs = s.fs` across the `true` and `false` tails so `FdsGe3Closed` reaches `SegSave`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegTrustPlacedBudgetFd

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open scoped LibsignalBinary.Proofs.Placed.BudgetVmSteps
open scoped LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
open CryptoGames.LibsignalSession (IdentityKey)
open CryptoGames.LibsignalSessionApi (Direction)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsRustDeallocSym ls_externAt?_of_mem lsmpl lsρ)
open CryptoVerification.CliRatchet.DecPlaced (blkPC_463 blkPl_463 lsProg_463)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApiRepr (directionByte storeHookStr)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsAt IdentityShimCall IdentityStoreSpec)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
  (keyReadyPCPlaced saveCallPCPlaced trustedPCPlaced untrustedPCPlaced)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave (out_repack_sp)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
  (box_lscro_463 pollOutPlacedRel_err shim_463)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
  (memRegion_39_entails_cells_sp pointsTo32_split_1_2_1_sp stack_alloc_to_trustCall
   stack_trustCall_to_trustShim stack_trustPoll_to_alloc stack_trustShim_to_trustPoll
   trustCallStack trustPollTag)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust (trustPollOutPlacedRel)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FdsHiFrame FitsEnv RustCliAllocBudget
   RustLayoutOk SeqEnv VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliDeallocBudgetSpecWithStack subroutine_ok_deallocBudget_withStack_of_hookSat)
open LibsignalBinary.Heap.IfaceLemmas (subroutine_ok_frame_oom')
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins
  (BoxAllocEnv BoxDeallocEnv TrustStepEnvDec)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlacedBudgetFd
  (futDropBudgetFd_463 toTwinsIdEnv_save)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (IdentityStoreKitPlacedOkI)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private def deallocBudgetExternSpecFds [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := 16384) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := fun (p, size, align, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧
      (s.readReg64 .x2).toNat = align ∧ RustLayoutOk size align ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.live p size align ∗ memRegion p size ∗ stackAt s.sp stk
  post := fun (_, size, align, st) s0 sf =>
    let st' := M.stepEvents (rustDeallocEvents size align) st
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗ A.pool lim st' sf ∗ stackAt s0.sp stk
  onOom := fun _ _ _ => ⌜False⌝

private theorem deallocBudgetFd_463 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hsat : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsρ lsRustDeallocSym)
      (deallocBudgetExternSpecFds M A lim allocHookStack) := by
  refine subroutine_ok_frame_oom' (fun _ _ => emp)
    (subroutine_ok_deallocBudget_withStack_of_hookSat (stk := allocHookStack) hsat
      (ls_externAt?_of_mem (prog := (blkPC_463).rebase (blkPl_463).base H)
        (i := 463) (sym := lsRustDeallocSym) (by decide))) ?_ ?_
  · rintro ⟨p, size, align, st⟩ s0
    dsimp only [rustCliDeallocBudgetSpecWithStack, deallocBudgetExternSpecFds]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨h0, h1, h2, _hl, hlr⟩ =>
      Entails.pure_right ⟨h0, h1, h2, hlr⟩ (Entails.refl _)
  · rintro ⟨p, size, align, st⟩ s0 sf
    dsimp only [rustCliDeallocBudgetSpecWithStack, deallocBudgetExternSpecFds]
    rw [sepConj_emp]
    exact Entails.pure_left fun ⟨hacp, _⟩ =>
      Entails.pure_right ⟨hacp.2.1, hacp.1⟩ (Entails.refl _)

set_option maxHeartbeats 3200000 in
theorem segTrust_call_placed_wp_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : IdentityStoreBudgetEnv ikit} {st : M.σ}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv H true)
    (hstack_lt : trustCallStack ikit ≤ 2 ^ 64)
    {s : State} {R : SepProp}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    {self addrA c0 c1 d0 d1 d2 d3 k0 k1 k2 k3 a0 a1 a2 a3 : BitVec 64} {d5 : BitVec 32}
    {ist : ikit.IdState} {addr : AddrGhost} {k : IdentityKey} {Q : Prop}
    (hfits : FitsEnv M lim st (TrustStepEnvDec ikit (toTwinsIdEnv_save ikitEnv) ist addr.val k))
    (haddr : ikit.addrOk addr.val)
    (hpc : s.pc = keyReadyPCPlaced)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hk_2a8 :
      (((s.sp + 0x2a8#64) ↦₆₄ k0) ∗ ((s.sp + 0x2b0#64) ↦₆₄ k1) ∗
        ((s.sp + 0x2b8#64) ↦₆₄ k2) ∗ ((s.sp + 0x2c0#64) ↦₆₄ k3)) =
        ((s.sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList))
    (hfs : FsAt ikit.envOk Q (lsProg_463 H) s)
    (hfds : ikit.fdsOk s.fs)
    (hfds_mono : ∀ ⦃s₁ s₂ : State⦄, FdsHiFrame s₁ s₂ → ikit.fdsOk s₁.fs → ikit.fdsOk s₂.fs) :
    SepWPp (lsProg_463 H) ((blkPl_463).base + 8516#64) s
      (((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
        ((s.sp + 0x108#64) ↦₆₄ self) ∗
        ((s.sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
        ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ ikit.trustShimOff) ∗
        (ikit.trustFutVtOff ↦₆₄ᵣ ikit.trustFutDropOff) ∗
        ((ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
        ((ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ ikit.trustPollOff) ∗
        ikit.identityAt self ist ∗
        ((s.sp + 0x2a8#64) ↦₆₄ a0) ∗ ((s.sp + 0x2b0#64) ↦₆₄ a1) ∗
        ((s.sp + 0x2b8#64) ↦₆₄ a2) ∗ ((s.sp + 0x2c0#64) ↦₆₄ a3) ∗
        ((s.sp + 0x2d0#64) ↦₆₄ c0) ∗ ((s.sp + 0x2d8#64) ↦₆₄ c1) ∗
        ((s.sp + 0x4f0#64) ↦₆₄ d0) ∗ ((s.sp + 0x4f8#64) ↦₆₄ d1) ∗
        ((s.sp + 0x500#64) ↦₆₄ d2) ∗ ((s.sp + 0x508#64) ↦₆₄ d3) ∗
        ((s.sp + 0x510#64) ↦₃₂ d5) ∗
        memRegion (s.sp + 0x5f0#64) 48 ∗
        ((s.sp + 0xca0#64) ↦₆₄ k0) ∗ ((s.sp + 0xca8#64) ↦₆₄ k1) ∗
        ((s.sp + 0xcb0#64) ↦₆₄ k2) ∗ ((s.sp + 0xcb8#64) ↦₆₄ k3) ∗
        FromRecordCallees.lsLogOff ∗ protocolAddressAt A.repAlloc addr addrA ∗ A.pool lim st s ∗
        stackAt s.sp (trustCallStack ikit))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ evs : List AllocEvent, ∃∗ ans : Except Unit Bool,
          ∃∗ box : BitVec 64, ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
          ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
          ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ∃∗ b0 : BitVec 8, ∃∗ b3 : BitVec 8, ∃∗ h1 : BitVec 16,
          ⌜sf.readReg64 .x28 = trustPollTag ans ∧
            sf.readReg64 .x21 = b0.zeroExtend 64 ∧
            sf.readReg64 .x23 = b3.zeroExtend 64 ∧
            sf.readReg64 .x24 = h1.zeroExtend 64 ∧
            ikit.trustRel ist addr.val k .receiving ans ∧
            sf.trace = s.trace ++ ikit.trustEvs addr.val k .receiving ans ∧
            trustPollOutPlacedRel strPtr vt o2 o3 o4 o5 b0 b3 h1 ans ∧
            TrustStepEnvDec ikit (toTwinsIdEnv_save ikitEnv) ist addr.val k evs⌝ ∗
          ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
          ((s.sp + 0x108#64) ↦₆₄ self) ∗
          ((s.sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
          ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ ikit.trustShimOff) ∗
          (ikit.trustFutVtOff ↦₆₄ᵣ ikit.trustFutDropOff) ∗
          ((ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
          ((ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ ikit.trustPollOff) ∗
          ikit.identityAt self (ikit.trustUpdate ist addr.val k .receiving ans) ∗
          ((s.sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
          ((s.sp + 0x2d0#64) ↦₆₄ box) ∗ ((s.sp + 0x2d8#64) ↦₆₄ ikit.trustFutVtOff) ∗
          ((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
          ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
          ((s.sp + 0x510#64) ↦₃₂ o6) ∗
          ((s.sp + 0x5f0#64) ↦₆₄ trustPollTag ans) ∗
          ((s.sp + 0x5f8#64) ↦₈ b0) ∗ ((s.sp + 0x5f9#64) ↦₁₆ h1) ∗
          ((s.sp + 0x5fb#64) ↦₈ b3) ∗
          ((s.sp + 0x5fc#64) ↦₆₄ o2) ∗ ((s.sp + 0x604#64) ↦₆₄ o3) ∗
          ((s.sp + 0x60c#64) ↦₆₄ o4) ∗ ((s.sp + 0x614#64) ↦₆₄ o5) ∗
          ((s.sp + 0x61c#64) ↦₃₂ o6) ∗
          ((s.sp + 0xca0#64) ↦₆₄ k0) ∗ ((s.sp + 0xca8#64) ↦₆₄ k1) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ k2) ∗ ((s.sp + 0xcb8#64) ↦₆₄ k3) ∗
          (if ans.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          FromRecordCallees.lsLogOff ∗ protocolAddressAt A.repAlloc addr addrA ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s.sp (trustCallStack ikit)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x19 = s.sp + 0x2a8#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        ikit.fdsOk sf.fs)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R)) := by
  have hshim := shim_463 (hikit.trustShim (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
  have hdrop := futDropBudgetFd_463 (hikit.trustFutDrop (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
  have hfits_sh : FitsEnv M lim st (BoxAllocEnv ikit.trustBoxSize) := hfits.seq_left
  unfold keyReadyPCPlaced at hpc
  dsimp only [lsProg_463] at hfs ⊢
  have hdealloc := deallocBudgetFd_463 hdealloc_sat
  refine SepWPp.congr_pre (by rw [stack_trustCall_to_trustShim ikit s.sp hstack_lt]) ?_
  apply StoreKit.sepWPp_seq_lscro (mid := ikit.trustShimOff) hcrl
  clear hcrl
  by_vm_open (
    wp_steps
    apply SepWP.fold (Entails.of_eq hk_2a8) (by sep_focus)
    refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
    intro hvm1 hcrl1
    refine SepWPp.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
    cli_messageDecrypt_call_panic_p_budget_lscro hshim hcrl1
      ((⟨self, addrA, s.sp + 680#64⟩ : IdentityShimCall), 1#8, st)
    clear hcrl1 hshim hfds
    apply StoreKit.sepWPp_seq_lscro (mid := ikit.trustPollOff) hcrl_sf
    clear hcrl_sf
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro (evs_sh : List AllocEvent)
    wp_simp_pre [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hsteps_sh, hx1_sf, hx0_ne, hx0_al, htr_sf, hevs_sh, hfds_sh⟩
    have hfits_rem := hfits.seq_right hevs_sh
    have hfits_pl : FitsEnv M lim (M.stepEvents evs_sh st)
        (ikitEnv.trustPollEnv ist addr.val k .receiving) := hfits_rem.seq_left
    have henv : ikit.envOk sf.fs.files :=
      (hfs.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
    clear hsteps_sh hfs
    apply SepWP.fold (Entails.of_eq (stack_trustShim_to_trustPoll ikit s.sp hstack_lt)) (by sep_focus)
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm2 hcrl2
      refine SepWPp.transport_budgetPool hvm2 (hnext := ?_); clear hvm2
      have hpoll := box_lscro_463 (hikit.trustPoll (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
      cli_messageDecrypt_call_panic_budget_lscro hpoll hcrl2
        (⟨sf.readReg64 (Reg.gpr 0#5), s.sp + 1520#64, ⟨addrA, addr, s.sp + 680#64, k⟩⟩,
          Direction.receiving, self, ist, M.stepEvents evs_sh st)
      clear hcrl2 hpoll hikit hfds_sh
      generalize hbox : sf.readReg64 (Reg.gpr 0#5) = box at *
      simp only [hsp_sf] at hsp_sf_1 ⊢
      have hdz : ikit.trustFutDropOff ≠ 0#64 := by
        simpa only [BitVec.zero_add] using ikit.trustFutDrop_ne_zero (by decide)
      have hdz' : (ikit.trustFutDropOff == 0#64) = false := beq_eq_false_iff_ne.mpr hdz
      have hbs := ikit.trustBoxSize_ne_zero
      have hbs' : (BitVec.ofNat 64 ikit.trustBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs
      have hbs_pos : 0 < ikit.trustBoxSize := Nat.pos_of_ne_zero (fun h => hbs (by simp [h]))
      have hbs_toNat : (BitVec.ofNat 64 ikit.trustBoxSize).toNat = ikit.trustBoxSize :=
        Nat.mod_eq_of_lt ikit.trustBoxSize_lt
      have hevs_dealloc : BoxDeallocEnv ikit.trustBoxSize (rustDeallocEvents ikit.trustBoxSize 8) :=
        Or.inr ⟨hbs_pos, rfl⟩
      apply SepWP.fold (A.block_valid box ikit.trustBoxSize 8) (by sep_focus)
      wp_simp_pre [sepConj_assoc, sepConj_pure_left_comm]
      apply SepWP.pure_elim; rintro ⟨_, _, _, ⟨_, hpow8, hbound_box⟩, _⟩
      rcases w with ⟨⟨⟩⟩ | t
      · dsimp only [StoreKit.trustPollPlacedOutAt]
        wp_simp_pre [StoreKit.errTailPlacedAt, ProofLib.memRegion_eight,
          sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
        apply SepWP.exists_elim; intro (strPtr : BitVec 64)
        apply SepWP.exists_elim; intro (vt : BitVec 64)
        apply SepWP.exists_elim; intro (w5 : BitVec 64)
        apply SepWP.fold
          (Entails.of_eq (out_repack_sp s.sp strPtr 10#64 1#64 vt w5))
          (by sep_focus)
        apply SepWP.fold
          (Entails.of_eq (pointsTo32_split_1_2_1_sp s.sp (strPtr.extractLsb' 0 32)))
          (by sep_focus)
        apply StoreKit.sepWP_seq_lscro hcrl_poll (mid := ikit.trustFutDropOff)
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          rintro hvm3 ⟨hcl_d, hro_d⟩
          have hfds_d : ikit.fdsOk _ := hfds_mono hvm3.fdsHiFrame (by assumption)
          refine SepWP.transport_budgetPool hvm3 (hnext := ?_); clear hvm3
          wp_call hdrop ()
          refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
          wp_steps
          apply SepWP.fold (ikit.trustBoxAt_memRegion box self addrA (s.sp + 680#64) 1#8 (directionByte .receiving)) (by sep_focus)
          apply SepWP.fold (Entails.of_eq (stack_trustPoll_to_alloc ikit s.sp hstack_lt)) (by sep_focus)
          wp_call hdealloc (box, ikit.trustBoxSize, 8, M.stepEvents w_1 (M.stepEvents evs_sh st))
          have hsp_sf2 : sf_2.sp = s.sp := by simp_all
          rw [hsp_sf2]
          apply SepWP.fold (Entails.of_eq (stack_alloc_to_trustCall ikit s.sp hstack_lt)) (by sep_focus)
          simp only [show (0x800000000000001A#64 : BitVec 64) = trustPollTag (.error ()) from rfl] at *
          apply SepWP.done (by simp_all) (by simp_all)
          refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final,
            by simp_all [AllocCallPreserved, wp_norm, arm64_norm]⟩
          refine Entails.sepExists_right (evs_sh ++ (w_1 ++ rustDeallocEvents ikit.trustBoxSize 8))
            (Entails.sepExists_right (.error ())
            (Entails.sepExists_right box
            (Entails.sepExists_right strPtr
            (Entails.sepExists_right vt
            (Entails.sepExists_right (10#32 ++ strPtr.extractLsb' 32 32)
            (Entails.sepExists_right 4294967296#64
            (Entails.sepExists_right (vt.extractLsb' 0 32 ++ 0#32)
            (Entails.sepExists_right (w5.extractLsb' 0 32 ++ vt.extractLsb' 32 32)
            (Entails.sepExists_right (w5.extractLsb' 32 32)
            (Entails.sepExists_right ((strPtr.extractLsb' 0 32).extractLsb' 0 8)
            (Entails.sepExists_right ((strPtr.extractLsb' 0 32).extractLsb' 24 8)
            (Entails.sepExists_right ((strPtr.extractLsb' 0 32).extractLsb' 8 16) ?_))))))))))))
          have henv_step : TrustStepEnvDec ikit (toTwinsIdEnv_save ikitEnv) ist addr.val k
              (evs_sh ++ (w_1 ++ rustDeallocEvents ikit.trustBoxSize 8)) :=
            SeqEnv.append hevs_sh (SeqEnv.append (by simp_all [toTwinsIdEnv_save]) hevs_dealloc)
          refine Entails.pure_right ⟨by simp_all, by simp_all; bv_bits, by simp_all; bv_bits,
            by simp_all, by simp_all, by simp_all,
            ⟨by bv_bits, by bv_bits, by bv_bits, pollOutPlacedRel_err strPtr vt w5⟩, henv_step⟩ ?_
          dsimp only [Except.isOk, Except.toBool]
          simp only [Bool.false_eq_true, ↓reduceIte, ← M.stepEvents_append, List.append_assoc]
          exact Entails.of_eq (by sep_ac_rfl))
      · dsimp only [StoreKit.trustPollPlacedOutAt]
        wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd]
        apply SepWP.fold (memRegion_39_entails_cells_sp s.sp) (by sep_focus)
        wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro (h1 : BitVec 16)
        apply SepWP.exists_elim; intro (b3 : BitVec 8)
        apply SepWP.exists_elim; intro (o2 : BitVec 64)
        apply SepWP.exists_elim; intro (o3 : BitVec 64)
        apply SepWP.exists_elim; intro (o4 : BitVec 64)
        apply SepWP.exists_elim; intro (o5 : BitVec 64)
        apply SepWP.exists_elim; intro (o6 : BitVec 32)
        apply StoreKit.sepWP_seq_lscro hcrl_poll (mid := ikit.trustFutDropOff)
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          rintro hvm3 ⟨hcl_d, hro_d⟩
          have hfds_d : ikit.fdsOk _ := hfds_mono hvm3.fdsHiFrame (by assumption)
          refine SepWP.transport_budgetPool hvm3 (hnext := ?_); clear hvm3
          wp_call hdrop ()
          refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
          wp_steps
          apply SepWP.fold (ikit.trustBoxAt_memRegion box self addrA (s.sp + 680#64) 1#8 (directionByte .receiving)) (by sep_focus)
          apply SepWP.fold (Entails.of_eq (stack_trustPoll_to_alloc ikit s.sp hstack_lt)) (by sep_focus)
          wp_call hdealloc (box, ikit.trustBoxSize, 8, M.stepEvents w_1 (M.stepEvents evs_sh st))
          have hsp_sf2 : sf_2.sp = s.sp := by simp_all
          rw [hsp_sf2]
          apply SepWP.fold (Entails.of_eq (stack_alloc_to_trustCall ikit s.sp hstack_lt)) (by sep_focus)
          have henv_step : TrustStepEnvDec ikit (toTwinsIdEnv_save ikitEnv) ist addr.val k
              (evs_sh ++ (w_1 ++ rustDeallocEvents ikit.trustBoxSize 8)) :=
            SeqEnv.append hevs_sh (SeqEnv.append (by simp_all [toTwinsIdEnv_save]) hevs_dealloc)
          cases t
          · simp only [Bool.false_eq_true, ↓reduceIte,
              show (bv% (2 ^ 64 - 2) : BitVec 64) = trustPollTag (.ok false) from rfl] at *
            apply SepWP.done (by simp_all) (by simp_all)
            refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final,
              by simp_all [AllocCallPreserved, wp_norm, arm64_norm]⟩
            refine Entails.sepExists_right (evs_sh ++ (w_1 ++ rustDeallocEvents ikit.trustBoxSize 8))
              (Entails.sepExists_right (.ok false)
              (Entails.sepExists_right box
              (Entails.sepExists_right 0#64
              (Entails.sepExists_right 0#64
              (Entails.sepExists_right o2
              (Entails.sepExists_right o3
              (Entails.sepExists_right o4
              (Entails.sepExists_right o5
              (Entails.sepExists_right o6
              (Entails.sepExists_right 0#8
              (Entails.sepExists_right b3
              (Entails.sepExists_right h1 ?_))))))))))))
            refine Entails.pure_right (by simp_all [henv_step]) ?_
            dsimp only [Except.isOk, Except.toBool]
            simp only [↓reduceIte, emp_sepConj, ← M.stepEvents_append, List.append_assoc]
            exact Entails.of_eq (by sep_ac_rfl)
          · simp only [↓reduceIte,
              show (bv% (2 ^ 64 - 2) : BitVec 64) = trustPollTag (.ok true) from rfl] at *
            apply SepWP.done (by simp_all) (by simp_all)
            refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final,
              by simp_all [AllocCallPreserved, wp_norm, arm64_norm]⟩
            refine Entails.sepExists_right (evs_sh ++ (w_1 ++ rustDeallocEvents ikit.trustBoxSize 8))
              (Entails.sepExists_right (.ok true)
              (Entails.sepExists_right box
              (Entails.sepExists_right 0#64
              (Entails.sepExists_right 0#64
              (Entails.sepExists_right o2
              (Entails.sepExists_right o3
              (Entails.sepExists_right o4
              (Entails.sepExists_right o5
              (Entails.sepExists_right o6
              (Entails.sepExists_right 1#8
              (Entails.sepExists_right b3
              (Entails.sepExists_right h1 ?_))))))))))))
            refine Entails.pure_right (by simp_all [henv_step]) ?_
            dsimp only [Except.isOk, Except.toBool]
            simp only [↓reduceIte, emp_sepConj, ← M.stepEvents_append, List.append_assoc]
            exact Entails.of_eq (by sep_ac_rfl))))

theorem segTrust_tail_placed_ok_true_fs [LibsignalPlacement] {H : LibsignalHooks}
    {s : State} {R : SepProp}
    (hpc : s.pc = (blkPl_463).base + 8516#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = trustPollTag (.ok true))
    (hx21 : s.readReg64 .x21 = (1#8 : BitVec 8).zeroExtend 64) :
    SepWP (lsProg_463 H) (trustedPCPlaced true) s
      emp
      (fun sf P_f => VmPreserved s sf ∧ ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ emp ∗ R)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.fs = s.fs ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold trustedPCPlaced saveCallPCPlaced
  dsimp only [lsProg_463]
  simp only [trustPollTag] at hx28
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all)
      ⟨by simp only [wp_norm, arm64_norm], fun hvm =>
        ⟨hvm, fun hm => hm, by simp_all [wp_norm, arm64_norm],
          by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
          by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
          by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
          by simp_all [wp_norm, arm64_norm], by simp_all [calleeSavedVRegs, wp_norm, arm64_norm]⟩⟩)

theorem segTrust_tail_placed_ok_false_fs [LibsignalPlacement] {H : LibsignalHooks}
    {s : State} {R : SepProp}
    (hpc : s.pc = (blkPl_463).base + 8516#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = trustPollTag (.ok false))
    (hx21 : s.readReg64 .x21 = (0#8 : BitVec 8).zeroExtend 64) :
    SepWP (lsProg_463 H) (trustedPCPlaced false) s
      emp
      (fun sf P_f => VmPreserved s sf ∧ ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ emp ∗ R)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.fs = s.fs ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  simp only [trustedPCPlaced, Bool.false_eq_true, ↓reduceIte, untrustedPCPlaced]
  dsimp only [lsProg_463]
  simp only [trustPollTag] at hx28
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all)
      ⟨by simp only [wp_norm, arm64_norm], fun hvm =>
        ⟨hvm, fun hm => hm, by simp_all [wp_norm, arm64_norm],
          by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
          by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
          by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
          by simp_all [wp_norm, arm64_norm], by simp_all [calleeSavedVRegs, wp_norm, arm64_norm]⟩⟩)

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegTrustPlacedBudgetFd
