/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public meta import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

/-!
# File-Descriptor-Threaded `SegSave` Call Proof

Proves `segSave_call_placed_wp_fd` across `saveShim` and `IdSavePoll` (Block `565`, the final
`read_file` call in `MessageDecrypt`), consuming `ikit.fdsOk s.fs` at entry and matching the
post-cutoff postcondition of `SegSavePlacedBudget.segSave_call_placed_wp`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlacedBudgetFd

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open scoped LibsignalBinary.Proofs.Placed.BudgetVmSteps
open scoped LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
open CryptoGames.LibsignalSession (IdentityKey)
open CryptoGames.LibsignalSessionApi (IdentityChange)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsRustDeallocSym lsmpl)
open CryptoVerification.CliRatchet.DecPlaced (blkPC_463 blkPl_463 lsProg_463)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.LibsignalPublicApiRepr (storeHookStr)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsAt IdentityShimCall IdentityStoreSpec LibsignalCodeRoLoaded errTailPlacedAt
  savePollPlacedOutAt sepWP_seq_lscro sepWPp_seq_lscro
  subroutine_ok_withLsCodeRoLoaded_of_rocl withLsCodeRoLoaded withLsRoCl
)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt (saveCallPCPlaced)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
  (memRegion_36_entails_cells out_repack_sp saveCallStack savePollTag
   stack_alloc_to_saveCall stack_saveCall_to_saveShim stack_savePoll_to_alloc
   stack_saveShim_to_savePoll)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
  (box_lscro_463 pollOutPlacedRel shim_463)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
  (deallocBudget_463)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins
  (BoxAllocEnv BoxDeallocEnv SaveStepEnvDec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (IdentityStoreKitPlacedOkI)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (futDropBudgetSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

def toTwinsIdEnv_save {A : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b} (e : IdentityStoreBudgetEnv ikit) :
    SegSaveAuxPlacedBudget.TempTwins.IdentityStoreBudgetEnv ikit :=
  ⟨e.trustPollEnv, e.savePollEnv⟩

theorem futDropBudgetFd_463 [LibsignalPlacement] {H : LibsignalHooks} {off : BitVec 64}
    {fdsOk : FsState → Prop}
    (h : subroutine_ok (lsProg_463 H) (0#64 + off)
      (withLsRoCl lsmpl (futDropBudgetSpec fdsOk true))) :
    subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) off
      (withLsCodeRoLoaded lsmpl (futDropBudgetSpec fdsOk true)) := by
  rw [BitVec.zero_add] at h
  exact subroutine_ok_withLsCodeRoLoaded_of_rocl h

set_option maxHeartbeats 3200000 in
theorem segSave_call_placed_wp_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : IdentityStoreBudgetEnv ikit} {st : M.σ}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv H true)
    (hstack_lt : saveCallStack ikit ≤ 2 ^ 64)
    {s : State} {R : SepProp} {self addrA keyA : BitVec 64} {ist : ikit.IdState}
    {addr : AddrGhost} {k : IdentityKey} {c0 c1 d0 d1 d2 d3 : BitVec 64} {d5 : BitVec 32} {Q : Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfits : FitsEnv M lim st (SaveStepEnvDec ikit (toTwinsIdEnv_save ikitEnv) ist addr.val k))
    (haddr : ikit.addrOk addr.val)
    (hpc : s.pc = saveCallPCPlaced)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = keyA)
    (hfs : FsAt ikit.envOk Q (lsProg_463 H) s)
    (hfds : ikit.fdsOk s.fs) :
    SepWPp (lsProg_463 H) ((blkPl_463).base + 9088#64) s
      (((s.sp + 0xe8#64) ↦₆₄ addrA) ∗ ((s.sp + 0x108#64) ↦₆₄ self) ∗
        ((s.sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ ikit.saveShimOff) ∗
        (ikit.saveFutVtOff ↦₆₄ᵣ ikit.saveFutDropOff) ∗
        ((ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ ikit.savePollOff) ∗
        ikit.identityAt self ist ∗
        ((s.sp + 0x2d0#64) ↦₆₄ c0) ∗ ((s.sp + 0x2d8#64) ↦₆₄ c1) ∗
        ((s.sp + 0x520#64) ↦₆₄ d0) ∗ ((s.sp + 0x528#64) ↦₆₄ d1) ∗ ((s.sp + 0x530#64) ↦₆₄ d2) ∗
        ((s.sp + 0x538#64) ↦₆₄ d3) ∗ ((s.sp + 0x540#64) ↦₃₂ d5) ∗
        memRegion (s.sp + 0x5f0#64) 48 ∗
        lsLogOff ∗ protocolAddressAt A.repAlloc addr addrA ∗
        (keyA ↦ₛ k.publicKey.bytes.toList) ∗ A.pool lim st s ∗
        stackAt s.sp (saveCallStack ikit))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ evs : List AllocEvent, ∃∗ ans : Except Unit IdentityChange, ∃∗ box : BitVec 64,
          ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
          ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
          ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ⌜sf.readReg64 .x28 = savePollTag ans ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            ikit.saveRel ist addr.val k ans ∧
            sf.trace = s.trace ++ ikit.saveEvs addr.val k ans ∧
            pollOutPlacedRel strPtr vt o2 o3 o4 o5 o1 ans ∧
            SaveStepEnvDec ikit (toTwinsIdEnv_save ikitEnv) ist addr.val k evs⌝ ∗
          ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗ ((s.sp + 0x108#64) ↦₆₄ self) ∗
          ((s.sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
          ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ ikit.saveShimOff) ∗
          (ikit.saveFutVtOff ↦₆₄ᵣ ikit.saveFutDropOff) ∗
          ((ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
          ((ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ ikit.savePollOff) ∗
          ikit.identityAt self (ikit.saveUpdate ist addr.val k ans) ∗
          ((s.sp + 0x2d0#64) ↦₆₄ box) ∗ ((s.sp + 0x2d8#64) ↦₆₄ ikit.saveFutVtOff) ∗
          ((s.sp + 0x520#64) ↦₆₄ o2) ∗ ((s.sp + 0x528#64) ↦₆₄ o3) ∗
          ((s.sp + 0x530#64) ↦₆₄ o4) ∗ ((s.sp + 0x538#64) ↦₆₄ o5) ∗
          ((s.sp + 0x540#64) ↦₃₂ o6) ∗
          ((s.sp + 0x5f0#64) ↦₆₄ savePollTag ans) ∗ ((s.sp + 0x5f8#64) ↦₃₂ o1) ∗
          ((s.sp + 0x5fc#64) ↦₆₄ o2) ∗ ((s.sp + 0x604#64) ↦₆₄ o3) ∗
          ((s.sp + 0x60c#64) ↦₆₄ o4) ∗ ((s.sp + 0x614#64) ↦₆₄ o5) ∗
          ((s.sp + 0x61c#64) ↦₃₂ o6) ∗
          (if ans.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          lsLogOff ∗ protocolAddressAt A.repAlloc addr addrA ∗
          (keyA ↦ₛ k.publicKey.bytes.toList) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s.sp (saveCallStack ikit)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R)) := by
  have hshim := shim_463 (hikit.saveShim (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
  have hdrop := futDropBudgetFd_463 (hikit.saveFutDrop (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
  have hfits_sh : FitsEnv M lim st (BoxAllocEnv ikit.saveBoxSize) := hfits.seq_left
  unfold saveCallPCPlaced at hpc
  dsimp only [lsProg_463] at hfs ⊢
  have hdealloc := deallocBudget_463 hdealloc_sat
  refine SepWPp.congr_pre (by rw [stack_saveCall_to_saveShim ikit s.sp hstack_lt]) ?_
  apply sepWPp_seq_lscro (mid := ikit.saveShimOff) hcrl
  clear hcrl
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
    intro hvm1 hcrl1
    refine SepWPp.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
    cli_messageDecrypt_call_panic_p_budget_lscro hshim hcrl1 ((⟨self, addrA, keyA⟩ : IdentityShimCall), st)
    clear hcrl1 hshim hfds
    apply sepWPp_seq_lscro (mid := ikit.savePollOff) hcrl_sf
    clear hcrl_sf
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro (evs_sh : List AllocEvent)
    wp_simp_pre [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hsteps_sh, hx1_sf, hx0_ne, hx0_al, htr_sf, hevs_sh, hfds_sh⟩
    have hfits_rem := hfits.seq_right hevs_sh
    have hfits_pl : FitsEnv M lim (M.stepEvents evs_sh st) (ikitEnv.savePollEnv ist addr.val k) :=
      hfits_rem.seq_left
    have henv : ikit.envOk sf.fs.files :=
      (hfs.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
    clear hsteps_sh hfs
    apply SepWP.fold (Entails.of_eq (stack_saveShim_to_savePoll ikit s.sp hstack_lt)) (by sep_focus)
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm2 hcrl2
      refine SepWPp.transport_budgetPool hvm2 (hnext := ?_); clear hvm2
      have hpoll := box_lscro_463 (hikit.savePoll (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
      cli_messageDecrypt_call_panic_budget_lscro hpoll hcrl2
        (⟨sf.readReg64 (Reg.gpr 0#5), s.sp + 1520#64, ⟨addrA, addr, keyA, k⟩⟩, self, ist, M.stepEvents evs_sh st)
      clear hcrl2 hpoll hikit
      generalize hbox : sf.readReg64 (Reg.gpr 0#5) = box at *
      simp only [hsp_sf] at hsp_sf_1 ⊢
      have hdz : ikit.saveFutDropOff ≠ 0#64 := by
        simpa only [BitVec.zero_add] using ikit.saveFutDrop_ne_zero (by decide)
      have hdz' : (ikit.saveFutDropOff == 0#64) = false := beq_eq_false_iff_ne.mpr hdz
      have hbs := ikit.saveBoxSize_ne_zero
      have hbs' : (BitVec.ofNat 64 ikit.saveBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs
      have hbs_pos : 0 < ikit.saveBoxSize := Nat.pos_of_ne_zero (fun h => hbs (by simp [h]))
      have hbs_toNat : (BitVec.ofNat 64 ikit.saveBoxSize).toNat = ikit.saveBoxSize :=
        Nat.mod_eq_of_lt ikit.saveBoxSize_lt
      have hevs_dealloc : BoxDeallocEnv ikit.saveBoxSize (rustDeallocEvents ikit.saveBoxSize 8) :=
        Or.inr ⟨hbs_pos, rfl⟩
      apply SepWP.fold (A.block_valid box ikit.saveBoxSize 8) (by sep_focus)
      wp_simp_pre [sepConj_assoc, sepConj_pure_left_comm]
      apply SepWP.pure_elim; rintro ⟨_, _, _, ⟨_, hpow8, hbound_box⟩, _⟩
      rcases w with ⟨⟨⟩⟩ | c
      · dsimp only [savePollPlacedOutAt]
        wp_simp_pre [errTailPlacedAt, ProofLib.memRegion_eight,
          sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
        apply SepWP.exists_elim; intro (strPtr : BitVec 64)
        apply SepWP.exists_elim; intro (vt : BitVec 64)
        apply SepWP.exists_elim; intro (w5 : BitVec 64)
        apply SepWP.fold
          (Entails.of_eq (out_repack_sp s.sp strPtr 10#64 1#64 vt w5))
          (by sep_focus)
        apply sepWP_seq_lscro hcrl_poll (mid := ikit.saveFutDropOff)
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          rintro hvm3 ⟨hcl_d, hro_d⟩
          refine SepWP.transport_budgetPool hvm3 (hnext := ?_); clear hvm3
          wp_call hdrop ()
          refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
          wp_steps
          apply SepWP.fold (ikit.saveBoxAt_memRegion box self addrA keyA 1#8) (by sep_focus)
          apply SepWP.fold (Entails.of_eq (stack_savePoll_to_alloc ikit s.sp hstack_lt)) (by sep_focus)
          wp_call hdealloc (box, ikit.saveBoxSize, 8, M.stepEvents w_1 (M.stepEvents evs_sh st))
          have hsp_sf2 : sf_2.sp = s.sp := by simp_all
          rw [hsp_sf2]
          apply SepWP.fold (Entails.of_eq (stack_alloc_to_saveCall ikit s.sp hstack_lt)) (by sep_focus)
          simp only [show (9223372036854775834#64 : BitVec 64) = savePollTag (.error ()) from rfl] at *
          apply SepWP.done (by simp_all) (by simp_all)
          refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
          refine Entails.sepExists_right (evs_sh ++ (w_1 ++ rustDeallocEvents ikit.saveBoxSize 8))
            (Entails.sepExists_right (.error ())
            (Entails.sepExists_right box
            (Entails.sepExists_right strPtr
            (Entails.sepExists_right vt
            (Entails.sepExists_right (strPtr.extractLsb' 0 32)
            (Entails.sepExists_right (10#32 ++ strPtr.extractLsb' 32 32)
            (Entails.sepExists_right 4294967296#64
            (Entails.sepExists_right (vt.extractLsb' 0 32 ++ 0#32)
            (Entails.sepExists_right (w5.extractLsb' 0 32 ++ vt.extractLsb' 32 32)
            (Entails.sepExists_right (w5.extractLsb' 32 32) ?_))))))))))
          have henv_step : SaveStepEnvDec ikit (toTwinsIdEnv_save ikitEnv) ist addr.val k
              (evs_sh ++ (w_1 ++ rustDeallocEvents ikit.saveBoxSize 8)) :=
            SeqEnv.append hevs_sh (SeqEnv.append (by simp_all [toTwinsIdEnv_save]) hevs_dealloc)
          refine Entails.pure_right (by simp_all [henv_step]) ?_
          dsimp only [Except.isOk, Except.toBool]
          simp only [Bool.false_eq_true, ↓reduceIte, ← M.stepEvents_append, List.append_assoc]
          exact Entails.of_eq (by sep_ac_rfl))
      · dsimp only [savePollPlacedOutAt]
        apply SepWP.fold (memRegion_36_entails_cells (s.sp + 1520#64 + 0xc#64)) (by sep_focus)
        wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
          BitVec.add_assoc, BitVec.reduceAdd]
        apply SepWP.exists_elim; intro (o2 : BitVec 64)
        apply SepWP.exists_elim; intro (o3 : BitVec 64)
        apply SepWP.exists_elim; intro (o4 : BitVec 64)
        apply SepWP.exists_elim; intro (o5 : BitVec 64)
        apply SepWP.exists_elim; intro (o6 : BitVec 32)
        apply sepWP_seq_lscro hcrl_poll (mid := ikit.saveFutDropOff)
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          rintro hvm3 ⟨hcl_d, hro_d⟩
          refine SepWP.transport_budgetPool hvm3 (hnext := ?_); clear hvm3
          wp_call hdrop ()
          refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
          wp_steps
          apply SepWP.fold (ikit.saveBoxAt_memRegion box self addrA keyA 1#8) (by sep_focus)
          apply SepWP.fold (Entails.of_eq (stack_savePoll_to_alloc ikit s.sp hstack_lt)) (by sep_focus)
          wp_call hdealloc (box, ikit.saveBoxSize, 8, M.stepEvents w_1 (M.stepEvents evs_sh st))
          have hsp_sf2 : sf_2.sp = s.sp := by simp_all
          rw [hsp_sf2]
          apply SepWP.fold (Entails.of_eq (stack_alloc_to_saveCall ikit s.sp hstack_lt)) (by sep_focus)
          simp only [show (bv% (2 ^ 64 - 2) : BitVec 64) = savePollTag (.ok c) from rfl] at *
          apply SepWP.done (by simp_all) (by simp_all)
          refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
          refine Entails.sepExists_right (evs_sh ++ (w_1 ++ rustDeallocEvents ikit.saveBoxSize 8))
            (Entails.sepExists_right (.ok c)
            (Entails.sepExists_right box
            (Entails.sepExists_right 0#64
            (Entails.sepExists_right 0#64
            (Entails.sepExists_right (if c = .replacedExisting then 1#32 else 0#32)
            (Entails.sepExists_right o2
            (Entails.sepExists_right o3
            (Entails.sepExists_right o4
            (Entails.sepExists_right o5
            (Entails.sepExists_right o6 ?_))))))))))
          have henv_step : SaveStepEnvDec ikit (toTwinsIdEnv_save ikitEnv) ist addr.val k
              (evs_sh ++ (w_1 ++ rustDeallocEvents ikit.saveBoxSize 8)) :=
            SeqEnv.append hevs_sh (SeqEnv.append (by simp_all [toTwinsIdEnv_save]) hevs_dealloc)
          refine Entails.pure_right (by simp_all [henv_step]) ?_
          dsimp only [Except.isOk, Except.toBool]
          simp only [↓reduceIte, emp_sepConj, ← M.stepEvents_append, List.append_assoc]
          exact Entails.of_eq (by sep_ac_rfl))))

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlacedBudgetFd
