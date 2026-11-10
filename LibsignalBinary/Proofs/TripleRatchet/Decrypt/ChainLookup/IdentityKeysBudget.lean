/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSymBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysStepsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeys
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainStack
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.RegChain
import ProofLib.SepLogic.WP.Apply
meta import ProofLib.SepLogic.WP.Apply -- shake: keep

/-!
# Budget-Threaded Segment S0 (`IdentityKeys`) & Pre-Key Callee Contracts

Re-exports budget-threaded `SessionState::remote_identity_key` (block `29`), verifies
`SessionState::clear_unacknowledged_pre_key_message` (block `35`), and proves the relocatable
Segment S0 seams (`identityKeys_placed_ok`, `S0SeamPlaced`, `S0SeamXPlaced`) on block `130` over
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SessionState)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded
   lsBlackBoxU8Sym lsRustDeallocSym ls_hook_ok_of_mem ls_subroutine_ok_of_block
   lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.RustHeap
  (RustAlloc allocHookStack vecAt vecHeader vecU8At vecU8At_entails_dealloc)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalSessionRepr
  (chainAt msgTypeByte vecGhostAt)
open CryptoVerification.LibsignalTripleRatchetRepr
  (TailVecGhost noneCap optSenderChainAt optTailVecAt protocolAddressAt
   sessionStateAt signalMessageAt tapeAfter tapeAt uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet
  (SpqrModel TryDecryptGhost extHookStack logOff rootStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Getters
  (ClearUpkGhost blkPC_29 blkPC_35 blkPl_29 blkPl_35 clearUpkStack clearUpkStackX
   isSameAccountStack localIdentityOkAt remoteIdentityOkAt)
open CryptoVerification.LibsignalTripleRatchet.Decrypt
  (tryDecryptCommonHeap tryDecryptSavedRegs tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
  (blkPC_131 blkPl_131 exists_remoteGroupC_of_length_32 exists_remoteGroupC_of_memRegion_32
   identityKeys_step4_to_memRegion_1352 identityKeys_step5_some_extract
   identityKeys_step5_some_recombine reaches_pc_lscl reaches_pc_lsro_preserve
   reaches_pc_seq_lscl remoteGroupC remoteGroupC_eq_remoteGroupD remoteGroupD
   segLoadRatchetPC_placed sepWP_to_reaches_pc sessionStateAt_cleared_upk_intro
   sessionStateAt_split_upk stackAt_tryDecryptSubStack_sub tryDecryptDummyImg
   tryDecryptEntry_placed)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliDeallocBudgetSpecWithStack subroutine_ok_rustCliDeallocBudget_withStack)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
  (clearUpkSpec clearUpkSpecX remoteIdentityKeyPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (TryDecryptEnvArgs tryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
  (S0SeamPlaced S0SeamXPlaced tryDecryptFnSpecPlaced tryDecryptRawSpecPlaced
   tryDecryptSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget
  (LoadRatchetStatePlaced_of_placed LoadRatchetState_placed tryDecryptDummyImg_eq_placedImg
   tryDecryptFnPlacedSpec tryDecryptPlacedSpec tryDecryptRawSpec)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSymBudget
  (identityKeys_remote_some_wp_placed)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysStepsBudget
  (clearUpkSpecWithStack identityKeys_step1_reaches_placed identityKeys_step2_reaches_placed
   identityKeys_step3_reaches_placed identityKeys_step4_reaches_placed
   identityKeys_step5_none_reaches_placed is_same_account_placed_ok)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Block `29`: `<SessionState>::remote_identity_key` -/

theorem remote_identity_key_placed_ok [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) :
    subroutine_ok ((blkPC_29).rebase (blkPl_29).base H) (blkPl_29).base
      (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)) :=
  LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget.remote_identity_key_placed_ok A H

/-! ## 2. Block `35`: `<SessionState>::clear_unacknowledged_pre_key_message` -/

abbrev clearUpkBudgetSpecWithStack := @clearUpkSpecWithStack

private theorem slt_one_iff_eq_zero_placed {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap.slt 1#64 = true) ↔ cap = 0 := by
  have h1 : (cap = 0) ↔ cap.toNat = 0 := ⟨by rintro rfl; rfl, fun h0 => BitVec.eq_of_toNat_eq h0⟩
  have h2 : (1#64 : BitVec 64).toNat = 1 := rfl
  have h3 : 2 * cap.toNat < 2 ^ 64 := by omega
  rw [h1]; unfold BitVec.slt BitVec.toInt; simp only [decide_eq_true_iff, h2, h3, ↓reduceIte]; omega

private theorem optTailVecAt_entails_deallocX_placed (A : RustAlloc) (size : Nat)
    (hsz24 : 24 ≤ size) (hsz64 : size ≤ 64) (a : BitVec 64) (opt : Option TailVecGhost) :
    optTailVecAt A size a opt ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) (size - 16) ∗
        (if cap.slt 1#64 = true then emp
         else ⌜0 < cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  cases opt with
  | none =>
    unfold optTailVecAt
    have hsplit : size - 8 = 8 + (size - 16) := by omega
    rw [hsplit, ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := size - 16)
          (b' := a + 16#64) rfl (by bv_omega) (by omega),
        memRegion_eight (a + 8#64), sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right noneCap (Entails.sepExists_right ptr ?_)
    have hslt : noneCap.slt 1#64 = true := by decide
    simp only [hslt, ↓reduceIte, sepConj_emp]; exact Entails.refl _
  | some g =>
    unfold optTailVecAt; apply Entails.pure_left; intro htail
    have hvec : vecGhostAt A g.vec a ⊢
        (a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else ⌜0 < g.vec.cap.toNat ∧ g.vec.cap.toNat < 2 ^ 63⌝ ∗
             A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat) := by
      unfold vecGhostAt
      refine Entails.trans (vecU8At_entails_dealloc A a g.vec.cap g.vec.ptr g.vec.bytes) ?_
      rw [sepConj_pure_left_comm]; apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader; simp only [slt_one_iff_eq_zero_placed hcap_lt, sepConj_assoc]
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
      by_cases h0 : g.vec.cap = 0
      · simp only [h0, ↓reduceIte]; exact Entails.refl _
      · simp only [h0, ↓reduceIte]
        exact Entails.pure_right
          ⟨Nat.pos_of_ne_zero (fun h => h0 (BitVec.eq_of_toNat_eq h)), hcap_lt⟩ (Entails.refl _)
    refine Entails.trans (sepConj_mono_left hvec) ?_
    refine Entails.sepExists_right g.vec.cap (Entails.sepExists_right g.vec.ptr ?_)
    have h16 : (((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ ((a + 24#64) ↦ₛ g.tail)) ⊢
        memRegion (a + 16#64) (size - 16) := by
      have hsplit : size - 16 = 8 + (size - 24) := by omega
      rw [hsplit, ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := size - 24)
            (b' := a + 24#64) rfl (by bv_omega) (by omega)]
      apply sepConj_mono (pointsTo64_entails_memRegion _ _)
      have hb := pointsToBytes_entails_memRegion (a + 24#64) g.tail; rwa [htail] at hb
    have hpull1 :
        (((a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else ⌜0 < g.vec.cap.toNat ∧ g.vec.cap.toNat < 2 ^ 63⌝ ∗
             A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat)) ∗
          ((a + 24#64) ↦ₛ g.tail)) =
        ((a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          (((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ ((a + 24#64) ↦ₛ g.tail)) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else ⌜0 < g.vec.cap.toNat ∧ g.vec.cap.toNat < 2 ^ 63⌝ ∗
             A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat)) := by sep_ac_rfl
    rw [hpull1]; exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h16))

private theorem stackAt_clearUpk_opt_placed {hookStack : Nat}
    (hstack : hookStack + 32 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (32 + hookStack) = stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 := by
  rw [Nat.add_comm 32 hookStack]; exact stackAt_split_cells sp hookStack 4 hstack

private theorem sepWP_sync_stackAt {prog : Program} {pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {sp1 : BitVec 64} {sz : Nat}
    (hf : P = stackAt sp1 sz ∗ F) (hsp : sp1 = s.sp)
    (hnext : SepWP prog pc s (stackAt s.sp sz ∗ F) post) :
    SepWP prog pc s P post :=
  SepWP.fold (Entails.of_eq (congrArg (stackAt · sz) hsp)) hf hnext

private theorem sepWP_instantiate_post_exists_4 {α : Type} {prog : Program} {pc : BitVec 64}
    {s : State} {P R : SepProp}
    {Q : State → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → α → SepProp}
    {rest : State → Prop} (w : α)
    (h : SepWP prog pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x : BitVec 64, ∃∗ x_1 : BitVec 64, ∃∗ x_2 : BitVec 64, ∃∗ x_3 : BitVec 64,
          Q sf x x_1 x_2 x_3 w) ∧ rest sf)) :
    SepWP prog pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x : BitVec 64, ∃∗ x_1 : BitVec 64, ∃∗ x_2 : BitVec 64, ∃∗ x_3 : BitVec 64,
          ∃∗ a : α, Q sf x x_1 x_2 x_3 a) ∧ rest sf) := by
  refine SepWP.mono h fun sf _ _ _ ⟨h1, h2⟩ => ⟨fun hm => ?_, h2⟩
  refine Satisfies.mono ?_ (h1 hm)
  apply Entails.sepExists_elim; intro x; refine Entails.sepExists_right x ?_
  apply Entails.sepExists_elim; intro x_1; refine Entails.sepExists_right x_1 ?_
  apply Entails.sepExists_elim; intro x_2; refine Entails.sepExists_right x_2 ?_
  apply Entails.sepExists_elim; intro x_3; refine Entails.sepExists_right x_3 ?_
  exact Entails.sepExists_right w (Entails.refl _)

private theorem clearUpkBudget_strengthen_post {prog : Program} {target_pc : BitVec 64} {s : State}
    {P R S₁ S₂ : SepProp}
    {PostRest : State → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → List AllocEvent → SepProp}
    {traceProp rest : State → Prop} (himp : S₁ ⊢ S₂)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ∃∗ evs,
          ⌜traceProp sf⌝ ∗ S₁ ∗ PostRest sf x x_1 x_2 x_3 evs) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ∃∗ evs,
          ⌜traceProp sf⌝ ∗ S₂ ∗ PostRest sf x x_1 x_2 x_3 evs) ∧ rest sf) := by
  refine SepWP.mono h fun sf _ _ _ ⟨h1, h2⟩ => ⟨fun hm => ?_, h2⟩
  refine Satisfies.mono ?_ (h1 hm)
  apply Entails.sepExists_elim; intro x; refine Entails.sepExists_right x ?_
  apply Entails.sepExists_elim; intro x_1; refine Entails.sepExists_right x_1 ?_
  apply Entails.sepExists_elim; intro x_2; refine Entails.sepExists_right x_2 ?_
  apply Entails.sepExists_elim; intro x_3; refine Entails.sepExists_right x_3 ?_
  apply Entails.sepExists_elim; intro evs; refine Entails.sepExists_right evs ?_
  exact sepConj_mono_right (sepConj_mono_left himp)

set_option maxHeartbeats 1600000 in
/-- Stack-parameterized budget-threaded relocatable verification of
`SessionState::clear_unacknowledged_pre_key_message` (Block `35`). -/
theorem clear_unacknowledged_pre_key_message_placed_ok_of_dealloc [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) (hookStack : Nat)
    (hstack : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hdealloc : subroutine_ok ((blkPC_35).rebase (blkPl_35).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_35).rebase (blkPl_35).base H) (blkPl_35).base
      (clearUpkSpecWithStack M A lim hookStack) := by
  dsimp only [rustCliDeallocBudgetSpecWithStack, AllocCallPreserved] at hdealloc
  unfold clearUpkSpecWithStack
  wp_init xst s0
  obtain ⟨⟨ss, G, sessSt⟩, st⟩ := xst
  dsimp only at *
  have hx0_eq : s0.readReg64 .x0 = ss := by assumption
  subst hx0_eq
  rw [sessionStateAt_split_upk, stackAt_clearUpk_opt_placed (by omega) s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.pure_elim ?_
  rintro ⟨hloc, hrem, hchains, hpending, hreg, hlik_len, hrik_len⟩
  refine SepWP.weaken_pre (sepConj_mono
    (optTailVecAt_entails_deallocX_placed { pool := emp, live := A.live } 48 (by decide) (by decide)
      (s0.readReg64 (Reg.gpr 0#5) + 248#64) G.pending)
    (sepConj_mono_left (optTailVecAt_entails_deallocX_placed { pool := emp, live := A.live } 32
      (by decide) (by decide) (s0.readReg64 (Reg.gpr 0#5) + 296#64) G.kyber))) ?_
  dsimp only
  wp_pull_exists
  rename_i cap2 ptr2 cap1 ptr1
  refine clearUpkBudget_strengthen_post
    (sessionStateAt_cleared_upk_intro { pool := emp, live := A.live }
      (s0.readReg64 (Reg.gpr 0#5)) ptr1 ptr2 G sessSt
      hloc hrem hchains hreg hlik_len hrik_len) ?_
  by_cases h1 : cap1.slt 1#64 = true <;>
    simp only [h1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · by_cases h2 : cap2.slt 1#64 = true <;>
      simp only [h2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_instantiate_post_exists_4 []
      have hfo : FreeOnlyEvs ([] : List AllocEvent) := by simp [FreeOnlyEvs]
      simp only [AllocCostModel.stepEvents_nil]
      wp_steps_sync_pool (s0.readReg64 .lr)
      wp_done
    · refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hpos2, hlt2⟩
      apply sepWP_instantiate_post_exists_4 (rustDeallocEvents cap2.toNat 1)
      have hfo : FreeOnlyEvs (rustDeallocEvents cap2.toNat 1) := by
        simp [FreeOnlyEvs, rustDeallocEvents]
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      wp_simp_pre [wp_norm]
      wp_call hdealloc (ptr2, cap2.toNat, 1, st)
      wp_steps_sync_pool (s0.readReg64 .lr)
      wp_done
  · refine SepWP.focus_pure (by sep_focus) ?_
    rintro ⟨hpos1, hlt1⟩
    by_cases h2 : cap2.slt 1#64 = true <;>
      simp only [h2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_instantiate_post_exists_4 (rustDeallocEvents cap1.toNat 1)
      have hfo : FreeOnlyEvs (rustDeallocEvents cap1.toNat 1) := by
        simp [FreeOnlyEvs, rustDeallocEvents]
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      wp_simp_pre [wp_norm]
      wp_call hdealloc (ptr1, cap1.toNat, 1, st)
      wp_steps_sync_pool (s0.readReg64 .lr)
      wp_done
    · refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hpos2, hlt2⟩
      apply sepWP_instantiate_post_exists_4
        (rustDeallocEvents cap1.toNat 1 ++ rustDeallocEvents cap2.toNat 1)
      have hfo : FreeOnlyEvs (rustDeallocEvents cap1.toNat 1 ++ rustDeallocEvents cap2.toNat 1) := by
        simp [FreeOnlyEvs, rustDeallocEvents]
      simp only [AllocCostModel.stepEvents_append]
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      wp_simp_pre [wp_norm]
      wp_call hdealloc (ptr1, cap1.toNat, 1, st)
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      wp_simp_pre [wp_norm]
      refine sepWP_sync_stackAt (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
      wp_call hdealloc (ptr2, cap2.toNat, 1, M.stepEvents (rustDeallocEvents cap1.toNat 1) st)
      wp_steps_sync_pool (s0.readReg64 .lr)
      rw [show stackAt _ hookStack = stackAt (s0.sp - 32#64) hookStack by
        simp only [wp_norm, arm64_norm, *]]
      wp_done

/-- Block `35` (`<SessionState>::clear_unacknowledged_pre_key_message`) meets
`clearUpkSpec M A lim` under `[LibsignalPlacement]`. -/
theorem clear_unacknowledged_pre_key_message_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_35).rebase (blkPl_35).base H) (blkPl_35).base
      (clearUpkSpec M A lim) :=
  clear_unacknowledged_pre_key_message_placed_ok_of_dealloc A lim H allocHookStack (by decide)
    (subroutine_ok_rustCliDeallocBudget_withStack (by decide) (by decide) (ls_hook_ok_of_mem hdealloc))

/-- Block `35` (`<SessionState>::clear_unacknowledged_pre_key_message`) meets
`clearUpkSpecX M A lim` under `[LibsignalPlacement]`. -/
theorem clear_unacknowledged_pre_key_message_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_35).rebase (blkPl_35).base H) (blkPl_35).base
      (clearUpkSpecX M A lim) :=
  clear_unacknowledged_pre_key_message_placed_ok_of_dealloc A lim H extHookStack (by decide)
    (subroutine_ok_rustCliDeallocBudget_withStack (by decide) (by decide) (ls_hook_ok_of_mem hdealloc))

/-! ## 3. Block `130` Segment S0 (`identityKeys_placed_ok` / `S0SeamPlaced` / `S0SeamXPlaced`) -/

private theorem tapeAfter_zero (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAt ctl cur rest ⊢ tapeAfter ctl cur rest 0 := by
  unfold tapeAt tapeAfter
  have hcur : cur + BitVec.ofNat 64 0 = cur := by bv_omega
  have hlen : rest.length - 0 = rest.length := Nat.sub_zero _
  rw [hcur, hlen]
  exact Entails.pure_left (fun _ => Entails.refl _)

theorem identityKeys_step5_some_reaches_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (x : TryDecryptGhost) (remIk : IdentityKey) (F : SepProp) (s0 s4 : State)
    (hcl : LibsignalCodeLoaded lsmpl s4.mem)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (h_pc : s4.pc = (blkPl_131).base + 384#64) (h_run : s4.status = .Running)
    (h_sp : s4.sp = s0.sp - 1504#64) (h_sp_align : s4.spAligned = true)
    (htr : s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hx8 : s4.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13)
    (hx9 : s4.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21)
    (hx10 : s4.readReg64 .x10 = BitVec.zeroExtend 64 b22) (hx11 : s4.readReg64 .x11 = 1#64)
    (hx19 : s4.readReg64 .x19 = x.ret) (hx20 : s4.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s4.readReg64 .x21 = x.ss) (hx22 : s4.readReg64 .x22 = x.msgA)
    (hx23 : s4.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s4.readReg64 .x25 = x.locA) (hx29 : s4.readReg64 .x29 = s0.sp - 96#64)
    (hrem_eq : ∀ a : BitVec 64, (a ↦ₛ remIk.publicKey.bytes.toList) =
      remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    (hdiff : x.st.localIdentity ≠ remIk)
    (hm : s4.mem ⊨ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗ memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗
      ((s0.sp - 1504#64 + 352#64) ↦₆₄ w3) ∗ ((s0.sp - 1504#64 + 360#64) ↦₈ b31) ∗
      ((s0.sp - 1504#64 + 976#64) ↦₃₂ w0) ∗ ((s0.sp - 1504#64 + 980#64) ↦₈ b4) ∗
      ((s0.sp - 1504#64 + 981#64) ↦₈ b5) ∗ memRegion ((s0.sp - 1504#64) + 56#64) 296 ∗
      memRegion ((s0.sp - 1504#64) + 361#64) 39 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 542 ∗
      memRegion ((s0.sp - 1504#64) + 982#64) 298 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 472#64) s4
      (fun s5 => VmPreserved s4 s5 ∧ s5.sp = sp ∧ s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧ s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧ s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧ s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧ s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨ ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 1352 ∗ stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  rw [stackAt_tryDecryptSubStack_sub s0.sp isSameAccountStack (by decide)] at hm
  have hm_sub : s4.mem ⊨ (memRegion (sp + 400#64) 34 ∗ memRegion (sp + 56#64) 296) ∗
      (((sp + 48#64) ↦₆₄ x.remA) ∗ ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
       ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
       memRegion (sp + 361#64) 39 ∗ memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗
       ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 1312#64) 96 ∗ stackAt sp isSameAccountStack ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountStack) ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u400, u408, dw0, db4, db5, db6, db7, db8, db9, db10, db11, db12, db13, db14, db15,
    db16, db17, db18, db19, db20, db21, db22, dw3, db31, hm_ext⟩ :=
    identityKeys_step5_some_extract hm_sub
  have hm_pre : s4.mem ⊨
      (((s4.sp + 48#64) ↦₆₄ x.remA) ∗ ((s4.sp + 400#64) ↦₆₄ u400) ∗ ((s4.sp + 408#64) ↦₈ u408) ∗
       ((s4.sp + 352#64) ↦₆₄ w3) ∗ ((s4.sp + 360#64) ↦₈ b31) ∗ ((s4.sp + 976#64) ↦₃₂ w0) ∗
       ((s4.sp + 980#64) ↦₈ b4) ∗ ((s4.sp + 981#64) ↦₈ b5) ∗
       remoteGroupD (s4.sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 dw3 db31 ∗
       ((s4.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗ stackAt s4.sp isSameAccountStack) ∗
      (memRegion (sp + 409#64) 25 ∗ memRegion (sp + 88#64) 264 ∗
       memRegion (sp + 361#64) 39 ∗ memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗
       memRegion (sp + 1312#64) 96 ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountStack) ∗ F) := by
    rw [h_sp]; dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hx20' : s4.readReg64 .x20 = s4.sp + 320#64 := by rw [h_sp]; exact hx20
  have hx29' : s4.readReg64 .x29 = s4.sp + 1408#64 := by rw [hx29, h_sp]; bv_omega
  have hsame := ls_subroutine_ok_of_block (callerProg := (blkPC_131).rebase (blkPl_131).base H)
    (is_same_account_placed_ok h_bb)
  have hwp := identityKeys_remote_some_wp_placed hsame x remIk s4 hcl w0 b4 b5 b6 b7 b8 b9 b10 b11
    b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 u400 u408 dw0 db4 db5 db6 db7 db8 db9 db10
    db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 dw3 db31
    h_pc h_run h_sp_align hx8 hx9 hx10 hx11 hx20' hx25 hx29' hrem_eq hdiff
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s5 _ _ ⟨P_f, hm_s5, hvm5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hPf⟩
  refine ⟨hvm5, by reg_chain, halign5, by reg_chain, hx1_5, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, hx25_5, by rw [hx29_5, h_sp]; bv_omega, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s5; rw [h_sp] at hm2
  have hm3 : s5.mem ⊨
      (((sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗ memRegion (sp + 88#64) 264 ∗
       ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗ memRegion (sp + 361#64) 39 ∗
       ((sp + 400#64) ↦₈ b6) ∗ ((sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
       memRegion (sp + 409#64) 25 ∗ memRegion (sp + 434#64) 542 ∗ ((sp + 976#64) ↦₃₂ w0) ∗
       ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗ memRegion (sp + 982#64) 298 ∗
       ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗ memRegion (sp + 1312#64) 96) ∗
      (((sp + 48#64) ↦₆₄ x.remA) ∗
       (stackAt sp isSameAccountStack ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountStack)) ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  rw [← stackAt_tryDecryptSubStack_sub s0.sp isSameAccountStack (by decide)] at hm3
  have hm4 := Satisfies.mono
    (sepConj_mono_left (identityKeys_step5_some_recombine sp x.st.localIdentity remIk w0 b4 b5 b6
      (pack64 b7 b8 b9 b10 b11 b12 b13 b14) w3 b31)) hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem identityKeys_step45_reaches_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (x : TryDecryptGhost) (F : SepProp) (s0 s3 : State) (hcl : LibsignalCodeLoaded lsmpl s3.mem)
    (h_pc : s3.pc = (blkPl_131).base + 160#64) (h_run : s3.status = .Running)
    (h_sp : s3.sp = s0.sp - 1504#64) (h_sp_align : s3.spAligned = true)
    (htr : s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hx19 : s3.readReg64 .x19 = x.ret) (hx20 : s3.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s3.readReg64 .x21 = x.ss) (hx22 : s3.readReg64 .x22 = x.msgA)
    (hx23 : s3.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s3.readReg64 .x25 = x.locA) (hx29 : s3.readReg64 .x29 = s0.sp - 96#64)
    (hnot_self : x.st.remoteIdentity ≠ some x.st.localIdentity)
    (hm : s3.mem ⊨ remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      logOff tryDecryptDummyImg ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 472#64) s3
      (fun s5 => VmPreserved s3 s5 ∧ s5.sp = sp ∧ s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧ s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧ s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧ s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧ s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨ ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 1352 ∗
          logOff tryDecryptDummyImg ∗ stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  rcases hrem_opt : x.st.remoteIdentity with _ | remIk
  · rw [hrem_opt] at hm; dsimp only [remoteIdentityOkAt] at hm
    rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega,
        show sp + 400#64 + 2#64 = sp + 402#64 by bv_omega] at hm
    have hm_402 : s3.mem ⊨ memRegion (sp + 402#64) 32 ∗
        (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ 0#8) ∗
         memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846 ∗
         ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
         logOff tryDecryptDummyImg ∗ stackAt sp tryDecryptSubStack ∗ F) := by
      dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
    obtain ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, w3, b31, hent_402, hm_402⟩ :=
      exists_remoteGroupC_of_memRegion_32 hm_402
    have hm_s4 : s3.mem ⊨
        ((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ 0#8) ∗
        remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
        memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846 ∗
        (((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
         logOff tryDecryptDummyImg ∗ stackAt sp tryDecryptSubStack ∗ F) := by
      dsimp only [sp] at hm_402 ⊢; convert hm_402 using 1; sep_ac_rfl
    refine reaches_pc_seq
      (identityKeys_step4_reaches_placed x _ s0 s3 0#8 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
        w3 b31 h_pc h_run h_sp h_sp_align htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 (hent_402 (sp + 402#64)) hm_s4) ?_
    intro s4 hpc4 hrun4 ⟨hvm4, hsp4, halign4, htr4, _, _, _, hx11_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hm4⟩
    have hm4_re : s4.mem ⊨
        (memRegion (sp + 56#64) 296 ∗ ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
         memRegion (sp + 361#64) 39 ∗ memRegion (sp + 400#64) 34 ∗ memRegion (sp + 434#64) 542 ∗
         ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
         memRegion (sp + 982#64) 298 ∗ ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96) ∗
        (logOff tryDecryptDummyImg ∗ (((sp + 48#64) ↦₆₄ x.remA) ∗ stackAt sp tryDecryptSubStack ∗ F)) := by
      dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl
    have hm4_1352 := Satisfies.mono (sepConj_mono_left (identityKeys_step4_to_memRegion_1352 sp x.st.localIdentity w0 b4 b5 w3 b31)) hm4_re
    refine reaches_pc_mono
      (identityKeys_step5_none_reaches_placed x (((sp + 48#64) ↦₆₄ x.remA) ∗ stackAt sp tryDecryptSubStack ∗ F)
        s0 s4 hpc4 hrun4 hsp4 halign4 htr4 hx11_4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx29_4 hm4_1352) ?_
    intro s5 _ _ ⟨hvm5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hm5⟩
    refine ⟨hvm4.trans hvm5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, ?_⟩
    dsimp only [sp] at hm5; convert hm5 using 1; sep_ac_rfl
  · rw [hrem_opt] at hm; dsimp only [remoteIdentityOkAt] at hm
    rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega,
        show sp + 400#64 + 2#64 = sp + 402#64 by bv_omega] at hm
    obtain ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, w3, b31, hrem_c⟩ :=
      exists_remoteGroupC_of_length_32 (List.Vector.toList_length remIk.publicKey.bytes)
    have hent_402 : remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ⊢
        memRegion (sp + 402#64) 32 := by
      rw [← hrem_c (sp + 402#64)]
      have hlen : remIk.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
      have h := pointsToBytes_entails_memRegion (sp + 402#64) remIk.publicKey.bytes.toList; rwa [hlen] at h
    rw [hrem_c (sp + 402#64)] at hm
    have hm_s4 : s3.mem ⊨
        ((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ 1#8) ∗
        remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
        memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846 ∗
        (((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
         logOff tryDecryptDummyImg ∗ stackAt sp tryDecryptSubStack ∗ F) := by
      dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
    refine reaches_pc_seq_lscl hcl
      (identityKeys_step4_reaches_placed x _ s0 s3 1#8 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
        w3 b31 h_pc h_run h_sp h_sp_align htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 hent_402 hm_s4) ?_
    intro s4 hpc4 hrun4 ⟨hvm4, hsp4, halign4, htr4, hx8_4, hx9_4, hx10_4, hx11_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hm4⟩ hcl4
    have hrem_d : ∀ a : BitVec 64, (a ↦ₛ remIk.publicKey.bytes.toList) =
        remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 :=
      fun a => (hrem_c a).trans (remoteGroupC_eq_remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    have hdiff : x.st.localIdentity ≠ remIk := by intro heq; apply hnot_self; rw [hrem_opt, heq]
    have hm4_re : s4.mem ⊨
        ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 400#64) 34 ∗
        ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗ ((sp + 976#64) ↦₃₂ w0) ∗
        ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗ memRegion (sp + 56#64) 296 ∗
        memRegion (sp + 361#64) 39 ∗ memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗
        ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
        memRegion (sp + 1312#64) 96 ∗ stackAt sp tryDecryptSubStack ∗ (logOff tryDecryptDummyImg ∗ F) := by
      dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl
    refine reaches_pc_mono
      (identityKeys_step5_some_reaches_placed h_bb x remIk (logOff tryDecryptDummyImg ∗ F) s0 s4 hcl4
        w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31
        hpc4 hrun4 hsp4 halign4 htr4 hx8_4 hx9_4 hx10_4 hx11_4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx29_4
        hrem_d hdiff hm4_re) ?_
    intro s5 _ _ ⟨hvm5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hm5⟩
    refine ⟨hvm4.trans hvm5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, ?_⟩
    convert hm5 using 1; sep_ac_rfl

/-- Block `130` Segment S0 under `[LibsignalPlacement]` (`RustCliAllocBudget M`): reaches
`segLoadRatchetPC_placed` with budget-threaded `LoadRatchetState_placed`. -/
theorem identityKeys_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (x : TryDecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State)
    (h_pc : s0.pc = tryDecryptEntry_placed) (h_run : s0.status = .Running)
    (h_sp_align : s0.spAligned = true)
    (hpre : s0.mem ⊨ (tryDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0 ∗ R) :
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) segLoadRatchetPC_placed s0
      (LoadRatchetState_placed A lim st_init ctl x R s0) := by
  dsimp only [tryDecryptPlacedSpec, withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  dsimp only [tryDecryptRawSpec, tryDecryptRawSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hfits, hpre⟩
  let A0 : RustAlloc := A.atState lim st_init s0
  change s0.mem ⊨
    (CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptRawSpecPlaced
      C A0 ctl uuidTryParse S).pre x s0 ∗ R at hpre
  dsimp only [CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptRawSpecPlaced] at hpre
  rw [← tryDecryptDummyImg_eq_placedImg] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hnot_self, _, _, _⟩, hm0⟩
  unfold sessionStateAt at hm0; rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm0
  rcases hm0 with ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, hm0⟩
  have hm_s1 : s0.mem ⊨ stackAt s0.sp rootStack ∗ vecGhostAt A0 x.G.localIk x.ss ∗ logOff tryDecryptDummyImg ∗
      (vecGhostAt A0 x.G.remoteIk (x.ss + 0x18#64) ∗
       vecU8At A0 (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A0 104 8 (chainAt A0) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A0 x.G.alice (x.ss + 0x60#64) ∗
       vecU8At A0 (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A0 (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A0 48 (x.ss + 0xf8#64) x.G.pending ∗ optTailVecAt A0 32 (x.ss + 0x128#64) x.G.kyber ∗
       ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗ memRegion x.ret 48 ∗
       protocolAddressAt A0 x.rem x.remA ∗ protocolAddressAt A0 x.loc x.locA ∗
       signalMessageAt A0 x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ A0.pool ∗ R) := by
    convert hm0 using 1; sep_ac_rfl
  refine reaches_pc_seq_lscl hcl
    (identityKeys_step1_reaches_placed x _ s0 hcl h_pc h_run h_sp_align hx0 hx1 hx2 hx3 hx4 hx5 hdeser_loc hm_s1) ?_
  intro s1 hpc1 hrun1 ⟨hvm1, hsp1, halign1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx29_1, hm1⟩ hcl1
  have hm_s2 : s1.mem ⊨ localIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.localIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 433#64) 975 ∗
      (vecGhostAt A0 x.G.localIk x.ss ∗ vecGhostAt A0 x.G.remoteIk (x.ss + 0x18#64) ∗
       memRegion (s0.sp - 1504#64) 48 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ tryDecryptSavedRegs s0.sp s0 ∗
       (vecU8At A0 (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        vecAt A0 104 8 (chainAt A0) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A0 x.G.alice (x.ss + 0x60#64) ∗
        vecU8At A0 (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optSenderChainAt A0 (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
        optTailVecAt A0 48 (x.ss + 0xf8#64) x.G.pending ∗ optTailVecAt A0 32 (x.ss + 0x128#64) x.G.kyber ∗
        ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
        ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗ logOff tryDecryptDummyImg ∗ memRegion x.ret 48 ∗
        protocolAddressAt A0 x.rem x.remA ∗ protocolAddressAt A0 x.loc x.locA ∗
        signalMessageAt A0 x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ A0.pool ∗ R)) := by
    convert hm1 using 1; sep_ac_rfl
  refine reaches_pc_seq_lscl hcl1
    (identityKeys_step2_reaches_placed x _ s0 s1 hpc1 hrun1 hsp1 halign1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hm_s2) ?_
  intro s2 hpc2 hrun2 ⟨hvm2, hsp2, halign2, htr2, hx0_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx29_2, hm2⟩ hcl2
  have hm_s3 : s2.mem ⊨ vecGhostAt A0 x.G.remoteIk (x.ss + 0x18#64) ∗
      memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗ logOff tryDecryptDummyImg ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      (memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
       ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗ vecGhostAt A0 x.G.localIk x.ss ∗
       memRegion (s0.sp - 1504#64) 48 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       (vecU8At A0 (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        vecAt A0 104 8 (chainAt A0) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A0 x.G.alice (x.ss + 0x60#64) ∗
        vecU8At A0 (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optSenderChainAt A0 (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
        optTailVecAt A0 48 (x.ss + 0xf8#64) x.G.pending ∗ optTailVecAt A0 32 (x.ss + 0x128#64) x.G.kyber ∗
        ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
        ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗ memRegion x.ret 48 ∗
        protocolAddressAt A0 x.rem x.remA ∗ protocolAddressAt A0 x.loc x.locA ∗
        signalMessageAt A0 x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ A0.pool ∗ R)) := by
    convert hm2 using 1; sep_ac_rfl
  have hremote := ls_subroutine_ok_of_block (callerProg := (blkPC_131).rebase (blkPl_131).base H)
    (remote_identity_key_placed_ok A0 H)
  refine reaches_pc_seq_lscl hcl2
    (identityKeys_step3_reaches_placed hremote x _ s0 s2 hcl2 hpc2 hrun2 hsp2 halign2 htr2 hx0_2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx29_2 hdeser_rem hm_s3) ?_
  intro s3 hpc3 hrun3 ⟨hvm3, hsp3, halign3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx29_3, hm3⟩ hcl3
  have hm_s45 : s3.mem ⊨ remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      logOff tryDecryptDummyImg ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      (vecGhostAt A0 x.G.localIk x.ss ∗ vecGhostAt A0 x.G.remoteIk (x.ss + 0x18#64) ∗
       memRegion (s0.sp - 1504#64) 48 ∗ tryDecryptSavedRegs s0.sp s0 ∗
       vecU8At A0 (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A0 104 8 (chainAt A0) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A0 x.G.alice (x.ss + 0x60#64) ∗
       vecU8At A0 (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A0 (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A0 48 (x.ss + 0xf8#64) x.G.pending ∗ optTailVecAt A0 32 (x.ss + 0x128#64) x.G.kyber ∗
       ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗ memRegion x.ret 48 ∗
       protocolAddressAt A0 x.rem x.remA ∗ protocolAddressAt A0 x.loc x.locA ∗
       signalMessageAt A0 x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ A0.pool ∗ R) := by
    convert hm3 using 1; sep_ac_rfl
  refine reaches_pc_mono
    (reaches_pc_lscl hcl3
      (identityKeys_step45_reaches_placed h_bb x _ s0 s3 hcl3 hpc3 hrun3 hsp3 halign3 htr3
        hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx29_3 hnot_self hm_s45)) ?_
  intro s5 hpc5 hrun5 ⟨⟨hvm45, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hm5⟩, hcl5⟩
  have hvm : VmPreserved s0 s5 := ((hvm1.trans hvm2).trans hvm3).trans hvm45
  have hA_eq : A.atState lim st_init s5 = A0 := A.atState_eq_of_vmPreserved lim st_init hvm
  unfold LoadRatchetState_placed
  rw [hA_eq]
  refine ⟨hpc5, ⟨hrun5, hsp5, h_sp_align, halign5, hx29_5, htr5.1, hcl5, htr5.2⟩,
    hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx1_5, ?_⟩
  unfold sessionStateAt tryDecryptCommonHeap; rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, ?_⟩
  have hm5_tape : s5.mem ⊨
      tapeAt ctl x.cur x.rest ∗ (((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
       memRegion (s0.sp - 1504#64 + 56#64) 1352 ∗ logOff tryDecryptDummyImg ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ vecGhostAt A0 x.G.localIk x.ss ∗
       vecGhostAt A0 x.G.remoteIk (x.ss + 0x18#64) ∗ memRegion (s0.sp - 1504#64) 48 ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       vecU8At A0 (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A0 104 8 (chainAt A0) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A0 x.G.alice (x.ss + 0x60#64) ∗
       vecU8At A0 (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A0 (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A0 48 (x.ss + 0xf8#64) x.G.pending ∗ optTailVecAt A0 32 (x.ss + 0x128#64) x.G.kyber ∗
       ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗ memRegion x.ret 48 ∗
       protocolAddressAt A0 x.rem x.remA ∗ protocolAddressAt A0 x.loc x.locA ∗
       signalMessageAt A0 x.msgG x.msgA x.msg ∗ A0.pool ∗ R) := by
    convert hm5 using 1; sep_ac_rfl
  have hm5_after := Satisfies.mono (sepConj_mono_left (tapeAfter_zero ctl x.cur x.rest)) hm5_tape
  convert hm5_after using 1; sep_ac_rfl

/-- Block `130` Segment S0 under `[LibsignalPlacement]` (`tryDecryptFnPlacedSpec` variant). -/
theorem identityKeys_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (x : TryDecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State)
    (h_pc : s0.pc = tryDecryptEntry_placed) (h_run : s0.status = .Running)
    (h_sp_align : s0.spAligned = true)
    (hpre : s0.mem ⊨ (tryDecryptFnPlacedSpec C decFn A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0 ∗ R) :
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) segLoadRatchetPC_placed s0
      (LoadRatchetState_placed A lim st_init ctl x R s0) :=
  @identityKeys_placed_ok _ M C A lim ctl S H tdEnv h_bb x st_init R s0 h_pc h_run h_sp_align hpre

/-- Segment S0 seam (`S0SeamPlaced`) for Block `130` under `[LibsignalPlacement]`. -/
theorem identityKeys_seam_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    S0SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      C A lim ctl uuidTryParse S tdEnv := by
  intro x st_init R s0 h_pc h_run h_sp_align hpre
  dsimp only [tryDecryptSpecPlaced, withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  have hro : LibsignalRoLoaded lsmpl s0.mem := hpre.1.2
  have hpre_cl :
      s0.mem ⊨ (tryDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0 ∗ R := by
    dsimp only [tryDecryptPlacedSpec, withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hpre.1.1, hpre.2⟩
  refine reaches_pc_mono
    (reaches_pc_lsro_preserve hro
      (@identityKeys_placed_ok _ M C A lim ctl S H tdEnv h_bb x st_init R s0
        h_pc h_run h_sp_align hpre_cl)) ?_
  intro sf _ _ ⟨hS1, hro_f⟩
  exact LoadRatchetStatePlaced_of_placed hS1 hro_f

/-- Segment S0 `X` seam (`S0SeamXPlaced`) for Block `130` under `[LibsignalPlacement]`. -/
theorem identityKeys_seam_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    S0SeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      C decFn A lim ctl uuidTryParse S tdEnv :=
  fun x st_init R s0 h_pc h_run h_sp_align hpre =>
    @identityKeys_seam_placed_ok _ M C A lim ctl S H tdEnv h_bb x st_init R s0 h_pc h_run h_sp_align hpre

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysBudget
