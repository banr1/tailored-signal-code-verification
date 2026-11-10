/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.ApplyBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.Apply
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.CallsBudget
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExtBudget
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.ExtBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Verification of `TripleRatchet::apply_to_session_state`

Relocatable `RustCliAllocBudget`-threaded verification of
`<libsignal_protocol::triple_ratchet::TripleRatchet>::apply_to_session_state` (block 58) against
`trApplyBoundedSpec{,X}` and `DefsBudget.trApplySpec{,X}`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.ApplyBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (PublicKey SenderChain SessionState TripleRatchet)
open CryptoVerification
  (LibsignalPlacement blkPC_58 blkPl_58
   lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym
   ls_hook_ok_of_mem ls_subroutine_ok_of_block lsmpl lsρ
   sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.RustHeap (LayoutOk allocHookStack)
open CryptoVerification.LibsignalSessionRepr (length_keyToBytes32)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet
  (TrApplyGhost boxU8Buf extHookStack privSerializeStackX trAt)
open CryptoVerification.LibsignalTripleRatchet.Getters
  (blkPC_2 blkPC_3 blkPl_2 blkPl_3
   dropVecChainStack dropVecChainStackX dropVecMessageKeyStack dropVecMessageKeyStackX)
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetApply
  (LsClInv boxU8Buf_pk_expose exists_unpack64_of_length_104
   hck_tr_pack hrk_pack hrk_tr_pack hsc_stack_pack hsc_tr_pack
   memRegion_32_unpack mkApplyGhost mkSenderChainGhost
   optSenderChainAt_none_fold optSenderChainAt_some_fold
   optSenderChainBytes_length optSenderChainBytes_none_stack_eq
   optSenderChainBytes_some_stack_eq optSenderChainBytes_some_tr_eq
   pk_buf_to_memRegion priv_buf_to_memRegion serialize_pk_length
   sessionStateAt_expose_apply sessionStateAt_reassemble_apply
   spAligned_sub_224 sp_sub_224_orr_4
   stackAt_ext_to_gen stackAt_trApply stackAt_trApply_fold stackAt_trApply_fold_x stackAt_trApply_x
   stack_104_none_to_memRegion stack_104_some_to_memRegion stack_24_to_memRegion
   trApplyRel_mkApplyGhost trAt_expose trAt_in_struct_entails_memRegion
   vecU8At_fold_exact vecU8_priv_expose_stack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   RustLayoutOk VmPreserved allocMemcpyVmSpec fitsEvents_append
   rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustDeallocEvents
   subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (subroutine_ok_rustCliAllocNoOom_externWithStack
   subroutine_ok_rustCliDeallocBudget_externWithStack)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv framelessMemcpyBudgetSpec noAllocShimBudgetSpec
   publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
  (memcpySpecWithStack memcpyWithStack_of_framelessMemcpy
   publicKeySerializeSpecWithStack rustAllocNoOomExternSpecWithStack
   rustDeallocExternSpecWithStack shimSpecWithStack shimWithStack_of_noAllocShim)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
  (public_key_serialize_placed_ok public_key_serialize_placed_ok_x)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
  (dropVecChainSpec dropVecChainSpecX dropVecMessageKeySpec dropVecMessageKeySpecX)
open LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExtBudget
  (drop_vec_chain_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.ExtBudget
  (drop_vec_message_key_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.CallsBudget
  (priv_serialize_placed_ok_at priv_serialize_placed_ok_at_x)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
  (PrivSerializeEnv privSerializeEvents privSerializeSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.ApplyBudgetAux
  (SepWP_call_dropCh_lscl SepWP_call_pk_lscl SepWP_call_priv_lscl
   SepWP_drop_old_sender_placed SepWP_fold_stack_gen SepWP_tail_14c_to_184_placed
   TrApplyBoundedEnv TrApplyPreEnv
   dropVecChainSpecAt dropVecMessageKeySpecAt fitsEnv_trApplyPre_iff
   freeOnly_dealloc hookSat_framelessMemcpy_of_allocMemcpyVm
   hookSat_noAllocShim_of_rustAllocShimVm hookSat_sessionShim_of_noAllocShim
   instantiate_trApplyBounded_post subroutine_ok_trApplyX_of_bounded
   subroutine_ok_trApply_of_bounded trApplyAllocPrefix
   trApplyBoundedSpec trApplyBoundedSpecAt trApplyBoundedSpecX)

export LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.ApplyBudgetAux
  (trApplyBoundedSpecAt trApplyBoundedSpec trApplyBoundedSpecX)
export LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget
  (trApplySpec trApplySpecX)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Stack-parameterized relocatable proof (`trApplyBounded_placed_ok_opt`) -/

private theorem instantiate_trApplyBounded_post_norm {M : AllocCostModel}
    {prog : Program} {target_pc : BitVec 64} {s s0 : State} {P R : SepProp}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {calleeStack : Nat}
    (x : TrApplyGhost) (stB : M.σ) (G' : SessionGhost)
    (evsPre evsFree : List AllocEvent)
    (hpre_eq : evsPre = trApplyAllocPrefix x)
    (hfree : FreeOnlyEvs evsFree)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
          (⌜x.G.TrApplyRel x.trG G'⌝ ∗
            sessionStateAt A.repAlloc x.ss G' (x.tr.applyToSessionState x.st)) ∗
          memRegion x.t 264 ∗
          stackAt s0.sp (224 + calleeStack) ∗
          A.pool lim (M.stepEvents evsFree (M.stepEvents evsPre stB)) sf) ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨
          (∃∗ evs : List AllocEvent,
            ∃∗ G'' : SessionGhost,
              ⌜TrApplyBoundedEnv x evs ∧ sf.trace = s0.trace⌝ ∗
                ⌜x.G.TrApplyRel x.trG G''⌝ ∗
                  sessionStateAt A.repAlloc x.ss G'' (x.tr.applyToSessionState x.st) ∗
                    memRegion x.t 264 ∗
                      stackAt s0.sp (224 + calleeStack) ∗
                        A.pool lim (M.stepEvents evs stB) sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  refine SepWP.mono
    (instantiate_trApplyBounded_post x stB G' evsPre evsFree hpre_eq hfree h)
    fun sf P_f _ _ ⟨h1, h2⟩ => ⟨fun hm => ?_, h2⟩
  simpa only [trApplyBoundedSpecAt, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc] using h1 hm

set_option maxHeartbeats 1200000 in
/-- Stack-parameterized relocatable proof of `<TripleRatchet>::apply_to_session_state`
    (Block `58`) against `withLsCodeLoaded lsmpl (trApplyBoundedSpecAt M A lim calleeStack)`. -/
theorem trApplyBounded_placed_ok_opt [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {calleeStack stubStack mkStack chStack pkHookStack privStack : Nat}
    (hcallee : 224 + calleeStack < 2 ^ 64)
    (hstub_le : stubStack ≤ calleeStack)
    (hmk_le : mkStack ≤ calleeStack)
    (hch_le : chStack ≤ calleeStack)
    (hpk_le : pkHookStack + 32 ≤ calleeStack)
    (hpriv_le : privStack ≤ calleeStack)
    (hstack_open : ∀ sp : BitVec 64,
      stackAt sp (224 + calleeStack) =
        stackAt (sp - 224#64) calleeStack ∗
        (∃∗ u0 : BitVec 64, (sp - 224#64) ↦₆₄ u0) ∗
        (∃∗ u1 : BitVec 64, (sp - 216#64) ↦₆₄ u1) ∗
        (∃∗ u2 : BitVec 64, (sp - 208#64) ↦₆₄ u2) ∗
        (∃∗ u3 : BitVec 64, (sp - 200#64) ↦₆₄ u3) ∗
        (∃∗ u4 : BitVec 64, (sp - 192#64) ↦₆₄ u4) ∗
        (∃∗ u5 : BitVec 64, (sp - 184#64) ↦₆₄ u5) ∗
        (∃∗ u6 : BitVec 64, (sp - 176#64) ↦₆₄ u6) ∗
        (∃∗ u7 : BitVec 64, (sp - 168#64) ↦₆₄ u7) ∗
        (∃∗ u8 : BitVec 64, (sp - 160#64) ↦₆₄ u8) ∗
        (∃∗ u9 : BitVec 64, (sp - 152#64) ↦₆₄ u9) ∗
        (∃∗ u10 : BitVec 64, (sp - 144#64) ↦₆₄ u10) ∗
        (∃∗ u11 : BitVec 64, (sp - 136#64) ↦₆₄ u11) ∗
        (∃∗ u12 : BitVec 64, (sp - 128#64) ↦₆₄ u12) ∗
        memRegion (sp - 120#64) 24 ∗
        (∃∗ r0 : BitVec 64, (sp - 96#64) ↦₆₄ r0) ∗
        (∃∗ r1 : BitVec 64, (sp - 88#64) ↦₆₄ r1) ∗
        (∃∗ r2 : BitVec 64, (sp - 80#64) ↦₆₄ r2) ∗
        (∃∗ r3 : BitVec 64, (sp - 72#64) ↦₆₄ r3) ∗
        (∃∗ r4 : BitVec 64, (sp - 64#64) ↦₆₄ r4) ∗
        (∃∗ r5 : BitVec 64, (sp - 56#64) ↦₆₄ r5) ∗
        (∃∗ r6 : BitVec 64, (sp - 48#64) ↦₆₄ r6) ∗
        (∃∗ r7 : BitVec 64, (sp - 40#64) ↦₆₄ r7) ∗
        (∃∗ r8 : BitVec 64, (sp - 32#64) ↦₆₄ r8) ∗
        (∃∗ r9 : BitVec 64, (sp - 24#64) ↦₆₄ r9) ∗
        (∃∗ r10 : BitVec 64, (sp - 16#64) ↦₆₄ r10) ∗
        (∃∗ r11 : BitVec 64, (sp - 8#64) ↦₆₄ r11))
    (hstack_fold : ∀ (sp : BitVec 64) (s0 : State),
      (stackAt (sp - 224#64) calleeStack ∗
        memRegion (sp - 224#64) 104 ∗
        memRegion (sp - 120#64) 24 ∗
        ((sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp - 88#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
        stackAt sp (224 + calleeStack))
    (hshim : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsρ lsRustNoAllocShimSym) (shimSpecWithStack stubStack))
    (halloc : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsρ lsRustAllocSym) (rustAllocNoOomExternSpecWithStack M A lim false stubStack))
    (hdealloc : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack M A lim stubStack))
    (hmemcpy : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsρ lsMemcpySym) (memcpySpecWithStack stubStack))
    (hpriv : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsmpl.base 208) (withLsCodeLoaded lsmpl (privSerializeSpecWithStack M A lim privStack)))
    (hpk : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsmpl.base 205) (withLsCodeLoaded lsmpl (publicKeySerializeSpecWithStack M A lim pkHookStack)))
    (hdropMk : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsmpl.base 3) (withLsCodeLoaded lsmpl (dropVecMessageKeySpecAt M A lim mkStack)))
    (hdropCh : subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (lsmpl.base 2) (withLsCodeLoaded lsmpl (dropVecChainSpecAt M A lim chStack))) :
    subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (blkPl_58).base
      (withLsCodeLoaded lsmpl (trApplyBoundedSpecAt M A lim calleeStack)) := by
  have hdealloc_raw := hdealloc
  dsimp only [shimSpecWithStack] at hshim
  dsimp only [memcpySpecWithStack] at hmemcpy
  dsimp only [rustAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    RustLayoutOk, LayoutOk, ↓reduceIte] at halloc
  dsimp only [rustDeallocExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
    LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
    RustLayoutOk, LayoutOk] at hdealloc
  unfold withLsCodeLoaded trApplyBoundedSpecAt
  wp_init gx s0
  rcases gx with ⟨x, stB⟩
  have hinv0 : LsClInv s0 := by assumption
  have hEnv : FitsEnv M lim stB (TrApplyPreEnv x) := by assumption
  have hfit_all : FitsEvents M lim stB (trApplyAllocPrefix x) :=
    fitsEnv_trApplyPre_iff.mp hEnv
  rcases x with ⟨t, trG, tr, ss, G, st⟩
  dsimp only at *
  have hx0_eq : s0.readReg64 .x0 = t := by assumption
  have hx1_eq : s0.readReg64 .x1 = ss := by assumption
  subst hx0_eq hx1_eq
  refine SepWP.weaken_pre (sepConj_mono (trAt_expose A.repAlloc (s0.readReg64 .x0) trG tr)
    (sepConj_mono (sessionStateAt_expose_apply A.repAlloc (s0.readReg64 .x1) G st)
      (sepConj_mono (Entails.of_eq (hstack_open s0.sp)) (Entails.refl _)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat refine SepWP.exists_elim fun _ => ?_
  refine SepWP.pure_elim fun ⟨hclamp, hchains_len, hpad_len, hmax_jumps⟩ => ?_
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  refine SepWP.pure_elim fun ⟨hG_chains_len, hroot_pos, hroot_lt, hroot_c0, hroot_ptr, hGs_eq⟩ => ?_
  obtain ⟨scw0, scw1, scw2, scw3, scw4, scw5, scw6, scw7, scw8, scw9, scw10, scw11, scw12, hsc_unpack⟩ :=
    exists_unpack64_of_length_104 (optSenderChainBytes_length tr.ratchet.senderChain hpad_len)
  obtain ⟨rkw0, rkw1, rkw2, rkw3, hrk_eq, hrk_unpack⟩ :=
    exists_unpack64_of_length_32 (bs := keyToBytes32 tr.ratchet.rootKey)
      (length_keyToBytes32 _)
  clear hrk_eq
  rw [hsc_unpack (s0.readReg64 .x0 + 24#64), hrk_unpack (s0.readReg64 .x0 + 128#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, A.repAlloc_live_norm]
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hpos32 : 0 < (32 : Nat) := by decide
  have hsum32 : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  have hpos33 : 0 < (33 : Nat) := by decide
  have hsum33 : (33 : Nat) + 1 ≤ 2 ^ 63 := by decide
  have hroot_sum : G.root.cap.toNat + 1 ≤ 2 ^ 63 := by omega
  have hfit_base : FitsEvents M lim stB
      (rustAllocEvents 32 1 ++ rustDeallocEvents G.root.cap.toNat 1) := by
    cases hsc0 : tr.ratchet.senderChain
    · have heq :
          trApplyAllocPrefix ⟨s0.readReg64 .x0, trG, tr, s0.readReg64 .x1, G, st⟩ =
          rustAllocEvents 32 1 ++ rustDeallocEvents G.root.cap.toNat 1 := by
        simp [trApplyAllocPrefix, hsc0]
      exact heq ▸ hfit_all
    · have heq :
          trApplyAllocPrefix ⟨s0.readReg64 .x0, trG, tr, s0.readReg64 .x1, G, st⟩ =
          (rustAllocEvents 32 1 ++ rustDeallocEvents G.root.cap.toNat 1) ++
            (publicKeySerializeEvents ++ rustAllocEvents 33 1 ++
              privSerializeEvents ++ rustAllocEvents 32 1 ++ rustAllocEvents 32 1) := by
        simp [trApplyAllocPrefix, hsc0, List.append_assoc]
      exact ((fitsEvents_append M lim
        (rustAllocEvents 32 1 ++ rustDeallocEvents G.root.cap.toNat 1) _ stB).mp
        (heq ▸ hfit_all)).1
  have hfit_1 : FitsEvents M lim stB (rustAllocEvents 32 1) :=
    ((fitsEvents_append M lim _ _ stB).mp hfit_base).1
  have hfit_alloc1 : FitsEvents M lim stB [.alloc 32] := by
    simpa [rustAllocEvents] using hfit_1
  rcases hfit_alloc1 with ⟨⟨hwma1, henf1, hram1, hva1⟩, hnil_1⟩
  refine SepWP.fold (stackAt_ext_to_gen s0.sp calleeStack stubStack hcallee hstub_le)
    (by sep_focus) ?_
  apply sepWP_seq_lscl (mid := (blkPl_58).base + bv% (104)) hinv0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (32, 1, stB)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  have hoom1 : sf_1.readReg64 Reg.x0 ≠ 0#64 := by assumption
  have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom1
  rw [memRegion_32_unpack (sf_1.readReg64 Reg.x0)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => ?_
  refine SepWP.fold (hsc_stack_pack hsc_unpack) (by sep_focus) ?_
  refine SepWP.fold (hsc_tr_pack hsc_unpack) (by sep_focus) ?_
  apply sepWP_seq_lscl (mid := (blkPl_58).base + bv% (140)) hinv1
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  simp only [State.setMem_setMem]
  wp_call hdealloc (G.root.ptr, G.root.cap.toNat, 1, M.stepEvents (rustAllocEvents 32 1) stB)
  wp_steps_sync_pool ((blkPl_58).base + bv% (140))
  simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv2
  set evsBase := rustAllocEvents 32 1 ++ rustDeallocEvents G.root.cap.toNat 1
  have hstep_base :
      M.stepEvents (rustDeallocEvents G.root.cap.toNat 1)
        (M.stepEvents (rustAllocEvents 32 1) stB) =
      M.stepEvents evsBase stB := by
    simp only [evsBase, AllocCostModel.stepEvents_append]
  wp_simp_pre only [hstep_base]
  refine SepWP.fold (hrk_pack hrk_unpack) (by sep_focus) ?_
  refine SepWP.fold (hrk_tr_pack hrk_unpack) (by sep_focus) ?_
  clear hsc_unpack hrk_unpack
  cases hsc : tr.ratchet.senderChain with
  | none =>
    have hpre_none :
        evsBase = trApplyAllocPrefix ⟨s0.readReg64 .x0, trG, tr, s0.readReg64 .x1, G, st⟩ := by
      simp [trApplyAllocPrefix, hsc, evsBase]
    rw [optSenderChainBytes_none_stack_eq s0.sp trG.ratchet.senderPad]
    simp only [sepConj_assoc]
    apply sepWP_seq_lscl (mid := (blkPl_58).base + bv% (208)) hinv2
    wp_steps_sync_pool ((blkPl_58).base + bv% (208))
    simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_208
    refine SepWP.fold (stack_104_none_to_memRegion s0.sp trG.ratchet.senderPad hpad_len)
      (by sep_focus) ?_
    wp_simp_pre only [← A.repAlloc_live_norm]
    refine SepWP.fold (vecU8At_fold_exact A.repAlloc (s0.readReg64 .x1 + 48#64) 32#64
      (sf_1.readReg64 Reg.x0) (keyToBytes32 tr.ratchet.rootKey) 32 rfl (length_keyToBytes32 _)
      (by decide) (by decide) hoom1) (by sep_focus) ?_
    refine SepWP_drop_old_sender_placed hcallee hstub_le hmk_le hch_le hdealloc_raw hdropMk
      s0.sp (s0.readReg64 .x1) hinv_208
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hsp_align (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hGs_eq (by sep_focus) (by simp only [arm64_norm, *])
      fun sf_ds evsDs _ _ _ _ _ _ _ _ _ _ _ _ _ hfree_ds hpc_ds hrun_ds hsp_ds htr_ds hcs_ds hinv_ds => ?_
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_ds
    rcases hcs_ds with ⟨hcs_d19, hcs_d20, hcs_d21, hcs_d22, hcs_d23, hcs_d24, hcs_d25, hcs_d26, hcs_d27, hcs_d28, hcs_d29, hcs_dv⟩
    simp only [arm64_norm, *] at hcs_d19 hcs_d20 hcs_d21 hcs_d22 hcs_d23 hcs_d24 hcs_d25 hcs_d26 hcs_d27 hcs_d28 hcs_d29 hcs_dv
    simp only [sepConj_assoc]
    apply sepWP_seq_lscl (mid := lsmpl.base 2) hinv_ds
    wp_steps_sync_pool (lsmpl.base 2)
    simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_call_dc
    refine SepWP_call_dropCh_lscl
      (stB := M.stepEvents evsDs (M.stepEvents evsBase stB))
      (sp := s0.sp) (ret_pc := (blkPl_58).base + bv% (332))
      hdropCh hinv_call_dc
      ⟨s0.readReg64 .x1 + 72#64, G.chainsCap, G.chainsPtr, G.chains.zip st.receiverChains⟩
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hsp_align (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_focus)
      fun sf_dc hpc_dc hrun_dc hsp_dc hcs_dc _hinv_332 => ?_
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_dc
    rcases hcs_dc with ⟨hcs_c19, hcs_c20, hcs_c21, hcs_c22, hcs_c23, hcs_c24, hcs_c25, hcs_c26, hcs_c27, hcs_c28, hcs_c29, hcs_cv⟩
    simp only [arm64_norm, *] at hcs_c19 hcs_c20 hcs_c21 hcs_c22 hcs_c23 hcs_c24 hcs_c25 hcs_c26 hcs_c27 hcs_c28 hcs_c29 hcs_cv
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun evsDc => ?_
    refine SepWP.focus_pure (by sep_focus) fun htr_dc => ?_
    refine SepWP.focus_pure (by sep_focus) fun hfree_dc => ?_
    refine SepWP.fold (optSenderChainAt_none_fold A.repAlloc (s0.readReg64 .x1) _ _ _ _ _ _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine SepWP_tail_14c_to_184_placed hcallee hstub_le hch_le hdealloc_raw
      s0.sp (s0.readReg64 .x1) (s0.readReg64 .x0)
      hpc_dc hrun_dc hsp_align (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hchains_len (by sep_focus) (by simp only [arm64_norm, *])
      fun sf_tl evsTl hfree_tl hpc_tl hrun_tl hsp_tl htr_tl hvregs_tl => ?_
    simp only [arm64_norm, *] at hvregs_tl
    simp only [sepConj_assoc]
    have hsc_sym : (none : Option SenderChain) = tr.ratchet.senderChain := hsc.symm
    rw [hsc_sym]
    refine SepWP.fold (sessionStateAt_reassemble_apply A.repAlloc (s0.readReg64 .x1) G st trG tr
      (sf_1.readReg64 Reg.x0) none hchains_len) (by sep_focus) ?_
    refine SepWP.fold (trAt_in_struct_entails_memRegion (s0.readReg64 .x0) trG tr hpad_len)
      (by sep_focus) ?_
    wp_steps_sync_pool (s0.readReg64 .lr)
    simp only [State.setMem_setMem]
    refine SepWP.fold (hstack_fold s0.sp s0) (by sep_focus) ?_
    let evsFree := evsDs ++ evsDc ++ evsTl
    have hfree_all : FreeOnlyEvs evsFree := (hfree_ds.append hfree_dc).append hfree_tl
    have hstep_free :
        M.stepEvents evsTl (M.stepEvents evsDc (M.stepEvents evsDs (M.stepEvents evsBase stB))) =
        M.stepEvents evsFree (M.stepEvents evsBase stB) := by
      simp only [evsFree, AllocCostModel.stepEvents_append]
    wp_simp_pre only [hstep_free]
    apply instantiate_trApplyBounded_post_norm ⟨s0.readReg64 .x0, trG, tr, s0.readReg64 .x1, G, st⟩
      stB (mkApplyGhost G trG (sf_1.readReg64 Reg.x0) none) evsBase evsFree hpre_none hfree_all
    have hrel := trApplyRel_mkApplyGhost G trG (sf_1.readReg64 Reg.x0) none
    wp_done
  | some sc =>
    have hfit_some :
        FitsEvents M lim (M.stepEvents evsBase stB)
          (publicKeySerializeEvents ++ rustAllocEvents 33 1 ++
            privSerializeEvents ++ rustAllocEvents 32 1 ++ rustAllocEvents 32 1) := by
      have heq :
          trApplyAllocPrefix ⟨s0.readReg64 .x0, trG, tr, s0.readReg64 .x1, G, st⟩ =
          evsBase ++
            (publicKeySerializeEvents ++ rustAllocEvents 33 1 ++
              privSerializeEvents ++ rustAllocEvents 32 1 ++ rustAllocEvents 32 1) := by
        simp [trApplyAllocPrefix, hsc, evsBase, List.append_assoc]
      exact ((fitsEvents_append M lim evsBase _ stB).mp (heq ▸ hfit_all)).2
    have hfit_pk_split := (fitsEvents_append M lim publicKeySerializeEvents _ _).mp
      (by simpa only [List.append_assoc] using hfit_some)
    have hfit_pk : FitsEnv M lim (M.stepEvents evsBase stB) PublicKeySerializeEnv := by
      rintro _ rfl; exact hfit_pk_split.1
    set st1 := M.stepEvents publicKeySerializeEvents (M.stepEvents evsBase stB)
    have hfit_srk_split := (fitsEvents_append M lim (rustAllocEvents 33 1) _ st1).mp hfit_pk_split.2
    have hfit_srk : FitsEvents M lim st1 (rustAllocEvents 33 1) := hfit_srk_split.1
    have hfit_srk_raw : FitsEvents M lim st1 [.alloc 33] := by
      simpa [rustAllocEvents] using hfit_srk
    rcases hfit_srk_raw with ⟨⟨hwma_srk, henf_srk, hram_srk, hva_srk⟩, hnil_srk⟩
    set st2 := M.stepEvents (rustAllocEvents 33 1) st1
    have hfit_priv_split := (fitsEvents_append M lim privSerializeEvents _ st2).mp hfit_srk_split.2
    have hfit_priv : FitsEnv M lim st2 PrivSerializeEnv := by
      rintro _ rfl; exact hfit_priv_split.1
    set st3 := M.stepEvents privSerializeEvents st2
    have hfit_pa_split := (fitsEvents_append M lim (rustAllocEvents 32 1) _ st3).mp hfit_priv_split.2
    have hfit_pa : FitsEvents M lim st3 (rustAllocEvents 32 1) := hfit_pa_split.1
    have hfit_pa_raw : FitsEvents M lim st3 [.alloc 32] := by
      simpa [rustAllocEvents] using hfit_pa
    rcases hfit_pa_raw with ⟨⟨hwma_pa, henf_pa, hram_pa, hva_pa⟩, hnil_pa⟩
    set st4 := M.stepEvents (rustAllocEvents 32 1) st3
    have hfit_ck : FitsEvents M lim st4 (rustAllocEvents 32 1) := hfit_pa_split.2
    have hfit_ck_raw : FitsEvents M lim st4 [.alloc 32] := by
      simpa [rustAllocEvents] using hfit_ck
    rcases hfit_ck_raw with ⟨⟨hwma_ck, henf_ck, hram_ck, hva_ck⟩, hnil_ck⟩
    set st5 := M.stepEvents (rustAllocEvents 32 1) st4
    have hclamp_sc :
        CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes =
          sc.ratchetKey.privateKey.bytes :=
      hclamp sc hsc
    obtain ⟨ckw0, ckw1, ckw2, ckw3, hck_eq, hck_unpack⟩ :=
      exists_unpack64_of_length_32 (bs := keyToBytes32 sc.chainKey.key)
        (length_keyToBytes32 _)
    clear hck_eq
    rw [optSenderChainBytes_some_stack_eq s0.sp sc trG.ratchet.senderPad,
        optSenderChainBytes_some_tr_eq (s0.readReg64 .x0) sc trG.ratchet.senderPad hck_unpack]
    simp only [sepConj_assoc]
    have horr4 : (s0.sp - 224#64) ||| 4#64 = s0.sp - 220#64 := sp_sub_224_orr_4 hsp_align
    refine SepWP_fold_stack_gen s0.sp calleeStack stubStack (pkHookStack + 32)
      hcallee hstub_le hpk_le (by sep_focus) (by simp only [arm64_norm, *]) ?_
    apply sepWP_seq_lscl (mid := lsmpl.base 205) hinv2
    wp_steps_sync_pool (lsmpl.base 205)
    simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_pk0
    wp_simp_pre only [← A.repAlloc_live_norm]
    refine SepWP.fold (vecU8At_fold_exact A.repAlloc (s0.readReg64 .x1 + 48#64) 32#64
      (sf_1.readReg64 Reg.x0) (keyToBytes32 tr.ratchet.rootKey) 32 rfl (length_keyToBytes32 _)
      (by decide) (by decide) hoom1) (by sep_focus) ?_
    refine SepWP_call_pk_lscl hpk hinv_pk0 sc.ratchetKey.publicKey hfit_pk
      (ret_pc := (blkPl_58).base + bv% (180))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hsp_align (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus)
      fun sf_pk hpc_pk hrun_pk hsp_pk hcs_pk hinv_pk => ?_
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_pk
    rcases hcs_pk with ⟨hcs_k19, hcs_k20, hcs_k21, hcs_k22, hcs_k23, hcs_k24, hcs_k25, hcs_k26, hcs_k27, hcs_k28, hcs_k29, hcs_kv⟩
    simp only [arm64_norm, *] at hcs_k19 hcs_k20 hcs_k21 hcs_k22 hcs_k23 hcs_k24 hcs_k25 hcs_k26 hcs_k27 hcs_k28 hcs_k29 hcs_kv
    simp only [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨hpk_x1, hpk_tr⟩ => ?_
    refine SepWP.fold (boxU8Buf_pk_expose A.repAlloc (sf_pk.readReg64 .x0) sc.ratchetKey.publicKey)
      (by sep_focus) ?_
    simp only [sepConj_assoc, A.repAlloc_live_norm]
    refine SepWP.pure_elim fun hpk_ptr => ?_
    refine SepWP_fold_stack_gen s0.sp calleeStack (pkHookStack + 32) stubStack
      hcallee hpk_le hstub_le (by sep_focus) (by simp only [arm64_norm, *]) ?_
    apply sepWP_seq_lscl (mid := (blkPl_58).base + bv% (448)) hinv_pk
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (33, 1, st1)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv4
    have hoom_srk : sf_4.readReg64 Reg.x0 ≠ 0#64 := by assumption
    have hoom_srk_beq : (sf_4.readReg64 Reg.x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom_srk
    have hsrk_len : sc.ratchetKey.publicKey.serialize.length = 33 :=
      serialize_pk_length sc.ratchetKey.publicKey
    have hpriv_len : sc.ratchetKey.privateKey.bytes.toList.length = 32 :=
      sc.ratchetKey.privateKey.bytes.toList_length
    have hfp_sub24 : s0.sp - 96#64 - 24#64 = s0.sp - 120#64 := by rw [BitVec.sub_sub]; rfl
    apply sepWP_seq_lscl (mid := lsmpl.base 208) hinv4
    wp_steps_sync_pool (lsρ lsMemcpySym)
    simp only [State.setMem_setMem]
    wp_call hmemcpy (sf_4.readReg64 .x0, sf_pk.readReg64 .x0, sc.ratchetKey.publicKey.serialize)
    refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
    wp_steps_sync_pool (lsmpl.base 208)
    simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_priv0
    refine SepWP_fold_stack_gen s0.sp calleeStack stubStack privStack
      hcallee hstub_le hpriv_le (by sep_focus) (by simp only [arm64_norm, *]) ?_
    refine SepWP.fold (pk_buf_to_memRegion (sf_pk.readReg64 .x0) sc.ratchetKey.publicKey)
      (by sep_focus) ?_
    refine SepWP_call_priv_lscl hpriv hinv_priv0 sc.ratchetKey.privateKey.bytes.toList hfit_priv
      (ret_pc := (blkPl_58).base + bv% (484))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hsp_align (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus)
      fun sf_priv hpc_priv hrun_priv hsp_priv hcs_priv hinv_priv => ?_
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_priv
    rcases hcs_priv with ⟨hcs_p19, hcs_p20, hcs_p21, hcs_p22, hcs_p23, hcs_p24, hcs_p25, hcs_p26, hcs_p27, hcs_p28, hcs_p29, hcs_pv⟩
    simp only [arm64_norm, *] at hcs_p19 hcs_p20 hcs_p21 hcs_p22 hcs_p23 hcs_p24 hcs_p25 hcs_p26 hcs_p27 hcs_p28 hcs_p29 hcs_pv
    simp only [sepConj_assoc]
    refine SepWP.pure_elim fun hpriv_tr => ?_
    refine SepWP.fold (vecU8_priv_expose_stack A.repAlloc s0.sp sc.ratchetKey.privateKey.bytes)
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc, A.repAlloc_live_norm]
    refine SepWP.exists_elim fun privTempCap => SepWP.exists_elim fun privTempPtr => ?_
    refine SepWP.pure_elim fun ⟨hpt_le, hpt_lt, hpt_c0, hpt_ptr⟩ => ?_
    have hpt_pos : 0 < privTempCap.toNat := by omega
    have hpt_sum : privTempCap.toNat + 1 ≤ 2 ^ 63 := by omega
    refine SepWP_fold_stack_gen s0.sp calleeStack privStack stubStack
      hcallee hpriv_le hstub_le (by sep_focus) (by simp only [arm64_norm, *]) ?_
    apply sepWP_seq_lscl (mid := (blkPl_58).base + bv% (564)) hinv_priv
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (32, 1, st3)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv7
    have hoom_priv : sf_7.readReg64 Reg.x0 ≠ 0#64 := by assumption
    have hoom_priv_beq : (sf_7.readReg64 Reg.x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom_priv
    apply sepWP_seq_lscl (mid := (blkPl_58).base + bv% (604)) hinv7
    wp_steps_sync_pool (lsρ lsMemcpySym)
    simp only [State.setMem_setMem]
    wp_call hmemcpy (sf_7.readReg64 .x0, privTempPtr, sc.ratchetKey.privateKey.bytes.toList)
    refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    refine SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (32, 1, st4)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv10
    have hoom_ck : sf_10.readReg64 Reg.x0 ≠ 0#64 := by assumption
    have hoom_ck_beq : (sf_10.readReg64 Reg.x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom_ck
    rw [memRegion_32_unpack (sf_10.readReg64 Reg.x0)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
      SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => ?_
    refine SepWP.fold (priv_buf_to_memRegion privTempPtr privTempCap
      sc.ratchetKey.privateKey.bytes hpt_le hpt_lt) (by sep_focus) ?_
    apply sepWP_seq_lscl (mid := (blkPl_58).base + bv% (208)) hinv10
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc (privTempPtr, privTempCap.toNat, 1, st5)
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc (sf_pk.readReg64 .x0, 33, 1,
      M.stepEvents (rustDeallocEvents privTempCap.toNat 1) st5)
    wp_steps_sync_pool ((blkPl_58).base + bv% (208))
    simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_208
    refine SepWP.fold (hrk_pack hck_unpack) (by sep_focus) ?_
    refine SepWP.fold (hck_tr_pack trG.ratchet.senderPad hck_unpack) (by sep_focus) ?_
    refine SepWP.fold (stack_104_some_to_memRegion s0.sp sc trG.ratchet.senderPad hpad_len)
      (by sep_focus) ?_
    refine SepWP.fold (stack_24_to_memRegion s0.sp privTempCap privTempPtr 32#64) (by sep_focus) ?_
    clear hck_unpack
    refine SepWP_drop_old_sender_placed hcallee hstub_le hmk_le hch_le hdealloc_raw hdropMk
      s0.sp (s0.readReg64 .x1) hinv_208
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hsp_align (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hGs_eq (by sep_focus) (by simp only [arm64_norm, *])
      fun sf_ds evsDs _ _ _ _ _ _ _ _ _ _ _ _ _ hfree_ds hpc_ds hrun_ds hsp_ds htr_ds hcs_ds hinv_ds => ?_
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_ds
    rcases hcs_ds with ⟨hcs_d19, hcs_d20, hcs_d21, hcs_d22, hcs_d23, hcs_d24, hcs_d25, hcs_d26, hcs_d27, hcs_d28, hcs_d29, hcs_dv⟩
    simp only [arm64_norm, *] at hcs_d19 hcs_d20 hcs_d21 hcs_d22 hcs_d23 hcs_d24 hcs_d25 hcs_d26 hcs_d27 hcs_d28 hcs_d29 hcs_dv
    simp only [sepConj_assoc]
    apply sepWP_seq_lscl (mid := lsmpl.base 2) hinv_ds
    wp_steps_sync_pool (lsmpl.base 2)
    simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_call_dc
    refine SepWP_call_dropCh_lscl
      (stB := M.stepEvents evsDs
        (M.stepEvents (rustDeallocEvents 33 1)
          (M.stepEvents (rustDeallocEvents privTempCap.toNat 1) st5)))
      (sp := s0.sp) (ret_pc := (blkPl_58).base + bv% (332))
      hdropCh hinv_call_dc
      ⟨s0.readReg64 .x1 + 72#64, G.chainsCap, G.chainsPtr, G.chains.zip st.receiverChains⟩
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hsp_align (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_focus)
      fun sf_dc hpc_dc hrun_dc hsp_dc hcs_dc _hinv_332 => ?_
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_dc
    rcases hcs_dc with ⟨hcs_c19, hcs_c20, hcs_c21, hcs_c22, hcs_c23, hcs_c24, hcs_c25, hcs_c26, hcs_c27, hcs_c28, hcs_c29, hcs_cv⟩
    simp only [arm64_norm, *] at hcs_c19 hcs_c20 hcs_c21 hcs_c22 hcs_c23 hcs_c24 hcs_c25 hcs_c26 hcs_c27 hcs_c28 hcs_c29 hcs_cv
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun evsDc => ?_
    refine SepWP.focus_pure (by sep_focus) fun htr_dc => ?_
    refine SepWP.focus_pure (by sep_focus) fun hfree_dc => ?_
    wp_simp_pre only [← A.repAlloc_live_norm]
    refine SepWP.fold (optSenderChainAt_some_fold A.repAlloc (s0.readReg64 .x1) sc
      (sf_4.readReg64 Reg.x0) (sf_7.readReg64 Reg.x0) (sf_10.readReg64 Reg.x0)
      hclamp_sc hoom_srk hoom_priv hoom_ck) (by sep_focus) ?_
    refine SepWP_tail_14c_to_184_placed hcallee hstub_le hch_le hdealloc_raw
      s0.sp (s0.readReg64 .x1) (s0.readReg64 .x0)
      hpc_dc hrun_dc hsp_align (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hchains_len (by sep_focus) (by simp only [arm64_norm, *])
      fun sf_tl evsTl hfree_tl hpc_tl hrun_tl hsp_tl htr_tl hvregs_tl => ?_
    simp only [arm64_norm, *] at hvregs_tl
    simp only [sepConj_assoc]
    have hsc_sym : (some sc : Option SenderChain) = tr.ratchet.senderChain := hsc.symm
    rw [hsc_sym]
    refine SepWP.fold (sessionStateAt_reassemble_apply A.repAlloc (s0.readReg64 .x1) G st trG tr
      (sf_1.readReg64 Reg.x0)
      (some (mkSenderChainGhost sc (sf_4.readReg64 Reg.x0) (sf_7.readReg64 Reg.x0)
        (sf_10.readReg64 Reg.x0)))
      hchains_len) (by sep_focus) ?_
    refine SepWP.fold (trAt_in_struct_entails_memRegion (s0.readReg64 .x0) trG tr hpad_len)
      (by sep_focus) ?_
    wp_steps_sync_pool (s0.readReg64 .lr)
    simp only [State.setMem_setMem]
    refine SepWP.fold (hstack_fold s0.sp s0) (by sep_focus) ?_
    let evsSome :=
      evsBase ++ publicKeySerializeEvents ++ rustAllocEvents 33 1 ++
        privSerializeEvents ++ rustAllocEvents 32 1 ++ rustAllocEvents 32 1
    have hpre_some : evsSome = trApplyAllocPrefix ⟨s0.readReg64 .x0, trG, tr, s0.readReg64 .x1, G, st⟩ := by
      simp [trApplyAllocPrefix, hsc, evsSome, evsBase, List.append_assoc]
    let evsFree :=
      rustDeallocEvents privTempCap.toNat 1 ++ rustDeallocEvents 33 1 ++
        evsDs ++ evsDc ++ evsTl
    have hfree_all : FreeOnlyEvs evsFree :=
      ((((freeOnly_dealloc _ _).append (freeOnly_dealloc _ _)).append hfree_ds).append
        hfree_dc).append hfree_tl
    have hstep_some :
        M.stepEvents evsTl
          (M.stepEvents evsDc
            (M.stepEvents evsDs
              (M.stepEvents (rustDeallocEvents 33 1)
                (M.stepEvents (rustDeallocEvents privTempCap.toNat 1) st5)))) =
        M.stepEvents evsFree (M.stepEvents evsSome stB) := by
      simp only [evsFree, evsSome, st5, st4, st3, st2, st1, AllocCostModel.stepEvents_append]
    wp_simp_pre only [hstep_some]
    apply instantiate_trApplyBounded_post_norm ⟨s0.readReg64 .x0, trG, tr, s0.readReg64 .x1, G, st⟩
      stB (mkApplyGhost G trG (sf_1.readReg64 Reg.x0)
        (some (mkSenderChainGhost sc (sf_4.readReg64 Reg.x0) (sf_7.readReg64 Reg.x0)
          (sf_10.readReg64 Reg.x0))))
      evsSome evsFree hpre_some hfree_all
    have hrel := trApplyRel_mkApplyGhost G trG (sf_1.readReg64 Reg.x0)
      (some (mkSenderChainGhost sc (sf_4.readReg64 Reg.x0) (sf_7.readReg64 Reg.x0)
        (sf_10.readReg64 Reg.x0)))
    wp_done

/-! ## Standard (`trApplyStack`) and extended (`trApplyStackX`) entry points -/

/-- Relocatable `TR::apply_to_session_state` (Block `58`) meets
    `withLsCodeLoaded lsmpl (trApplyBoundedSpec M A lim)` from explicit drop-glue contracts. -/
theorem trApplyBounded_placed_ok_of_drops [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hdropMk : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (blkPl_3).base (dropVecMessageKeySpec M A lim))
    (hdropCh : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base (withLsCodeLoaded lsmpl (dropVecChainSpec M A lim))) :
    subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (blkPl_58).base
      (withLsCodeLoaded lsmpl (trApplyBoundedSpec M A lim)) :=
  trApplyBounded_placed_ok_opt
    (calleeStack := extHookStack) (stubStack := allocHookStack)
    (mkStack := dropVecMessageKeyStack) (chStack := dropVecChainStack)
    (pkHookStack := allocHookStack) (privStack := extHookStack)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    stackAt_trApply stackAt_trApply_fold
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack) (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))
    (subroutine_ok_rustCliDeallocBudget_externWithStack (stk := allocHookStack) (by decide) (by decide)
      (ls_hook_ok_of_mem hdealloc))
    (memcpyWithStack_of_framelessMemcpy allocHookStack (ls_hook_ok_of_mem hmemcpy))
    (priv_serialize_placed_ok_at (prog := (blkPC_58).rebase (blkPl_58).base H)
      (hookSat_sessionShim_of_noAllocShim hshim) halloc)
    (ls_subroutine_ok_of_block (callerProg := (blkPC_58).rebase (blkPl_58).base H)
      (subroutine_ok_withLsCodeLoaded_of_plain (public_key_serialize_placed_ok hshim halloc)))
    (ls_subroutine_ok_of_block (callerProg := (blkPC_58).rebase (blkPl_58).base H)
      (subroutine_ok_withLsCodeLoaded_of_plain hdropMk))
    (ls_subroutine_ok_of_block (callerProg := (blkPC_58).rebase (blkPl_58).base H) hdropCh)

/-- Relocatable `TR::apply_to_session_state` (Block `58`) meets
    `withLsCodeLoaded lsmpl (trApplyBoundedSpec M A lim)` directly from allocator/libc `HookSat`
    hypotheses (discharging `dropVecMessageKey` and `dropVecChain` internally). -/
theorem trApplyBounded_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec) :
    subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (blkPl_58).base
      (withLsCodeLoaded lsmpl (trApplyBoundedSpec M A lim)) :=
  trApplyBounded_placed_ok_of_drops hshim halloc hdealloc hmemcpy
    (drop_vec_message_key_placed_ok hdealloc)
    (drop_vec_chain_placed_ok hdealloc)

/-- `rustAllocShimVmSpec` / `allocMemcpyVmSpec` convenience entry point for
    `trApplyBounded_placed_ok`. -/
theorem trApplyBounded_placed_ok_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (blkPl_58).base
      (withLsCodeLoaded lsmpl (trApplyBoundedSpec M A lim)) :=
  trApplyBounded_placed_ok
    (hookSat_noAllocShim_of_rustAllocShimVm hshim) halloc hdealloc
    (hookSat_framelessMemcpy_of_allocMemcpyVm hmemcpy)

/-- `X`-stack (`trApplyStackX`) relocatable entry point for `TR::apply_to_session_state`
    (Block `58`). -/
theorem trApplyBounded_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hdropMk : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (blkPl_3).base (dropVecMessageKeySpecX M A lim))
    (hdropCh : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base (withLsCodeLoaded lsmpl (dropVecChainSpecX M A lim))) :
    subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (blkPl_58).base
      (withLsCodeLoaded lsmpl (trApplyBoundedSpecX M A lim)) :=
  trApplyBounded_placed_ok_opt
    (calleeStack := dropVecChainStackX) (stubStack := extHookStack)
    (mkStack := dropVecMessageKeyStackX) (chStack := dropVecChainStackX)
    (pkHookStack := extHookStack) (privStack := privSerializeStackX)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    stackAt_trApply_x stackAt_trApply_fold_x
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (stk := extHookStack) (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))
    (subroutine_ok_rustCliDeallocBudget_externWithStack (stk := extHookStack) (by decide) (by decide)
      (ls_hook_ok_of_mem hdealloc))
    (memcpyWithStack_of_framelessMemcpy extHookStack (ls_hook_ok_of_mem hmemcpy))
    (priv_serialize_placed_ok_at_x (prog := (blkPC_58).rebase (blkPl_58).base H)
      (hookSat_sessionShim_of_noAllocShim hshim) halloc)
    (ls_subroutine_ok_of_block (callerProg := (blkPC_58).rebase (blkPl_58).base H)
      (subroutine_ok_withLsCodeLoaded_of_plain (public_key_serialize_placed_ok_x hshim halloc)))
    (ls_subroutine_ok_of_block (callerProg := (blkPC_58).rebase (blkPl_58).base H)
      (subroutine_ok_withLsCodeLoaded_of_plain hdropMk))
    (ls_subroutine_ok_of_block (callerProg := (blkPC_58).rebase (blkPl_58).base H) hdropCh)

/-- `rustAllocShimVmSpec` / `allocMemcpyVmSpec` convenience entry point for
    `trApplyBounded_placed_ok_x`. -/
theorem trApplyBounded_placed_ok_x_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (hdropMk : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (blkPl_3).base (dropVecMessageKeySpecX M A lim))
    (hdropCh : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base (withLsCodeLoaded lsmpl (dropVecChainSpecX M A lim))) :
    subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (blkPl_58).base
      (withLsCodeLoaded lsmpl (trApplyBoundedSpecX M A lim)) :=
  trApplyBounded_placed_ok_x
    (hookSat_noAllocShim_of_rustAllocShimVm hshim) halloc hdealloc
    (hookSat_framelessMemcpy_of_allocMemcpyVm hmemcpy) hdropMk hdropCh

/-! ## Corollaries for `DefsBudget.trApplySpec` and `DefsBudget.trApplySpecX` -/

/-- Relocatable `TR::apply_to_session_state` (Block `58`) meets
    `withLsCodeLoaded lsmpl (DefsBudget.trApplySpec M A lim)` from explicit drop-glue contracts. -/
theorem trApply_placed_ok_of_drops [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hdropMk : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (blkPl_3).base (dropVecMessageKeySpec M A lim))
    (hdropCh : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base (withLsCodeLoaded lsmpl (dropVecChainSpec M A lim))) :
    subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (blkPl_58).base
      (withLsCodeLoaded lsmpl (trApplySpec M A lim)) :=
  subroutine_ok_trApply_of_bounded
    (trApplyBounded_placed_ok_of_drops hshim halloc hdealloc hmemcpy hdropMk hdropCh)

/-- Relocatable `TR::apply_to_session_state` (Block `58`) meets
    `withLsCodeLoaded lsmpl (DefsBudget.trApplySpec M A lim)` directly from allocator/libc `HookSat`
    hypotheses. -/
theorem trApply_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec) :
    subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (blkPl_58).base
      (withLsCodeLoaded lsmpl (trApplySpec M A lim)) :=
  subroutine_ok_trApply_of_bounded (trApplyBounded_placed_ok hshim halloc hdealloc hmemcpy)

/-- `rustAllocShimVmSpec` / `allocMemcpyVmSpec` convenience entry point for `trApply_placed_ok`. -/
theorem trApply_placed_ok_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (blkPl_58).base
      (withLsCodeLoaded lsmpl (trApplySpec M A lim)) :=
  subroutine_ok_trApply_of_bounded (trApplyBounded_placed_ok_vm hshim halloc hdealloc hmemcpy)

/-- `X`-stack (`trApplyStackX`) relocatable entry point against
    `withLsCodeLoaded lsmpl (DefsBudget.trApplySpecX M A lim)`. -/
theorem trApply_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hdropMk : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (blkPl_3).base (dropVecMessageKeySpecX M A lim))
    (hdropCh : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base (withLsCodeLoaded lsmpl (dropVecChainSpecX M A lim))) :
    subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (blkPl_58).base
      (withLsCodeLoaded lsmpl (trApplySpecX M A lim)) :=
  subroutine_ok_trApplyX_of_bounded
    (trApplyBounded_placed_ok_x hshim halloc hdealloc hmemcpy hdropMk hdropCh)

/-- `rustAllocShimVmSpec` / `allocMemcpyVmSpec` convenience entry point for `trApply_placed_ok_x`. -/
theorem trApply_placed_ok_x_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (hdropMk : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (blkPl_3).base (dropVecMessageKeySpecX M A lim))
    (hdropCh : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base (withLsCodeLoaded lsmpl (dropVecChainSpecX M A lim))) :
    subroutine_ok ((blkPC_58).rebase (blkPl_58).base H)
      (blkPl_58).base
      (withLsCodeLoaded lsmpl (trApplySpecX M A lim)) :=
  subroutine_ok_trApplyX_of_bounded
    (trApplyBounded_placed_ok_x_vm hshim halloc hdealloc hmemcpy hdropMk hdropCh)

end LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.ApplyBudget
