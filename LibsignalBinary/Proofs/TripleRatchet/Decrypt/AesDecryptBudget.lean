/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecrypt
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded Segment 8 (`aes_256_cbc_decrypt`) Proofs

Re-exports the Segment 8 allocator event envelope `s8Env` and block `130` (`159`) budget-threaded
theorems from `AesDecryptBudgetAux`, and proves the block `433` (`549`) counterparts
(`aesDecrypt_some_549_placed_ok`, `aesDecrypt_none_549_placed_ok`, `aesDecrypt_549_placed_ok`, and
their `_x` `decFn` variants) over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget

open Arm64 ProofLib
open CryptoGames.CBC (blockToBytesLE)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  Crypto MessageKeys SessionState SignalProtocolError TripleRatchet aesCbcDecrypt macLength
)
open CryptoVerification (
  LibsignalPlacement lsRustDeallocSym lsmpl lsρ
)
open CryptoVerification.RustHeap (allocHookStack vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (
  errTag signalMessageAt uuidTryParse
)
open CryptoVerification.LibsignalTripleRatchet (
  AesCall SpqrModel TrGhost TryDecryptGhost extHookStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_434 blkLib_eq_434 blkPl_434 speBodyAt tryDecryptCommonHeap
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt (
  Satisfies.mono_focus SepWP.setPC_ite_false SepWPp.elim_exists SepWPp.elim_exists_focus
  SepWPp.elim_memRegion1_focus SepWPp.elim_memRegion8_focus SepWPp.elim_pure
  SepWPp.elim_pure_focus SepWPp.elim_vecU8_focus SepWPp.mono_focus
  add_one_ne_zero_of_lt_2_63 aesDecrypt_none_p0_spe_entails_memRegion
  aesDecrypt_none_prep aesDecrypt_none_prep_x aesDecrypt_none_reg1144_split aesDecrypt_scr_split
  applyRatchet_reg10_split applyRatchet_reg3e8_split applyRatchet_sp_entails_memRegion
  boxU8At_msg_ct bytesToBlock_blockToBytesLE bytesToKey32_keyToBytes32
  errTail_reg190_split errTail_sp_entails_memRegion errTail_sp_split
  formatInner_post_eq_badCiphertext layoutOk_of_cap_ne_zero length_blockToBytesLE
  length_keyToBytes32 lsAesDecSym lsFormatInnerSym messageKeysAt_eq
  mks_parts_entails_memRegion newPqr_dealloc_prep' newPqr_zero_prep noPanic_callee
  sepWPp_to_steps_or_panic stackAt_ext_split_alloc stackAt_sub_split
  vecU8At_parts_entails_vecU8'
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt.AuthDecryptFacts (
  spAligned_of_sp_eq
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (
  FormatInnerEnv aesCallPreBudget aesDecBudgetSpec aesDecFnBudgetSpec
  formatInnerBudgetEnvSpec formatInnerBudgetSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  AesDecryptStatePlaced ApplyRatchetStatePlaced ErrTailStatePlaced ErrTailStateXPlaced
  S8SeamPlaced S8SeamXPlaced tryDecryptFnOnPanic tryDecryptOnPanic
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefsBudget (
  SepWPp.call_frame_placed SepWPp.of_sepWP_placed logOff_eq_placed
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux (
  protocolAddressAt_atState sessionStateAt_atState signalMessageAt_atState
  speBodyAt_atState trAt_atState vecU8_atState
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

private theorem sepWP_seg_433 [LibsignalPlacement] {H : String → Option (State → State)}
    {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : ∀ m_strip : Memory,
      SepWP ((blkPC_434).rebase (blkPl_434).base (hooksException H)) mid (s.setMem m_strip) Pre
        (fun sm' Pm => ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
          SepWP ((blkPC_434).rebase (blkPl_434).base H) target (sm'.setMem m_real) Pm post oom)) :
    SepWP ((blkPC_434).rebase (blkPl_434).base H) target s Pre post oom :=
  sepWP_seg_ls_vm (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H)) blkLib_eq_434 (by rfl) hseg

local macro "wp_sync_433 " mid:term : tactic =>
  `(tactic| (
    apply sepWP_seg_433 (mid := $mid); intro _m_strip; wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm])) (hnext := ?_)))

/-! ## 1. Re-Exports from `AesDecryptBudgetAux` (Envelope & Block `130` / `159` Proofs) -/

abbrev AesDecCtEnv := AesDecryptBudgetAux.AesDecCtEnv
abbrev s8Env := AesDecryptBudgetAux.s8Env
abbrev freeOnlyEvs_rustDeallocEvents := AesDecryptBudgetAux.freeOnlyEvs_rustDeallocEvents

abbrev aesDecrypt_some_159_placed_ok := @AesDecryptBudgetAux.aesDecrypt_some_159_placed_ok
abbrev aesDecrypt_none_159_placed_ok := @AesDecryptBudgetAux.aesDecrypt_none_159_placed_ok
abbrev aesDecrypt_159_placed_ok := @AesDecryptBudgetAux.aesDecrypt_159_placed_ok
abbrev aesDecrypt_some_159_placed_ok_x := @AesDecryptBudgetAux.aesDecrypt_some_159_placed_ok_x
abbrev aesDecrypt_none_159_placed_ok_x := @AesDecryptBudgetAux.aesDecrypt_none_159_placed_ok_x
abbrev aesDecrypt_159_placed_ok_x := @AesDecryptBudgetAux.aesDecrypt_159_placed_ok_x

/-! ## 2. Block `433` (`549`) Segment-8 Proofs (`S8SeamPlaced` & `S8SeamXPlaced`) -/

theorem aesDecrypt_some_549_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsAesDecSym) (aesDecBudgetSpec C.D M A lim))
    (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState pt : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hfits : FitsEnv M lim st (s8Env x mks newPqrState))
    (hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext = some pt)
    (h8 : AesDecryptStatePlaced (blkPl_434).base A lim st ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      ((∃ evs, s8Env x mks newPqrState evs ∧
          ApplyRatchetStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
            x trG tr st1 newPqrState pt draws R s0 s') ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R))) := by
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  change s.pc = (blkPl_434).base + 1656#64 at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold tryDecryptCommonHeap at hmem
  rw [sessionStateAt_atState, trAt_atState, protocolAddressAt_atState, protocolAddressAt_atState,
      signalMessageAt_atState, A.atState_live_eq_repAlloc, A.atState_pool] at hmem
  unfold signalMessageAt at hmem
  rw [boxU8At_msg_ct A.repAlloc x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + 1700#64) hmem hL ?_
  clear hmem
  apply SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl (mid := lsρ lsAesDecSym)
  wp_sync_433 (lsρ lsAesDecSym)
  apply SepWP.done (by rfl) (by exact hstat)
  intro hcl1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  let aesCallArg : AesCall :=
    ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
     s0.sp - 1504#64 + 0x540#64, blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩
  refine SepWPp.call_frame_placed (spec := aesDecBudgetSpec C.D M A lim)
    (x := (aesCallArg, st))
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗
          A.pool lim st _ ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_434).base + 1688#64)
    hcl1 haes (by rfl) (by exact hstat)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecBudgetSpec, aesCallPreBudget, aesCallArg]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [aesDecBudgetSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ _ hm_pan => by dsimp only [aesDecBudgetSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40,
      hfits.seq_left⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hcl1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecBudgetSpec, aesCallArg, AesCall.frame]
    rw [bytesToKey32_keyToBytes32, bytesToBlock_blockToBytesLE, hd]
    simp only [wp_norm, hsp]
    apply SepWPp.elim_exists; intro evs1
    simp only [sepConj_assoc]
    apply SepWPp.elim_pure; rintro ⟨htr2, hevs1⟩
    simp only [htr] at htr2
    refine SepWPp.elim_vecU8_focus (A := A.repAlloc) (a := s0.sp - 528#64) (bs := pt)
      (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
    have hcap_ne : ptCap + 1#64 ≠ 0#64 := add_one_ne_zero_of_lt_2_63 hpt_lt
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_434).base + 1700#64)
    wp_sync_433 ((blkPl_434).base + 1700#64)
    apply SepWP.done (by rfl) (by exact hrun2)
    intro hcl3
    apply SepWPp.of_sepWP_ret
    apply SepWP.done (by rfl) (by exact hrun2)
    intro _ _ hmf
    refine ⟨evs1, SeqEnv.inl hevs1, rfl, ⟨hrun2, hsp2, hsp0,
        spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2, ?_, htr2, hcl3, by simp only [wp_norm, hvregs_2]⟩,
      by simp only [wp_norm, hx19_2],
      by simp only [wp_norm, hx20_2],
      by simp only [wp_norm, hx21_2],
      by simp only [wp_norm, hx23_2],
      by simp only [wp_norm, hx24_2],
      newPqrCap, newPqrPtr, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
    · simp only [wp_norm, hx29_2]
    · unfold tryDecryptCommonHeap
      rw [sessionStateAt_atState, trAt_atState, vecU8_atState, protocolAddressAt_atState,
          protocolAddressAt_atState, signalMessageAt_atState, A.atState_live_eq_repAlloc,
          A.atState_pool]
      unfold signalMessageAt
      rw [boxU8At_msg_ct A.repAlloc x.msgA x.msgG.ctPtr x.msg.ciphertext,
          stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
          applyRatchet_reg10_split (s0.sp - 1504#64),
          applyRatchet_reg3e8_split (s0.sp - 1504#64)]
      have hvec := vecU8At_parts_entails_vecU8' A.repAlloc (s0.sp - 528#64) ptCap ptPtr pt hpt_le hpt_lt hpt_nz
      have hmf1 := Satisfies.mono_focus hvec (by sep_focus) hmf
      have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
      have hmf3 := Satisfies.mono_focus (applyRatchet_sp_entails_memRegion s0.sp msgW x.locA x.remA) (by sep_focus) hmf2
      clear hmf hmf1 hmf2
      simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf3 ⊢
      rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
      sep_close

set_option maxHeartbeats 800000 in
theorem aesDecrypt_none_549_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsAesDecSym) (aesDecBudgetSpec C.D M A lim))
    (hfmt : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsFormatInnerSym) (formatInnerBudgetSpec M A lim))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hfits : FitsEnv M lim st (s8Env x mks newPqrState))
    (hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext = none)
    (h8 : AesDecryptStatePlaced (blkPl_434).base A lim st ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      ((∃ evs, s8Env x mks newPqrState evs ∧
          ErrTailStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
            x trG tr st1 (.invalidMessage x.msgType .badCiphertext) draws R s0 s') ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R))) := by
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  change s.pc = (blkPl_434).base + 1656#64 at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold tryDecryptCommonHeap at hmem
  rw [sessionStateAt_atState, trAt_atState, protocolAddressAt_atState, protocolAddressAt_atState,
      signalMessageAt_atState, A.atState_live_eq_repAlloc, A.atState_pool] at hmem
  unfold signalMessageAt at hmem
  rw [boxU8At_msg_ct A.repAlloc x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + 780#64) hmem hL ?_
  clear hmem
  apply SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl (mid := lsρ lsAesDecSym)
  wp_sync_433 (lsρ lsAesDecSym)
  apply SepWP.done (by rfl) (by exact hstat)
  intro hcl1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  let aesCallArg : AesCall :=
    ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
     s0.sp - 1504#64 + 0x540#64, blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩
  refine SepWPp.call_frame_placed (spec := aesDecBudgetSpec C.D M A lim)
    (x := (aesCallArg, st))
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗
          A.pool lim st _ ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_434).base + 1688#64)
    hcl1 haes (by rfl) (by exact hstat)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecBudgetSpec, aesCallPreBudget, aesCallArg]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [aesDecBudgetSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ _ hm_pan => by dsimp only [aesDecBudgetSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40,
      hfits.seq_left⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hcl1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecBudgetSpec, aesCallArg, AesCall.frame]
    rw [bytesToKey32_keyToBytes32, bytesToBlock_blockToBytesLE, hd]
    simp only [wp_norm, hsp]
    apply SepWPp.elim_exists; intro evs1
    simp only [sepConj_assoc]
    apply SepWPp.elim_pure; rintro ⟨htr2, hevs1⟩
    simp only [htr] at htr2
    refine SepWPp.elim_exists_focus
      (Φ := fun p : BitVec 64 => ⌜p ≠ 0⌝ ∗ ((s0.sp - 520#64) ↦₆₄ p))
      (by sep_focus) fun p => ?_
    simp only [sepConj_assoc]
    apply SepWPp.elim_pure; intro hp_nz
    simp only [← sepConj_assoc]
    refine SepWPp.mono_focus (aesDecrypt_none_prep s0.sp) (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 512#64) (by sep_focus) fun w512 => ?_
    refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun b1120 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1104#64) (by sep_focus) fun w1104 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1096#64) (by sep_focus) fun w1096 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 480#64) (by sep_focus) fun w480 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 472#64) (by sep_focus) fun w472 => ?_
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl2 (mid := lsρ lsFormatInnerSym)
    wp_sync_433 (lsρ lsFormatInnerSym)
    apply SepWP.done (by rfl) (by exact hrun2)
    intro hcl2'
    refine SepWPp.call_frame_placed (spec := formatInnerBudgetSpec M A lim)
      (x := (s0.sp - 1144#64, M.stepEvents evs1 st))
      (T := memRegion (s0.sp - 1144#64) 24 ∗
            A.pool lim (M.stepEvents evs1 st) _ ∗
            stackAt (s0.sp - 1504#64) extHookStack)
      (ret_pc := (blkPl_434).base + 2656#64)
      hcl2' hfmt (by rfl) (by exact hrun2)
      (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
      (by dsimp only [formatInnerBudgetSpec, formatInnerBudgetEnvSpec]; simp only [wp_norm, hsp2]; rfl)
      (by refine ⟨by simp only [wp_norm], FitsEnv.nil⟩) (by sep_focus)
      (fun _ _ _ _ h => by dsimp only [formatInnerBudgetSpec, formatInnerBudgetEnvSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
      (fun _ _ _ hm_pan => by dsimp only [formatInnerBudgetSpec, formatInnerBudgetEnvSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
    clear hcl2'
    intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
    simp only [wp_norm, hsp2] at hsp3
    rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
    simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
    dsimp only [formatInnerBudgetSpec, formatInnerBudgetEnvSpec, FormatInnerEnv]
    simp only [wp_norm, hsp2]
    apply SepWPp.elim_exists; intro evs2
    simp only [sepConj_assoc]
    apply SepWPp.elim_pure; rintro ⟨htr3, rfl⟩
    simp only [htr2] at htr3
    change SepWPp _ _ _ _ _ _
    rw [formatInner_post_eq_badCiphertext A.repAlloc s0.sp]
    simp only [← sepConj_assoc]
    by_cases hpqr_cap : newPqrCap = 0#64
    · refine SepWPp.mono_focus (newPqr_zero_prep A.repAlloc newPqrCap newPqrPtr newPqrState hpqr_cap) (by sep_focus) ?_
      rw [emp_sepConj]
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_434).base + 780#64)
      wp_sync_433 ((blkPl_434).base + 780#64)
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hcl4
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) (by exact hrun3)
      intro _ _ hmf
      refine ⟨evs1, SeqEnv.inl hevs1, rfl, ⟨hrun3, hsp3, hsp0,
          spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3, ?_, htr3, hcl4, by simp only [wp_norm, hvregs_3]⟩,
        by simp only [wp_norm, hx19_3],
        by simp only [wp_norm, hx20_3],
        by simp only [wp_norm, hx26_3]; rfl, ?_⟩
      · simp only [wp_norm, hx29_3]
      · unfold tryDecryptCommonHeap
        rw [sessionStateAt_atState, trAt_atState, speBodyAt_atState, protocolAddressAt_atState,
            protocolAddressAt_atState, signalMessageAt_atState, A.atState_pool]
        unfold signalMessageAt speBodyAt
        rw [boxU8At_msg_ct A.repAlloc x.msgA x.msgG.ctPtr x.msg.ciphertext,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            errTail_sp_split s0.sp,
            errTail_reg190_split s0.sp]
        have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
        clear hmf hmf1
        simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
        rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
        sep_close
    · refine SepWPp.mono_focus (newPqr_dealloc_prep' A.repAlloc newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
      rw [A.repAlloc_live_norm, stackAt_ext_split_alloc (s0.sp - 1504#64)]
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl3 (mid := lsρ lsRustDeallocSym)
      wp_sync_433 (lsρ lsRustDeallocSym)
      apply SepWP.done (by rfl) (by exact hrun3)
      intro hcl3'
      refine SepWPp.call_frame_placed (spec := rustCliDeallocBudgetSpec M A lim)
        (x := (newPqrPtr, newPqrCap.toNat, 1, M.stepEvents evs1 st))
        (T := A.pool lim (M.stepEvents evs1 st) _ ∗
              A.live newPqrPtr newPqrCap.toNat 1 ∗
              memRegion newPqrPtr newPqrCap.toNat ∗
              stackAt (s0.sp - 1504#64) allocHookStack)
        (ret_pc := (blkPl_434).base + 2520#64)
        hcl3' hdealloc (by rfl) (by exact hrun3)
        (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
        (by dsimp only [rustCliDeallocBudgetSpec]; simp only [wp_norm, hsp3]; rfl)
        (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
          by simpa only [wp_norm] using lsRetAddr624_blockPlacement_base_add 434 2520#64 (by decide) (by decide)⟩)
        (by sep_focus)
        (fun _ _ _ _ h => by dsimp only [rustCliDeallocBudgetSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
        (fun _ _ _ hm_pan => by dsimp only [rustCliDeallocBudgetSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
      clear hcl3'
      intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl4
      simp only [wp_norm, hsp3] at hsp4
      rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
      simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
      dsimp only [rustCliDeallocBudgetSpec]
      simp only [wp_norm, hsp3, sepConj_assoc]
      apply SepWPp.elim_pure; rintro ⟨hacp4, _⟩
      have htr4 : s4.trace = s0.trace := hacp4.2.1.trans (by simp only [wp_norm, htr3])
      rw [← M.stepEvents_append evs1 (rustDeallocEvents newPqrCap.toNat 1) st]
      simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_434).base + 780#64)
      wp_sync_433 ((blkPl_434).base + 780#64)
      apply SepWP.done (by rfl) (by exact hrun4)
      intro hcl5
      apply SepWPp.of_sepWP_ret
      apply SepWP.done (by rfl) (by exact hrun4)
      intro _ _ hmf
      refine ⟨evs1 ++ rustDeallocEvents newPqrCap.toNat 1,
        SeqEnv.append hevs1 (freeOnlyEvs_rustDeallocEvents newPqrCap.toNat 1),
        rfl, ⟨hrun4, hsp4, hsp0,
          spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4, ?_, htr4, hcl5, by simp only [wp_norm, hvregs_4]⟩,
        by simp only [wp_norm, hx19_4],
        by simp only [wp_norm, hx20_4],
        by simp only [wp_norm, hx26_4]; rfl, ?_⟩
      · simp only [wp_norm, hx29_4]
      · unfold tryDecryptCommonHeap
        rw [sessionStateAt_atState, trAt_atState, speBodyAt_atState, protocolAddressAt_atState,
            protocolAddressAt_atState, signalMessageAt_atState, A.atState_pool]
        unfold signalMessageAt speBodyAt
        rw [boxU8At_msg_ct A.repAlloc x.msgA x.msgG.ctPtr x.msg.ciphertext,
            stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
            stackAt_ext_split_alloc (s0.sp - 1504#64),
            errTail_sp_split s0.sp,
            errTail_reg190_split s0.sp]
        have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
        have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
        clear hmf hmf1
        simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
        rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
        sep_close

theorem aesDecrypt_549_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsAesDecSym) (aesDecBudgetSpec C.D M A lim))
    (hfmt : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsFormatInnerSym) (formatInnerBudgetSpec M A lim))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    S8SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C A lim ctl uuidTryParse S s8Env := by
  intro x st trG tr st1 mks newPqrState draws R s0 s hfits h8 hL
  cases hd : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
  | none =>
    exact aesDecrypt_none_549_placed_ok C A lim ctl S H haes hfmt hdealloc
      x st trG tr st1 mks newPqrState draws R s0 s hfits hd h8 hL
  | some pt =>
    exact aesDecrypt_some_549_placed_ok C A lim ctl S H haes
      x st trG tr st1 mks newPqrState pt draws R s0 s hfits hd h8 hL

theorem aesDecrypt_some_549_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsAesDecSym) (aesDecFnBudgetSpec decFn M A lim))
    (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState pt : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hfits : FitsEnv M lim st (s8Env x mks newPqrState))
    (hd : decFn x.msg.ciphertext (keyToBytes32 mks.cipherKey) (blockToBytesLE mks.iv) = some pt)
    (h8 : AesDecryptStatePlaced (blkPl_434).base A lim st ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      ((∃ evs, s8Env x mks newPqrState evs ∧
          ApplyRatchetStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
            x trG tr st1 newPqrState pt draws R s0 s') ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ tryDecryptFnOnPanic C decFn uuidTryParse S x s0 s' ∗ R))) := by
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  change s.pc = (blkPl_434).base + 1656#64 at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold tryDecryptCommonHeap at hmem
  rw [sessionStateAt_atState, trAt_atState, protocolAddressAt_atState, protocolAddressAt_atState,
      signalMessageAt_atState, A.atState_live_eq_repAlloc, A.atState_pool] at hmem
  unfold signalMessageAt at hmem
  rw [boxU8At_msg_ct A.repAlloc x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + 1700#64) hmem hL ?_
  clear hmem
  apply SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl (mid := lsρ lsAesDecSym)
  wp_sync_433 (lsρ lsAesDecSym)
  apply SepWP.done (by rfl) (by exact hstat)
  intro hcl1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  let aesCallArg : AesCall :=
    ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
     s0.sp - 1504#64 + 0x540#64, blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩
  refine SepWPp.call_frame_placed (spec := aesDecFnBudgetSpec decFn M A lim)
    (x := (aesCallArg, st))
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗
          A.pool lim st _ ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_434).base + 1688#64)
    hcl1 haes (by rfl) (by exact hstat)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecFnBudgetSpec, aesCallPreBudget, aesCallArg]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [aesDecFnBudgetSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ _ hm_pan => by dsimp only [aesDecFnBudgetSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40,
      hfits.seq_left⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hcl1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecFnBudgetSpec, aesCallArg, AesCall.frame]
    rw [hd]
    simp only [wp_norm, hsp]
    apply SepWPp.elim_exists; intro evs1
    simp only [sepConj_assoc]
    apply SepWPp.elim_pure; rintro ⟨htr2, hevs1⟩
    simp only [htr] at htr2
    refine SepWPp.elim_vecU8_focus (A := A.repAlloc) (a := s0.sp - 528#64) (bs := pt)
      (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
    have hcap_ne : ptCap + 1#64 ≠ 0#64 := add_one_ne_zero_of_lt_2_63 hpt_lt
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_434).base + 1700#64)
    wp_sync_433 ((blkPl_434).base + 1700#64)
    apply SepWP.done (by rfl) (by exact hrun2)
    intro hcl3
    apply SepWPp.of_sepWP_ret
    apply SepWP.done (by rfl) (by exact hrun2)
    intro _ _ hmf
    refine ⟨evs1, SeqEnv.inl hevs1, rfl, ⟨hrun2, hsp2, hsp0,
        spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2, ?_, htr2, hcl3, by simp only [wp_norm, hvregs_2]⟩,
      by simp only [wp_norm, hx19_2],
      by simp only [wp_norm, hx20_2],
      by simp only [wp_norm, hx21_2],
      by simp only [wp_norm, hx23_2],
      by simp only [wp_norm, hx24_2],
      newPqrCap, newPqrPtr, hpqr_le, hpqr_lt, hpqr_nz, ?_⟩
    · simp only [wp_norm, hx29_2]
    · unfold tryDecryptCommonHeap
      rw [sessionStateAt_atState, trAt_atState, vecU8_atState, protocolAddressAt_atState,
          protocolAddressAt_atState, signalMessageAt_atState, A.atState_live_eq_repAlloc,
          A.atState_pool]
      unfold signalMessageAt
      rw [boxU8At_msg_ct A.repAlloc x.msgA x.msgG.ctPtr x.msg.ciphertext,
          stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
          applyRatchet_reg10_split (s0.sp - 1504#64),
          applyRatchet_reg3e8_split (s0.sp - 1504#64)]
      have hvec := vecU8At_parts_entails_vecU8' A.repAlloc (s0.sp - 528#64) ptCap ptPtr pt hpt_le hpt_lt hpt_nz
      have hmf1 := Satisfies.mono_focus hvec (by sep_focus) hmf
      have hmf2 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf1
      have hmf3 := Satisfies.mono_focus (applyRatchet_sp_entails_memRegion s0.sp msgW x.locA x.remA) (by sep_focus) hmf2
      clear hmf hmf1 hmf2
      simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf3 ⊢
      rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
      sep_close

set_option maxHeartbeats 1200000 in
theorem aesDecrypt_none_549_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsAesDecSym) (aesDecFnBudgetSpec decFn M A lim))
    (hfmt : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsFormatInnerSym) (formatInnerBudgetSpec M A lim))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack M A lim extHookStack))
    (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State)
    (hfits : FitsEnv M lim st (s8Env x mks newPqrState))
    (hd : decFn x.msg.ciphertext (keyToBytes32 mks.cipherKey) (blockToBytesLE mks.iv) = none)
    (h8 : AesDecryptStatePlaced (blkPl_434).base A lim st ctl x trG tr st1 mks newPqrState draws R s0 s)
    (hL : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      ((∃ evs, s8Env x mks newPqrState evs ∧
          ErrTailStateXPlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
            x trG tr st1 (.invalidMessage x.msgType .badCiphertext) draws R s0 s') ∨
       (s'.status = .Panicked ∧
        (s'.mem ⊨ tryDecryptFnOnPanic C decFn uuidTryParse S x s0 s' ∗ R))) := by
  have hlog_c00 := logOff_eq_placed
  rcases h8 with ⟨hpc, ⟨hstat, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28,
    newPqrCap, newPqrPtr, msgW, hmsgW, hpqr_le, hpqr_lt, hpqr_nz, hmem⟩
  change s.pc = (blkPl_434).base + 1656#64 at hpc
  have hx29_sp : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 := by rw [hx29]; bv_omega
  clear hx29
  unfold tryDecryptCommonHeap at hmem
  rw [sessionStateAt_atState, trAt_atState, protocolAddressAt_atState, protocolAddressAt_atState,
      signalMessageAt_atState, A.atState_live_eq_repAlloc, A.atState_pool] at hmem
  unfold signalMessageAt at hmem
  rw [boxU8At_msg_ct A.repAlloc x.msgA x.msgG.ctPtr x.msg.ciphertext,
      messageKeysAt_eq (s0.sp - 1504#64) mks,
      stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
      aesDecrypt_scr_split (s0.sp - 1504#64)] at hmem
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_steps_or_panic ((blkPl_434).base + 780#64) hmem hL ?_
  clear hmem
  apply SepWPp.elim_pure_focus
    (φ := macLength + 1 ≤ x.msg.serialized.length ∧
      x.msg.serialized.length < 2 ^ 40 ∧
      x.msg.ciphertext.length < 2 ^ 40 ∧
      x.msg.pqRatchet.length < 2 ^ 40 ∧
      ∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)
    (by sep_focus)
  intro hmsg_bounds
  have hct_lt40 : x.msg.ciphertext.length < 2 ^ 40 := hmsg_bounds.2.2.1
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl (mid := lsρ lsAesDecSym)
  wp_sync_433 (lsρ lsAesDecSym)
  apply SepWP.done (by rfl) (by exact hstat)
  intro hcl1
  have hkey_len : (keyToBytes32 mks.cipherKey).length = 32 := length_keyToBytes32 _
  have hiv_len : (blockToBytesLE mks.iv).length = 16 := length_blockToBytesLE _
  let aesCallArg : AesCall :=
    ⟨x.msgG.ctPtr, x.msg.ciphertext, s0.sp - 1504#64 + 0x500#64, keyToBytes32 mks.cipherKey,
     s0.sp - 1504#64 + 0x540#64, blockToBytesLE mks.iv, s0.sp - 1504#64 + 0x3d0#64⟩
  refine SepWPp.call_frame_placed (spec := aesDecFnBudgetSpec decFn M A lim)
    (x := (aesCallArg, st))
    (T := (x.msgG.ctPtr ↦ₛ x.msg.ciphertext) ∗
          ((s0.sp - 1504#64 + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
          ((s0.sp - 1504#64 + 0x540#64) ↦ₛ blockToBytesLE mks.iv) ∗
          memRegion (s0.sp - 1504#64 + 0x3d0#64) 24 ∗
          A.pool lim st _ ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_434).base + 1688#64)
    hcl1 haes (by rfl) (by exact hstat)
    (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
    (by dsimp only [aesDecFnBudgetSpec, aesCallPreBudget, aesCallArg]; simp only [wp_norm, hsp]; rfl)
    ?_ (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [aesDecFnBudgetSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun _ _ _ hm_pan => by dsimp only [aesDecFnBudgetSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  · refine ⟨trivial, ?_, trivial, trivial, trivial, trivial, trivial, hkey_len, hiv_len, hct_lt40,
      hfits.seq_left⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hct_lt40 (by decide))]
  · clear hcl1
    intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
    simp only [wp_norm, hsp] at hsp2
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
    clear hx26_2
    simp only [wp_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hx29_sp, hvregs] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hvregs_2
    dsimp only [aesDecFnBudgetSpec, aesCallArg, AesCall.frame]
    rw [hd]
    simp only [wp_norm, hsp]
    apply SepWPp.elim_exists; intro evs1
    simp only [sepConj_assoc]
    apply SepWPp.elim_pure; rintro ⟨htr2, hevs1⟩
    simp only [htr] at htr2
    simp only [← sepConj_assoc]
    refine SepWPp.mono_focus (aesDecrypt_none_prep_x s0.sp) (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 520#64) (by sep_focus) fun p => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 512#64) (by sep_focus) fun w512 => ?_
    refine SepWPp.elim_memRegion1_focus (a := s0.sp - 1120#64) (by sep_focus) fun b1120 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1104#64) (by sep_focus) fun w1104 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1096#64) (by sep_focus) fun w1096 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 480#64) (by sep_focus) fun w480 => ?_
    refine SepWPp.elim_memRegion8_focus (a := s0.sp - 472#64) (by sep_focus) fun w472 => ?_
    by_cases hp : p = 0#64
    · rw [aesDecrypt_none_reg1144_split s0.sp]
      simp only [sepConj_assoc]
      refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun w1144 => ?_
      refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun w1136 => ?_
      simp only [← sepConj_assoc]
      by_cases hpqr_cap : newPqrCap = 0#64
      · refine SepWPp.mono_focus (newPqr_zero_prep A.repAlloc newPqrCap newPqrPtr newPqrState hpqr_cap) (by sep_focus) ?_
        rw [emp_sepConj]
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_434).base + 780#64)
        wp_sync_433 ((blkPl_434).base + 780#64)
        apply SepWP.done (by rfl) (by exact hrun2)
        intro hcl3
        apply SepWPp.of_sepWP_ret
        apply SepWP.done (by rfl) (by exact hrun2)
        intro _ _ hmf
        refine ⟨evs1, SeqEnv.inl hevs1, rfl, ⟨hrun2, hsp2, hsp0,
            spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2, ?_, htr2, hcl3, by simp only [wp_norm, hvregs_2]⟩,
          by simp only [wp_norm, hx19_2],
          by simp only [wp_norm, hx20_2],
          false, fun _ => rfl,
          by simp only [wp_norm]; rfl, ?_⟩
        · simp only [wp_norm, hx29_2]
        · unfold tryDecryptCommonHeap
          rw [sessionStateAt_atState, trAt_atState, protocolAddressAt_atState,
              protocolAddressAt_atState, signalMessageAt_atState, A.atState_pool]
          unfold signalMessageAt
          rw [boxU8At_msg_ct A.repAlloc x.msgA x.msgG.ctPtr x.msg.ciphertext,
              stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
              errTail_sp_split s0.sp,
              errTail_reg190_split s0.sp,
              hlog_c00]
          have hmf0 := Satisfies.mono_focus (aesDecrypt_none_p0_spe_entails_memRegion s0.sp _ _ b1120) (by sep_focus) hmf
          have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf0
          have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA w1104 w1096 errTag p w512 w480 w472 msgW) (by sep_focus) hmf1
          clear hmf hmf0 hmf1
          simp only [wp_norm, Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hmsg_bounds hmf2 ⊢
          rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
          sep_close
      · refine SepWPp.mono_focus (newPqr_dealloc_prep' A.repAlloc newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
        rw [A.repAlloc_live_norm]
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl2 (mid := lsρ lsRustDeallocSym)
        wp_sync_433 (lsρ lsRustDeallocSym)
        apply SepWP.done (by rfl) (by exact hrun2)
        intro hcl2'
        refine SepWPp.call_frame_placed (spec := rustDeallocExternSpecWithStack M A lim extHookStack)
          (x := (newPqrPtr, newPqrCap.toNat, 1, M.stepEvents evs1 st))
          (T := A.pool lim (M.stepEvents evs1 st) _ ∗
                A.live newPqrPtr newPqrCap.toNat 1 ∗
                memRegion newPqrPtr newPqrCap.toNat ∗
                stackAt (s0.sp - 1504#64) extHookStack)
          (ret_pc := (blkPl_434).base + 2520#64)
          hcl2' hdealloc (by rfl) (by exact hrun2)
          (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
          (by dsimp only [rustDeallocExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]; simp only [wp_norm, hsp2]; rfl)
          (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
            ⟨layoutOk_of_cap_ne_zero hpqr_cap hpqr_lt, by decide⟩,
            by simpa only [wp_norm] using lsRetAddr624_blockPlacement_base_add 434 2520#64 (by decide) (by decide)⟩)
          (by sep_focus)
          (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
          (fun _ _ _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
        clear hcl2'
        intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl4
        simp only [wp_norm, hsp2] at hsp4
        rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
        simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
        dsimp only [rustDeallocExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        simp only [wp_norm, hsp2, sepConj_assoc]
        apply SepWPp.elim_pure; intro htr4
        simp only [htr2] at htr4
        rw [← M.stepEvents_append evs1 (rustDeallocEvents newPqrCap.toNat 1) st]
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_434).base + 780#64)
        wp_sync_433 ((blkPl_434).base + 780#64)
        apply SepWP.done (by rfl) (by exact hrun4)
        intro hcl5
        apply SepWPp.of_sepWP_ret
        apply SepWP.done (by rfl) (by exact hrun4)
        intro _ _ hmf
        refine ⟨evs1 ++ rustDeallocEvents newPqrCap.toNat 1,
          SeqEnv.append hevs1 (freeOnlyEvs_rustDeallocEvents newPqrCap.toNat 1),
          rfl, ⟨hrun4, hsp4, hsp0,
            spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4, ?_, htr4, hcl5, by simp only [wp_norm, hvregs_4]⟩,
          by simp only [wp_norm, hx19_4],
          by simp only [wp_norm, hx20_4],
          false, fun _ => rfl,
          by simp only [wp_norm, hx26_4]; rfl, ?_⟩
        · simp only [wp_norm, hx29_4]
        · unfold tryDecryptCommonHeap
          rw [sessionStateAt_atState, trAt_atState, protocolAddressAt_atState,
              protocolAddressAt_atState, signalMessageAt_atState, A.atState_pool]
          unfold signalMessageAt
          rw [boxU8At_msg_ct A.repAlloc x.msgA x.msgG.ctPtr x.msg.ciphertext,
              stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
              errTail_sp_split s0.sp,
              errTail_reg190_split s0.sp,
              hlog_c00]
          have hmf0 := Satisfies.mono_focus (aesDecrypt_none_p0_spe_entails_memRegion s0.sp _ _ b1120) (by sep_focus) hmf
          have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf0
          have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA w1104 w1096 errTag p w512 w480 w472 msgW) (by sep_focus) hmf1
          clear hmf hmf0 hmf1
          simp only [wp_norm, Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hmsg_bounds hmf2 ⊢
          rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
          sep_close
    · simp only [← sepConj_assoc]
      apply SepWPp.of_sepWP_placed hcl2 (mid := lsρ lsFormatInnerSym)
      wp_sync_433 (lsρ lsFormatInnerSym)
      apply SepWP.done (by rfl) (by exact hrun2)
      intro hcl2'
      refine SepWPp.call_frame_placed (spec := formatInnerBudgetSpec M A lim)
        (x := (s0.sp - 1144#64, M.stepEvents evs1 st))
        (T := memRegion (s0.sp - 1144#64) 24 ∗
              A.pool lim (M.stepEvents evs1 st) _ ∗
              stackAt (s0.sp - 1504#64) extHookStack)
        (ret_pc := (blkPl_434).base + 2656#64)
        hcl2' hfmt (by rfl) (by exact hrun2)
        (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
        (by dsimp only [formatInnerBudgetSpec, formatInnerBudgetEnvSpec]; simp only [wp_norm, hsp2]; rfl)
        (by refine ⟨by simp only [wp_norm], FitsEnv.nil⟩) (by sep_focus)
        (fun _ _ _ _ h => by dsimp only [formatInnerBudgetSpec, formatInnerBudgetEnvSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
        (fun _ _ _ hm_pan => by dsimp only [formatInnerBudgetSpec, formatInnerBudgetEnvSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
      clear hcl2'
      intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
      simp only [wp_norm, hsp2] at hsp3
      rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3⟩
      simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hx29_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3
      dsimp only [formatInnerBudgetSpec, formatInnerBudgetEnvSpec, FormatInnerEnv]
      simp only [wp_norm, hsp2]
      apply SepWPp.elim_exists; intro evs2
      simp only [sepConj_assoc]
      apply SepWPp.elim_pure; rintro ⟨htr3, rfl⟩
      simp only [htr2] at htr3
      change SepWPp _ _ _ _ _ _
      rw [formatInner_post_eq_badCiphertext A.repAlloc s0.sp]
      simp only [← sepConj_assoc]
      by_cases hpqr_cap : newPqrCap = 0#64
      · refine SepWPp.mono_focus (newPqr_zero_prep A.repAlloc newPqrCap newPqrPtr newPqrState hpqr_cap) (by sep_focus) ?_
        rw [emp_sepConj]
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_434).base + 780#64)
        wp_sync_433 ((blkPl_434).base + 780#64)
        apply SepWP.done (by rfl) (by exact hrun3)
        intro hcl4
        apply SepWPp.of_sepWP_ret
        apply SepWP.done (by rfl) (by exact hrun3)
        intro _ _ hmf
        refine ⟨evs1, SeqEnv.inl hevs1, ErrTailStatePlaced.toX ⟨rfl, ⟨hrun3, hsp3, hsp0,
            spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3, ?_, htr3, hcl4, by simp only [wp_norm, hvregs_3]⟩,
          by simp only [wp_norm, hx19_3],
          by simp only [wp_norm, hx20_3],
          by simp only [wp_norm, hx26_3]; rfl, ?_⟩⟩
        · simp only [wp_norm, hx29_3]
        · unfold tryDecryptCommonHeap
          rw [sessionStateAt_atState, trAt_atState, speBodyAt_atState, protocolAddressAt_atState,
              protocolAddressAt_atState, signalMessageAt_atState, A.atState_pool]
          unfold signalMessageAt speBodyAt
          rw [boxU8At_msg_ct A.repAlloc x.msgA x.msgG.ctPtr x.msg.ciphertext,
              stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
              errTail_sp_split s0.sp,
              errTail_reg190_split s0.sp]
          have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
          have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
          clear hmf hmf1
          simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
          rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
          sep_close
      · refine SepWPp.mono_focus (newPqr_dealloc_prep' A.repAlloc newPqrCap newPqrPtr newPqrState hpqr_cap hpqr_le hpqr_lt) (by sep_focus) ?_
        rw [A.repAlloc_live_norm]
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl3 (mid := lsρ lsRustDeallocSym)
        wp_sync_433 (lsρ lsRustDeallocSym)
        apply SepWP.done (by rfl) (by exact hrun3)
        intro hcl3'
        refine SepWPp.call_frame_placed (spec := rustDeallocExternSpecWithStack M A lim extHookStack)
          (x := (newPqrPtr, newPqrCap.toNat, 1, M.stepEvents evs1 st))
          (T := A.pool lim (M.stepEvents evs1 st) _ ∗
                A.live newPqrPtr newPqrCap.toNat 1 ∗
                memRegion newPqrPtr newPqrCap.toNat ∗
                stackAt (s0.sp - 1504#64) extHookStack)
          (ret_pc := (blkPl_434).base + 2520#64)
          hcl3' hdealloc (by rfl) (by exact hrun3)
          (spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
          (by dsimp only [rustDeallocExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]; simp only [wp_norm, hsp3]; rfl)
          (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
            ⟨layoutOk_of_cap_ne_zero hpqr_cap hpqr_lt, by decide⟩,
            by simpa only [wp_norm] using lsRetAddr624_blockPlacement_base_add 434 2520#64 (by decide) (by decide)⟩)
          (by sep_focus)
          (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
          (fun _ _ _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
        clear hcl3'
        intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl4
        simp only [wp_norm, hsp3] at hsp4
        rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hvregs_4⟩
        simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs_4
        dsimp only [rustDeallocExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        simp only [wp_norm, hsp3, sepConj_assoc]
        apply SepWPp.elim_pure; intro htr4
        simp only [htr3] at htr4
        rw [← M.stepEvents_append evs1 (rustDeallocEvents newPqrCap.toNat 1) st]
        simp only [← sepConj_assoc]
        apply SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_434).base + 780#64)
        wp_sync_433 ((blkPl_434).base + 780#64)
        apply SepWP.done (by rfl) (by exact hrun4)
        intro hcl5
        apply SepWPp.of_sepWP_ret
        apply SepWP.done (by rfl) (by exact hrun4)
        intro _ _ hmf
        refine ⟨evs1 ++ rustDeallocEvents newPqrCap.toNat 1,
          SeqEnv.append hevs1 (freeOnlyEvs_rustDeallocEvents newPqrCap.toNat 1),
          ErrTailStatePlaced.toX ⟨rfl, ⟨hrun4, hsp4, hsp0,
            spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al4, ?_, htr4, hcl5, by simp only [wp_norm, hvregs_4]⟩,
          by simp only [wp_norm, hx19_4],
          by simp only [wp_norm, hx20_4],
          by simp only [wp_norm, hx26_4]; rfl, ?_⟩⟩
        · simp only [wp_norm, hx29_4]
        · unfold tryDecryptCommonHeap
          rw [sessionStateAt_atState, trAt_atState, speBodyAt_atState, protocolAddressAt_atState,
              protocolAddressAt_atState, signalMessageAt_atState, A.atState_pool]
          unfold signalMessageAt speBodyAt
          rw [boxU8At_msg_ct A.repAlloc x.msgA x.msgG.ctPtr x.msg.ciphertext,
              stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide),
              errTail_sp_split s0.sp,
              errTail_reg190_split s0.sp]
          have hmf1 := Satisfies.mono_focus (mks_parts_entails_memRegion s0.sp mks) (by sep_focus) hmf
          have hmf2 := Satisfies.mono_focus (errTail_sp_entails_memRegion s0.sp newPqrCap x.locA newPqrPtr x.remA _ _ _ p w512 p w512 msgW) (by sep_focus) hmf1
          clear hmf hmf1
          simp only [wp_norm, sepConj_assoc] at hmsg_bounds hmf2 ⊢
          rcases hmsg_bounds with ⟨hm1, hm2, hm3, hm4, hm5⟩
          sep_close

theorem aesDecrypt_549_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (H : String → Option (State → State))
    (haes : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsAesDecSym) (aesDecFnBudgetSpec decFn M A lim))
    (hfmt : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsFormatInnerSym) (formatInnerBudgetSpec M A lim))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack M A lim extHookStack)) :
    S8SeamXPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C decFn A lim ctl uuidTryParse S s8Env := by
  intro x st trG tr st1 mks newPqrState draws R s0 s hfits h8 hL
  cases hd : decFn x.msg.ciphertext (keyToBytes32 mks.cipherKey) (blockToBytesLE mks.iv) with
  | none =>
    exact aesDecrypt_none_549_placed_ok_x C A lim ctl S decFn H haes hfmt hdealloc
      x st trG tr st1 mks newPqrState draws R s0 s hfits hd h8 hL
  | some pt =>
    exact aesDecrypt_some_549_placed_ok_x C A lim ctl S decFn H haes
      x st trG tr st1 mks newPqrState pt draws R s0 s hfits hd h8 hL

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget
