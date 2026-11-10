/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.SpqrRecvErrPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded SPQR Recv Error-Path Helpers on CLI Block `433`

Proves budget-threaded (`RustCliAllocBudget M`) `pqRecv_dealloc_tail_433_placed`,
`pqRecv_recv_err_true_433_placed`, and `pqRecv_recv_err_false_433_placed` on CLI Block `433` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.M4.SpqrRecvErrPlacedBudget

open scoped LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.Simp
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.Simp (
  sessionStateAt_atState trAt_atState speBodyAt_atState
  protocolAddressAt_atState signalMessageAt_atState
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (
  steps_of_sepWP_placed_state
)

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalTripleRatchet.Decrypt
  CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive
open CryptoGames.LibsignalSession (
  Crypto SignalProtocolError TripleRatchet SessionState MessageKeyGenerator
)
open CryptoVerification (
  LibsignalPlacement lsmpl lsρ lsro_intro_chk lsRustDeallocSym
)
open CryptoVerification.RustHeap (allocHookStack vecU8 vecU8At vecHeader)
open CryptoVerification.LibsignalSessionRepr (msgTypeByte)
open CryptoVerification.LibsignalTripleRatchetRepr (
  uuidTryParse utf8 speWord protocolAddressAt
  sessionStateAt signalMessageAt
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel TrGhost trAt TryDecryptGhost LibsignalCodeRoLoaded
  logOff extHookStack
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_434 blkPl_434 blkLib_eq_434 tryDecryptPlacedImg tryDecryptSubStack
  tryDecryptSavedRegs errTailPC_at speTag speBodyAt
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive (
  tryDecryptMidMetaCore steps_done_of_sepWP_midMeta_placed
  mr_cut mr_cut_add stackAt_sub sp_fp_eq sp56_weaken buf_to_mr sepWP_8_mr7_to_64
  concat56_8_cbz64_zero concat56_8_cbz64_ne_zero concat56_8_cbz32_ne_zero
  byte_ne_zero_cbz32 byte_ne_zero_cbz64_32
  speBodyAt_invalidState_fold speBodyAt_pqRatchet_fold
  pointsTo8_memRegion7_to_64 pointsTo64_to_8_memRegion7
  extractLsb0_8_append56
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees (
  lsFormatInnerSym lsroCheck_tryDecryptCoinsRoSym
)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt (
  cliTryDecryptCommonHeapPlaced
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEnv FreeOnlyEvs rustDeallocEvents rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (
  FormatInnerEnv formatInnerBudgetEnvSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (
  hooksException sepWP_seg_ls_vm
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget (
  steps_call_out_placed
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  tryDecryptOnPanic
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget (
  lsLogOff_eq_logOff_placed
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  ErrTailStatePlaced
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem pqRecv_dealloc_tail_433_placed [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {sp seedCap seedPtr : BitVec 64}
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hdealloc_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hsp_def : s0.sp - 1504#64 = sp)
    (e : SignalProtocolError) (st2 : State)
    (hpc2 : st2.pc = (blkPl_434).base + 2500#64)
    (hrun2 : st2.status = .Running)
    (hsp2 : st2.sp = sp)
    (hsp_al2 : st2.spAligned = true)
    (hfp2 : st2.readReg64 .fp = sp + 1408#64)
    (htr2 : st2.trace = s0.trace)
    (hvregs2 : calleeSavedVRegs st2 = calleeSavedVRegs s0)
    (hcl2 : LibsignalCodeRoLoaded lsmpl st2.mem)
    (hL2 : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded st2.mem)
    (hx19_2 : st2.readReg64 .x19 = x.ret)
    (hx20_2 : st2.readReg64 .x20 = sp + 320#64)
    (hx26_2 : st2.readReg64 .x26 = speTag e)
    (hm2 : st2.mem ⊨
      (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
       trAt A.repAlloc (sp + 56#64) trG tr ∗
       (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
         (seedPtr ↦ₛ mkg.seed) ∗
         memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
       memRegion x.ret 48 ∗
       memRegion sp 16 ∗
       ((sp + 16#64) ↦₆₄ seedPtr) ∗
       memRegion (sp + 24#64) 16 ∗
       ((sp + 40#64) ↦₆₄ seedCap) ∗
       memRegion (sp + 48#64) 8 ∗
       memRegion (sp + 320#64) 40 ∗
       speBodyAt A.repAlloc (utf8 "decrypt") (sp + 360#64) e ∗
       memRegion (sp + 400#64) 1008 ∗
       protocolAddressAt A.repAlloc x.rem x.remA ∗
       protocolAddressAt A.repAlloc x.loc x.locA ∗
       signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
       cliTapeAfter ctl x.cur x.rest draws ∗
       lsLogOff ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool lim st st2) ∗ R) :
    ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) st2 s' ∧
      ((∃ evs3, FreeOnlyEvs evs3 ∧
          ErrTailStatePlaced (blkPl_434).base A lim (M.stepEvents evs3 st)
            ctl x trG tr st1 e draws R s0 s') ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R)) := by
  have hsp_al2' : (st2.sp &&& 15#64 == 0#64) = true := hsp_al2
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp2]; exact hsp_al2
  rw [lsLogOff_eq_logOff_placed] at hm2
  simp only [← sepConj_assoc] at hm2
  by_cases hsc : seedCap = 0
  · simp only [hsc, ↓reduceIte] at hm2
    subst hsc
    suffices ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) st2 s' ∧
        (ErrTailStatePlaced (blkPl_434).base A lim st ctl x trG tr st1 e draws R s0 s' ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R)) by
      obtain ⟨s', hsteps, hok | hpan⟩ := this
      · exact ⟨s', hsteps, Or.inl ⟨[], FreeOnlyEvs.nil, by simpa [M.stepEvents_nil] using hok⟩⟩
      · exact ⟨s', hsteps, Or.inr hpan⟩
    unfold ErrTailStatePlaced CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailStatePlaced
    refine steps_done_of_sepWP_midMeta_placed (s0 := s0)
      (Rest := fun sf =>
        sf.readReg64 .x19 = x.ret ∧
        sf.readReg64 .x20 = (s0.sp - 1504#64) + 320#64 ∧
        sf.readReg64 .x26 = speTag e ∧
        (sf.mem ⊨
          sessionStateAt (A.atState lim st sf) x.ss x.G.afterTrFrom st1 ∗
          trAt (A.atState lim st sf) ((s0.sp - 1504#64) + 56#64) trG tr ∗
          memRegion x.ret 48 ∗
          memRegion (s0.sp - 1504#64) 56 ∗
          memRegion ((s0.sp - 1504#64) + 320#64) 40 ∗
          speBodyAt (A.atState lim st sf) (utf8 "decrypt") ((s0.sp - 1504#64) + 360#64) e ∗
          memRegion ((s0.sp - 1504#64) + 400#64) 1008 ∗
          cliTryDecryptCommonHeapPlaced (A.atState lim st sf) ctl x draws s0 ∗ R))
      hm2 hL2 hcl2 ?_
    unfold errTailPC_at tryDecryptMidMetaCore cliTryDecryptCommonHeapPlaced
    rw [lsLogOff_eq_logOff_placed]
    simp only [sessionStateAt_atState, trAt_atState, speBodyAt_atState,
      protocolAddressAt_atState, signalMessageAt_atState, RustCliAllocBudget.atState_pool]
    have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
    rw [hsp29_eq]; clear hsp29_eq
    rw [hsp_def]
    wp_conv_pre => simp only [sepConj_assoc]
    wp_steps_sync_pool ((blkPl_434).base + 780#64)
    refine SepWP.focus_weaken (sp56_weaken sp seedPtr 0#64) (by sep_focus) ?_
    wp_done
  · simp only [hsc, ↓reduceIte] at hm2
    have hsc_beq : (seedCap == 0#64) = false := beq_false_of_ne hsc
    refine steps_of_sepWP_placed_state hm2 hL2 hcl2
      (mid := lsρ lsRustDeallocSym)
      (RegMid := fun sm3 =>
        sm3.readReg64 .x0 = seedPtr ∧
        sm3.readReg64 .x1 = seedCap ∧
        sm3.readReg64 .x2 = 1#64 ∧
        sm3.readReg64 .lr = (blkPl_434).base + 2520#64 ∧
        sm3.readReg64 .x19 = x.ret ∧
        sm3.readReg64 .x20 = sp + 320#64 ∧
        sm3.readReg64 .x26 = speTag e ∧
        sm3.readReg64 .fp = sp + 1408#64 ∧
        sm3.sp = sp ∧ sm3.spAligned = true ∧ sm3.trace = s0.trace ∧
        calleeSavedVRegs sm3 = calleeSavedVRegs s0)
      (P_mid := fun sm3 =>
        A.pool lim st sm3 ∗ A.live seedPtr seedCap.toNat 1 ∗ memRegion seedPtr seedCap.toNat ∗
        stackAt sp allocHookStack ∗
        sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
        trAt A.repAlloc (sp + 56#64) trG tr ∗
        memRegion x.ret 48 ∗
        memRegion sp 56 ∗
        memRegion (sp + 320#64) 40 ∗
        speBodyAt A.repAlloc (utf8 "decrypt") (sp + 360#64) e ∗
        memRegion (sp + 400#64) 1008 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗
        signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
        cliTapeAfter ctl x.cur x.rest draws ∗
        logOff tryDecryptPlacedImg ∗
        memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - allocHookStack) ∗
        tryDecryptSavedRegs s0.sp s0) ?_ ?_
    · wp_conv_pre =>
        rw [stackAt_sub sp tryDecryptSubStack allocHookStack]
        simp only [sepConj_assoc]
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      refine SepWP.focus_weaken (sp56_weaken sp seedPtr seedCap) (by sep_focus) ?_
      refine SepWP.focus_weaken (buf_to_mr seedPtr mkg.seed seedCap.toNat hseed1 hseed2)
        (by sep_focus) ?_
      wp_done
    · intro sm3 hpcm3 hrunm3 hclm3 hLm3 ⟨hx0_3, hx1_3, hx2_3, hlr_3,
        hx19_3, hx20_3, hx26_3, hfp_3, hsp_3, hsp_al3, htr_3, hvregs_3⟩ hmm3
      have hpre_dealloc : sm3.mem ⊨
          ((rustCliDeallocBudgetSpec M A lim).pre (seedPtr, seedCap.toNat, 1, st) sm3 ∗
           ((sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
             trAt A.repAlloc (sp + 56#64) trG tr ∗
             memRegion x.ret 48 ∗
             memRegion sp 56 ∗
             memRegion (sp + 320#64) 40 ∗
             speBodyAt A.repAlloc (utf8 "decrypt") (sp + 360#64) e ∗
             memRegion (sp + 400#64) 1008 ∗
             protocolAddressAt A.repAlloc x.rem x.remA ∗
             protocolAddressAt A.repAlloc x.loc x.locA ∗
             signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
             cliTapeAfter ctl x.cur x.rest draws ∗
             logOff tryDecryptPlacedImg ∗
             memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
               (tryDecryptSubStack - allocHookStack) ∗
             tryDecryptSavedRegs s0.sp s0) ∗ R)) := by
        dsimp only [rustCliDeallocBudgetSpec]
        rw [hsp_3, sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0_3, by rw [hx1_3], by rw [hx2_3]; rfl,
          by rw [hlr_3]; exact _root_.LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 434 2520#64 (by decide) (by decide)⟩, ?_⟩
        simp only [sepConj_assoc] at hmm3 ⊢
        arm64_sep_close
      refine steps_call_out_placed (seedPtr, seedCap.toNat, 1, st) hdealloc_call
        hpcm3 hrunm3 hsp_al3 hlr_3 hclm3 hLm3 hpre_dealloc
        (fun sf _ hp => False.elim (by
          dsimp only [rustCliDeallocBudgetSpec] at hp
          rw [sepConj_assoc] at hp
          exact not_satisfies_false_sepConj hp)) ?_
      intro sf3 hpcf3 hrunf3 hspf3 hsp_alf3 hcsf3 hclf3 hLf3 hpost3
      dsimp only [rustCliDeallocBudgetSpec] at hpost3
      rw [hsp_3] at hspf3 hpost3
      have hsp_alf3' : (sf3.sp &&& 15#64 == 0#64) = true := hsp_alf3
      have hcs3 := hcsf3
      rcases hcs3 with ⟨hx19_f3, hx20_f3, _, _, _, _, _, hx26_f3, _, _, hfp_f3, hvregs_f3⟩
      rw [hx19_3] at hx19_f3; rw [hx20_3] at hx20_f3
      rw [hx26_3] at hx26_f3; rw [hfp_3] at hfp_f3; rw [hvregs_3] at hvregs_f3
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost3
      rcases hpost3 with ⟨⟨hpres_f3, _⟩, hpost3⟩
      have htr_f3 : sf3.trace = s0.trace := hpres_f3.2.1.trans htr_3
      set st_d := M.stepEvents (rustDeallocEvents seedCap.toNat 1) st
      have hpost3' : sf3.mem ⊨
          (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
           trAt A.repAlloc (sp + 56#64) trG tr ∗
           memRegion x.ret 48 ∗
           memRegion sp 56 ∗
           memRegion (sp + 320#64) 40 ∗
           speBodyAt A.repAlloc (utf8 "decrypt") (sp + 360#64) e ∗
           memRegion (sp + 400#64) 1008 ∗
           protocolAddressAt A.repAlloc x.rem x.remA ∗
           protocolAddressAt A.repAlloc x.loc x.locA ∗
           signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
           cliTapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool lim st_d sf3) ∗ R := by
        rw [stackAt_sub sp tryDecryptSubStack allocHookStack]
        simp only [sepConj_assoc] at hpost3 ⊢
        arm64_sep_close
      simp only [← sepConj_assoc] at hpost3'
      suffices ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) sf3 s' ∧
          (ErrTailStatePlaced (blkPl_434).base A lim st_d ctl x trG tr st1 e draws R s0 s' ∨
            (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R)) by
        obtain ⟨s', hsteps, hok | hpan⟩ := this
        · exact ⟨s', hsteps,
            Or.inl ⟨rustDeallocEvents seedCap.toNat 1,
              FreeOnlyEvs.singleton 1 seedCap.toNat, hok⟩⟩
        · exact ⟨s', hsteps, Or.inr hpan⟩
      unfold ErrTailStatePlaced CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailStatePlaced
      refine steps_done_of_sepWP_midMeta_placed (s0 := s0)
        (Rest := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = (s0.sp - 1504#64) + 320#64 ∧
          sf.readReg64 .x26 = speTag e ∧
          (sf.mem ⊨
            sessionStateAt (A.atState lim st_d sf) x.ss x.G.afterTrFrom st1 ∗
            trAt (A.atState lim st_d sf) ((s0.sp - 1504#64) + 56#64) trG tr ∗
            memRegion x.ret 48 ∗
            memRegion (s0.sp - 1504#64) 56 ∗
            memRegion ((s0.sp - 1504#64) + 320#64) 40 ∗
            speBodyAt (A.atState lim st_d sf) (utf8 "decrypt") ((s0.sp - 1504#64) + 360#64) e ∗
            memRegion ((s0.sp - 1504#64) + 400#64) 1008 ∗
            cliTryDecryptCommonHeapPlaced (A.atState lim st_d sf) ctl x draws s0 ∗ R))
        hpost3' hLf3 hclf3 ?_
      unfold errTailPC_at tryDecryptMidMetaCore cliTryDecryptCommonHeapPlaced
      rw [lsLogOff_eq_logOff_placed]
      simp only [sessionStateAt_atState, trAt_atState, speBodyAt_atState,
        protocolAddressAt_atState, signalMessageAt_atState, RustCliAllocBudget.atState_pool]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]; clear hsp29_eq
      rw [hsp_def]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps_sync_pool ((blkPl_434).base + 780#64)
      wp_done

set_option maxHeartbeats 800000 in
theorem pqRecv_recv_err_true_433_placed [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (S : SpqrModel) (fmtEnv : List AllocEvent → Prop := FormatInnerEnv)
    (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {sp seedCap seedPtr : BitVec 64} {msgW : BitVec 32}
    (hfits_fmt : FitsEnv M lim st fmtEnv)
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hfmt_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsFormatInnerSym) (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hdealloc_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hsp_def : s0.sp - 1504#64 = sp)
    (sf1 : State)
    (hpcf1 : sf1.pc = (blkPl_434).base + 1488#64)
    (hrunf1 : sf1.status = .Running)
    (hspf1 : sf1.sp = sp)
    (hsp_alf1 : sf1.spAligned = true)
    (hx19_1 : sf1.readReg64 .x19 = x.ret)
    (hx20_1 : sf1.readReg64 .x20 = sp + 320#64)
    (_hx23_1 : sf1.readReg64 .x23 = sp + 1280#64)
    (hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32)
    (hx25_1 : sf1.readReg64 .x25 = sp + 400#64)
    (hx28_1 : sf1.readReg64 .x28 = sp + 1280#64)
    (hfp_1 : sf1.readReg64 .fp = sp + 1408#64)
    (htrace1 : sf1.trace = s0.trace)
    (hvregs1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0)
    (hclf1 : LibsignalCodeRoLoaded lsmpl sf1.mem)
    (hLf1 : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded sf1.mem)
    (hpost1' : sf1.mem ⊨
      (((sp + 1288#64) ↦₈ 0#8) ∗
       memRegion ((sp + 1288#64) + 1#64) 7 ∗
       ((sp + 1280#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
       memRegion (sp + 1296#64) 32 ∗
       trAt A.repAlloc (sp + 56#64) trG tr ∗
       signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
       sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
       (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
         (seedPtr ↦ₛ mkg.seed) ∗
         memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
       memRegion x.ret 48 ∗
       memRegion sp 16 ∗
       ((sp + 16#64) ↦₆₄ seedPtr) ∗
       memRegion (sp + 24#64) 4 ∗
       ((sp + 28#64) ↦₃₂ msgW) ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₆₄ seedCap) ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 784 ∗
       ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
       ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
       memRegion (sp + 1116#64) 164 ∗
       memRegion (sp + 1328#64) 80 ∗
       protocolAddressAt A.repAlloc x.rem x.remA ∗
       protocolAddressAt A.repAlloc x.loc x.locA ∗
       cliTapeAfter ctl x.cur x.rest draws ∗
       lsLogOff ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool lim st sf1) ∗ R) :
    ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) sf1 s' ∧
      ((∃ evs2 evs3, fmtEnv evs2 ∧ FreeOnlyEvs evs3 ∧
          ErrTailStatePlaced (blkPl_434).base A lim
            (M.stepEvents evs3 (M.stepEvents evs2 st))
            ctl x trG tr st1 .invalidState draws R s0 s') ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R)) := by
  have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hspf1]; exact hsp_alf1
  rw [lsLogOff_eq_logOff_placed] at hpost1'
  simp only [← sepConj_assoc] at hpost1'
  refine steps_of_sepWP_placed_state hpost1' hLf1 hclf1
    (mid := lsρ lsFormatInnerSym)
    (RegMid := fun sm2 =>
      sm2.readReg64 .x8 = sp + 408#64 ∧
      sm2.readReg64 .lr = (blkPl_434).base + 2452#64 ∧
      sm2.readReg64 .x19 = x.ret ∧
      sm2.readReg64 .x20 = sp + 320#64 ∧
      (sm2.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm2.readReg64 .x25 = sp + 400#64 ∧
      sm2.readReg64 .fp = sp + 1408#64 ∧
      sm2.sp = sp ∧ sm2.spAligned = true ∧ sm2.trace = s0.trace ∧
      calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (P_mid := fun sm2 =>
      memRegion (sp + 408#64) 24 ∗ A.pool lim st sm2 ∗ stackAt sp extHookStack ∗
      sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
      trAt A.repAlloc (sp + 56#64) trG tr ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 16 ∗
      ((sp + 16#64) ↦₆₄ seedPtr) ∗
      memRegion (sp + 24#64) 16 ∗
      ((sp + 40#64) ↦₆₄ seedCap) ∗
      memRegion (sp + 48#64) 8 ∗
      memRegion (sp + 320#64) 88 ∗
      memRegion (sp + 432#64) 976 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      protocolAddressAt A.repAlloc x.loc x.locA ∗
      signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      cliTapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗
      memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - extHookStack) ∗
      tryDecryptSavedRegs s0.sp s0) ?_ ?_
  · wp_conv_pre =>
      rw [mr_cut sp 320 88 696 784 408#64,
        mr_cut sp 408 24 672 696 432#64,
        mr_cut sp 432 512 160 672 944#64,
        mr_cut sp 944 8 152 160 952#64,
        mr_cut sp 952 8 144 152 960#64,
        mr_cut sp 960 64 80 144 1024#64,
        mr_cut sp 1024 8 72 80 1032#64,
        mr_cut sp 1032 8 64 72 1040#64,
        mr_cut sp 1040 8 56 64 1048#64,
        mr_cut sp 1296 8 24 32 1304#64,
        mr_cut sp 1304 8 16 24 1312#64,
        stackAt_sub sp tryDecryptSubStack extHookStack]
      simp only [sepConj_assoc,
        memRegion_eight (sp + 944#64),
        memRegion_eight (sp + 952#64),
        memRegion_eight (sp + 1024#64),
        memRegion_eight (sp + 1032#64),
        memRegion_eight (sp + 1040#64),
        memRegion_eight (sp + 1296#64),
        memRegion_eight (sp + 1304#64)]
    wp_pull_exists
    refine sepWP_8_mr7_to_64 (fun hi_d => ?_)
    have hcbz0 := concat56_8_cbz64_zero hi_d
    wp_steps_sync_pool (lsρ lsFormatInnerSym)
    have hm24 : memRegion (sp + 24#64) 16 =
        memRegion (sp + 24#64) 4 ∗ (memRegion (sp + 28#64) 4 ∗ memRegion (sp + 32#64) 8) := by
      rw [mr_cut_add sp 24 4 12 (by decide), mr_cut_add sp 28 4 8 (by decide)]
    have hm432 : memRegion (sp + 432#64) 976 =
        memRegion (sp + 432#64) 512 ∗ (memRegion (sp + 944#64) 8 ∗ (memRegion (sp + 952#64) 8 ∗
        (memRegion (sp + 960#64) 64 ∗ (memRegion (sp + 1024#64) 8 ∗ (memRegion (sp + 1032#64) 8 ∗
        (memRegion (sp + 1040#64) 8 ∗ (memRegion (sp + 1048#64) 56 ∗ (memRegion (sp + 1104#64) 8 ∗
        (memRegion (sp + 1112#64) 4 ∗ (memRegion (sp + 1116#64) 164 ∗ (memRegion (sp + 1280#64) 8 ∗
        (memRegion (sp + 1288#64) 8 ∗ (memRegion (sp + 1296#64) 8 ∗ (memRegion (sp + 1304#64) 8 ∗
        (memRegion (sp + 1312#64) 16 ∗ memRegion (sp + 1328#64) 80))))))))))))))) := by
      rw [mr_cut_add sp 432 512 464 (by decide),
        mr_cut_add sp 944 8 456 (by decide),
        mr_cut_add sp 952 8 448 (by decide),
        mr_cut_add sp 960 64 384 (by decide),
        mr_cut_add sp 1024 8 376 (by decide),
        mr_cut_add sp 1032 8 368 (by decide),
        mr_cut_add sp 1040 8 360 (by decide),
        mr_cut_add sp 1048 56 304 (by decide),
        mr_cut_add sp 1104 8 296 (by decide),
        mr_cut_add sp 1112 4 292 (by decide),
        mr_cut_add sp 1116 164 128 (by decide),
        mr_cut_add sp 1280 8 120 (by decide),
        mr_cut_add sp 1288 8 112 (by decide),
        mr_cut_add sp 1296 8 104 (by decide),
        mr_cut_add sp 1304 8 96 (by decide),
        mr_cut_add sp 1312 16 80 (by decide)]
    rw [hm24, hm432]
    wp_done
  · intro sm2 hpcm2 hrunm2 hclm2 hLm2 ⟨hx8_2, hlr_2, hx19_2, hx20_2,
      hw24_2, hx25_2, hfp_2, hsp_2, hsp_al2, htr_2, hvregs_2⟩ hmm2
    have hpre_fmt : sm2.mem ⊨
        ((formatInnerBudgetEnvSpec M A lim fmtEnv).pre (sp + 408#64, st) sm2 ∗
         ((sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
           trAt A.repAlloc (sp + 56#64) trG tr ∗
           (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
             (seedPtr ↦ₛ mkg.seed) ∗
             memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
               (seedCap.toNat - mkg.seed.length)) ∗
           memRegion x.ret 48 ∗
           memRegion sp 16 ∗
           ((sp + 16#64) ↦₆₄ seedPtr) ∗
           memRegion (sp + 24#64) 16 ∗
           ((sp + 40#64) ↦₆₄ seedCap) ∗
           memRegion (sp + 48#64) 8 ∗
           memRegion (sp + 320#64) 88 ∗
           memRegion (sp + 432#64) 976 ∗
           protocolAddressAt A.repAlloc x.rem x.remA ∗
           protocolAddressAt A.repAlloc x.loc x.locA ∗
           signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
           cliTapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
             (tryDecryptSubStack - extHookStack) ∗
           tryDecryptSavedRegs s0.sp s0) ∗ R)) := by
      dsimp only [formatInnerBudgetEnvSpec]
      rw [hsp_2, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx8_2, hfits_fmt⟩, ?_⟩
      simp only [sepConj_assoc] at hmm2 ⊢
      arm64_sep_close
    refine steps_call_out_placed (sp + 408#64, st) hfmt_call
      hpcm2 hrunm2 hsp_al2 hlr_2 hclm2 hLm2 hpre_fmt
      (fun sf _ hp => False.elim (by
        dsimp only [formatInnerBudgetEnvSpec] at hp
        rw [sepConj_assoc] at hp
        exact not_satisfies_false_sepConj hp)) ?_
    intro sf2 hpcf2 hrunf2 hspf2 hsp_alf2 hcsf2 hclf2 hLf2 hpost2
    dsimp only [formatInnerBudgetEnvSpec] at hpost2
    rw [hsp_2] at hspf2 hpost2
    have hsp_alf2' : (sf2.sp &&& 15#64 == 0#64) = true := hsp_alf2
    have hcs2 := hcsf2
    rcases hcs2 with ⟨hx19_f2, hx20_f2, _, _, _, hx24_f2, hx25_f2, _, _, _, hfp_f2, hvregs_f2⟩
    rw [hx19_2] at hx19_f2; rw [hx20_2] at hx20_f2
    rw [hx25_2] at hx25_f2; rw [hfp_2] at hfp_f2; rw [hvregs_2] at hvregs_f2
    have hw24_f2 : (sf2.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_f2]; exact hw24_2
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost2
    rcases hpost2 with ⟨evs2, hpost2⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost2
    rcases hpost2 with ⟨⟨htr_f2, hevs2⟩, hpost2⟩
    rw [htr_2] at htr_f2
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost2
    rcases hpost2 with ⟨fmtBs, hpost2⟩
    unfold vecU8 at hpost2
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost2
    rcases hpost2 with ⟨fmtCap, fmtPtr, hpost2⟩
    set st_f := M.stepEvents evs2 st
    have hpost2' : sf2.mem ⊨
        vecU8At A.repAlloc (sp + 408#64) fmtCap fmtPtr fmtBs ∗
        (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         trAt A.repAlloc (sp + 56#64) trG tr ∗
         (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
           (seedPtr ↦ₛ mkg.seed) ∗
           memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
             (seedCap.toNat - mkg.seed.length)) ∗
         memRegion x.ret 48 ∗
         memRegion sp 16 ∗
         ((sp + 16#64) ↦₆₄ seedPtr) ∗
         memRegion (sp + 24#64) 16 ∗
         ((sp + 40#64) ↦₆₄ seedCap) ∗
         memRegion (sp + 48#64) 8 ∗
         memRegion (sp + 320#64) 88 ∗
         memRegion (sp + 432#64) 976 ∗
         protocolAddressAt A.repAlloc x.rem x.remA ∗
         protocolAddressAt A.repAlloc x.loc x.locA ∗
         signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
         cliTapeAfter ctl x.cur x.rest draws ∗
         logOff tryDecryptPlacedImg ∗
         stackAt sp tryDecryptSubStack ∗
         tryDecryptSavedRegs s0.sp s0 ∗
         A.pool lim st_f sf2) ∗ R := by
      rw [stackAt_sub sp tryDecryptSubStack extHookStack]
      simp only [sepConj_assoc] at hpost2 ⊢
      arm64_sep_close
    unfold vecU8At vecHeader at hpost2'
    simp only [sepConj_assoc] at hpost2'
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
      satisfies_pure_sepConj] at hpost2'
    rcases hpost2' with ⟨⟨hfb1, hfb2, hfb3⟩, hpost2'⟩
    have hfb : fmtBs.length ≤ fmtCap.toNat ∧ fmtCap.toNat < 2 ^ 63 ∧ fmtPtr ≠ 0 :=
      ⟨hfb1, hfb2, hfb3⟩
    have hpost2_ro := lsro_intro_chk hclf2.2 lsroCheck_tryDecryptCoinsRoSym hpost2'
    simp only [← sepConj_assoc] at hpost2_ro
    refine steps_of_sepWP_placed_state hpost2_ro hLf2 hclf2
      (mid := (blkPl_434).base + 2500#64)
      (RegMid := fun st2 =>
        st2.readReg64 .x19 = x.ret ∧
        st2.readReg64 .x20 = sp + 320#64 ∧
        st2.readReg64 .x26 = speTag .invalidState ∧
        st2.readReg64 .fp = sp + 1408#64 ∧
        st2.sp = sp ∧ st2.spAligned = true ∧ st2.trace = s0.trace ∧
        calleeSavedVRegs st2 = calleeSavedVRegs s0)
      (P_mid := fun st2 =>
        sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
        trAt A.repAlloc (sp + 56#64) trG tr ∗
        (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
          (seedPtr ↦ₛ mkg.seed) ∗
          memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
            (seedCap.toNat - mkg.seed.length)) ∗
        memRegion x.ret 48 ∗
        memRegion sp 16 ∗
        ((sp + 16#64) ↦₆₄ seedPtr) ∗
        memRegion (sp + 24#64) 16 ∗
        ((sp + 40#64) ↦₆₄ seedCap) ∗
        memRegion (sp + 48#64) 8 ∗
        memRegion (sp + 320#64) 40 ∗
        speBodyAt A.repAlloc (utf8 "decrypt") (sp + 360#64) .invalidState ∗
        memRegion (sp + 400#64) 1008 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗
        signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
        cliTapeAfter ctl x.cur x.rest draws ∗
        logOff tryDecryptPlacedImg ∗
        stackAt sp tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool lim st_f st2) ?_ ?_
    · wp_conv_pre =>
        rw [mr_cut sp 320 40 48 88 360#64,
          mr_cut sp 360 8 40 48 368#64,
          mr_cut sp 368 8 32 40 376#64,
          mr_cut sp 376 8 24 32 384#64,
          mr_cut sp 384 8 16 24 392#64,
          mr_cut sp 392 8 8 16 400#64,
          mr_cut sp 432 8 968 976 440#64,
          mr_cut sp 440 8 960 968 448#64]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc,
          memRegion_eight (sp + 360#64),
          memRegion_eight (sp + 368#64),
          memRegion_eight (sp + 376#64),
          memRegion_eight (sp + 384#64),
          memRegion_eight (sp + 392#64),
          memRegion_eight (sp + 400#64),
          memRegion_eight (sp + 432#64),
          memRegion_eight (sp + 440#64)]
      dsimp only [speTag, speWord]
      wp_pull_exists
      apply sepWP_seg_ls_vm
        (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
        blkLib_eq_434 (mid := (blkPl_434).base + 2500#64)
      intro _m_strip
      have _hpc_strip : (sf2.setMem _m_strip).pc = (blkPl_434).base + 2452#64 := by simpa using hpcf2
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
      refine SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by wp_norm_lhs))
        (hnext := ?_)
      refine SepWP.focus_weaken
        (speBodyAt_invalidState_fold A.repAlloc sp fmtCap fmtPtr _ fmtBs hfb) (by sep_focus) ?_
      have hm400 : memRegion (sp + 400#64) 1008 =
          memRegion (sp + 400#64) 8 ∗ (memRegion (sp + 408#64) 8 ∗ (memRegion (sp + 416#64) 8 ∗
          (memRegion (sp + 424#64) 8 ∗ (memRegion (sp + 432#64) 8 ∗ (memRegion (sp + 440#64) 8 ∗
          memRegion (sp + 448#64) 960))))) := by
        rw [mr_cut_add sp 400 8 1000 (by decide),
          mr_cut_add sp 408 8 992 (by decide),
          mr_cut_add sp 416 8 984 (by decide),
          mr_cut_add sp 424 8 976 (by decide),
          mr_cut_add sp 432 8 968 (by decide),
          mr_cut_add sp 440 8 960 (by decide)]
      rw [hm400]
      wp_done
    · intro st2 hpc2 hrun2 hcl2 hL2 ⟨hx19_2, hx20_2, hx26_2, hfp_2, hsp_2, hsp_al2, htr_2, hvregs_2⟩ hm2
      rw [← lsLogOff_eq_logOff_placed] at hm2
      obtain ⟨s', hsteps, (⟨evs3, hevs3, hok⟩ | hpan)⟩ :=
        pqRecv_dealloc_tail_433_placed C A lim st_f ctl S H x trG tr st1 mkg draws R s0
          (seedPtr := seedPtr) hsp0_al' hseed1 hseed2 hdealloc_call hsp_def .invalidState
          st2 hpc2 hrun2 hsp_2 hsp_al2 hfp_2 htr_2 hvregs_2 hcl2 hL2 hx19_2 hx20_2 hx26_2 hm2
      · exact ⟨s', hsteps, Or.inl ⟨evs2, evs3, hevs2, hevs3, hok⟩⟩
      · exact ⟨s', hsteps, Or.inr hpan⟩

set_option maxHeartbeats 800000 in
theorem pqRecv_recv_err_false_433_placed [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (S : SpqrModel) (fmtEnv : List AllocEvent → Prop := FormatInnerEnv)
    (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {sp seedCap seedPtr : BitVec 64} {msgW : BitVec 32} {d : BitVec 8}
    (hfits_fmt : FitsEnv M lim st fmtEnv)
    (hmsgW : msgW.setWidth 8 = msgTypeByte x.msgType)
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hfmt_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsFormatInnerSym) (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hdealloc_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hd_ne : d ≠ 0#8)
    (sf1 : State)
    (hpcf1 : sf1.pc = (blkPl_434).base + 1488#64)
    (hrunf1 : sf1.status = .Running)
    (hspf1 : sf1.sp = sp)
    (hsp_alf1 : sf1.spAligned = true)
    (hx19_1 : sf1.readReg64 .x19 = x.ret)
    (hx20_1 : sf1.readReg64 .x20 = sp + 320#64)
    (_hx23_1 : sf1.readReg64 .x23 = sp + 1280#64)
    (hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32)
    (hx25_1 : sf1.readReg64 .x25 = sp + 400#64)
    (hx28_1 : sf1.readReg64 .x28 = sp + 1280#64)
    (hfp_1 : sf1.readReg64 .fp = sp + 1408#64)
    (htrace1 : sf1.trace = s0.trace)
    (hvregs1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0)
    (hclf1 : LibsignalCodeRoLoaded lsmpl sf1.mem)
    (hLf1 : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded sf1.mem)
    (hpost1' : sf1.mem ⊨
      (((sp + 1288#64) ↦₈ d) ∗
       memRegion ((sp + 1288#64) + 1#64) 7 ∗
       ((sp + 1280#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
       memRegion (sp + 1296#64) 32 ∗
       trAt A.repAlloc (sp + 56#64) trG tr ∗
       signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
       sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
       (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
         (seedPtr ↦ₛ mkg.seed) ∗
         memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
       memRegion x.ret 48 ∗
       memRegion sp 16 ∗
       ((sp + 16#64) ↦₆₄ seedPtr) ∗
       memRegion (sp + 24#64) 4 ∗
       ((sp + 28#64) ↦₃₂ msgW) ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₆₄ seedCap) ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 784 ∗
       ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
       ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
       memRegion (sp + 1116#64) 164 ∗
       memRegion (sp + 1328#64) 80 ∗
       protocolAddressAt A.repAlloc x.rem x.remA ∗
       protocolAddressAt A.repAlloc x.loc x.locA ∗
       cliTapeAfter ctl x.cur x.rest draws ∗
       lsLogOff ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool lim st sf1) ∗ R) :
    ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) sf1 s' ∧
      ((∃ evs2 evs3, fmtEnv evs2 ∧ FreeOnlyEvs evs3 ∧
          ErrTailStatePlaced (blkPl_434).base A lim
            (M.stepEvents evs3 (M.stepEvents evs2 st))
            ctl x trG tr st1 (.invalidMessage x.msgType .pqRatchet) draws R s0 s') ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R)) := by
  have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hspf1]; exact hsp_alf1
  have hd_cbz1 : (BitVec.setWidth 32 d == 0#32) = false := byte_ne_zero_cbz32 hd_ne
  have hd_cbz2 : (BitVec.setWidth 32 (BitVec.setWidth 64 d) == 0#32) = false :=
    byte_ne_zero_cbz64_32 hd_ne
  rw [lsLogOff_eq_logOff_placed] at hpost1'
  simp only [← sepConj_assoc] at hpost1'
  refine steps_of_sepWP_placed_state hpost1' hLf1 hclf1
    (mid := lsρ lsFormatInnerSym)
    (RegMid := fun sm2 =>
      sm2.readReg64 .x8 = sp + 408#64 ∧
      sm2.readReg64 .lr = (blkPl_434).base + 2156#64 ∧
      sm2.readReg64 .x19 = x.ret ∧
      sm2.readReg64 .x20 = sp + 320#64 ∧
      (sm2.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm2.readReg64 .x25 = sp + 400#64 ∧
      sm2.readReg64 .x26 = speTag (.invalidMessage x.msgType .pqRatchet) ∧
      sm2.readReg64 .fp = sp + 1408#64 ∧
      sm2.sp = sp ∧ sm2.spAligned = true ∧ sm2.trace = s0.trace ∧
      calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (P_mid := fun sm2 =>
      memRegion (sp + 408#64) 24 ∗ A.pool lim st sm2 ∗ stackAt sp extHookStack ∗
      sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
      trAt A.repAlloc (sp + 56#64) trG tr ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 16 ∗
      ((sp + 16#64) ↦₆₄ seedPtr) ∗
      memRegion (sp + 24#64) 4 ∗
      ((sp + 28#64) ↦₃₂ msgW) ∗
      memRegion (sp + 32#64) 8 ∗
      ((sp + 40#64) ↦₆₄ seedCap) ∗
      memRegion (sp + 48#64) 8 ∗
      memRegion (sp + 320#64) 88 ∗
      memRegion (sp + 432#64) 976 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      protocolAddressAt A.repAlloc x.loc x.locA ∗
      signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      cliTapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗
      memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - extHookStack) ∗
      tryDecryptSavedRegs s0.sp s0) ?_ ?_
  · dsimp only [speTag, speWord]
    wp_conv_pre =>
      rw [mr_cut sp 320 88 696 784 408#64,
        mr_cut sp 408 24 672 696 432#64,
        mr_cut sp 432 512 160 672 944#64,
        mr_cut sp 944 8 152 160 952#64,
        mr_cut sp 952 8 144 152 960#64,
        mr_cut sp 960 64 80 144 1024#64,
        mr_cut sp 1024 8 72 80 1032#64,
        mr_cut sp 1032 8 64 72 1040#64,
        mr_cut sp 1040 8 56 64 1048#64,
        mr_cut sp 1296 8 24 32 1304#64,
        mr_cut sp 1304 8 16 24 1312#64,
        stackAt_sub sp tryDecryptSubStack extHookStack]
      simp only [sepConj_assoc,
        memRegion_eight (sp + 944#64),
        memRegion_eight (sp + 952#64),
        memRegion_eight (sp + 1024#64),
        memRegion_eight (sp + 1032#64),
        memRegion_eight (sp + 1040#64),
        memRegion_eight (sp + 1296#64),
        memRegion_eight (sp + 1304#64)]
    wp_pull_exists
    refine sepWP_8_mr7_to_64 (fun hi_d => ?_)
    have hcbz1 := concat56_8_cbz64_ne_zero hi_d hd_ne
    have hcbz2 := concat56_8_cbz32_ne_zero hi_d hd_ne
    wp_steps_sync_pool (lsρ lsFormatInnerSym)
    have hm432 : memRegion (sp + 432#64) 976 =
        memRegion (sp + 432#64) 512 ∗ (memRegion (sp + 944#64) 8 ∗ (memRegion (sp + 952#64) 8 ∗
        (memRegion (sp + 960#64) 64 ∗ (memRegion (sp + 1024#64) 8 ∗ (memRegion (sp + 1032#64) 8 ∗
        (memRegion (sp + 1040#64) 8 ∗ (memRegion (sp + 1048#64) 56 ∗ (memRegion (sp + 1104#64) 8 ∗
        (memRegion (sp + 1112#64) 4 ∗ (memRegion (sp + 1116#64) 164 ∗ (memRegion (sp + 1280#64) 8 ∗
        (memRegion (sp + 1288#64) 8 ∗ (memRegion (sp + 1296#64) 8 ∗ (memRegion (sp + 1304#64) 8 ∗
        (memRegion (sp + 1312#64) 16 ∗ memRegion (sp + 1328#64) 80))))))))))))))) := by
      rw [mr_cut_add sp 432 512 464 (by decide),
        mr_cut_add sp 944 8 456 (by decide),
        mr_cut_add sp 952 8 448 (by decide),
        mr_cut_add sp 960 64 384 (by decide),
        mr_cut_add sp 1024 8 376 (by decide),
        mr_cut_add sp 1032 8 368 (by decide),
        mr_cut_add sp 1040 8 360 (by decide),
        mr_cut_add sp 1048 56 304 (by decide),
        mr_cut_add sp 1104 8 296 (by decide),
        mr_cut_add sp 1112 4 292 (by decide),
        mr_cut_add sp 1116 164 128 (by decide),
        mr_cut_add sp 1280 8 120 (by decide),
        mr_cut_add sp 1288 8 112 (by decide),
        mr_cut_add sp 1296 8 104 (by decide),
        mr_cut_add sp 1304 8 96 (by decide),
        mr_cut_add sp 1312 16 80 (by decide)]
    rw [hm432]
    wp_done
  · intro sm2 hpcm2 hrunm2 hclm2 hLm2 ⟨hx8_2, hlr_2, hx19_2, hx20_2,
      hw24_2, hx25_2, hx26_2, hfp_2, hsp_2, hsp_al2, htr_2, hvregs_2⟩ hmm2
    have hpre_fmt : sm2.mem ⊨
        ((formatInnerBudgetEnvSpec M A lim fmtEnv).pre (sp + 408#64, st) sm2 ∗
         ((sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
           trAt A.repAlloc (sp + 56#64) trG tr ∗
           (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
             (seedPtr ↦ₛ mkg.seed) ∗
             memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
               (seedCap.toNat - mkg.seed.length)) ∗
           memRegion x.ret 48 ∗
           memRegion sp 16 ∗
           ((sp + 16#64) ↦₆₄ seedPtr) ∗
           memRegion (sp + 24#64) 4 ∗
           ((sp + 28#64) ↦₃₂ msgW) ∗
           memRegion (sp + 32#64) 8 ∗
           ((sp + 40#64) ↦₆₄ seedCap) ∗
           memRegion (sp + 48#64) 8 ∗
           memRegion (sp + 320#64) 88 ∗
           memRegion (sp + 432#64) 976 ∗
           protocolAddressAt A.repAlloc x.rem x.remA ∗
           protocolAddressAt A.repAlloc x.loc x.locA ∗
           signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
           cliTapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
             (tryDecryptSubStack - extHookStack) ∗
           tryDecryptSavedRegs s0.sp s0) ∗ R)) := by
      dsimp only [formatInnerBudgetEnvSpec]
      rw [hsp_2, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx8_2, hfits_fmt⟩, ?_⟩
      simp only [sepConj_assoc] at hmm2 ⊢
      arm64_sep_close
    refine steps_call_out_placed (sp + 408#64, st) hfmt_call
      hpcm2 hrunm2 hsp_al2 hlr_2 hclm2 hLm2 hpre_fmt
      (fun sf _ hp => False.elim (by
        dsimp only [formatInnerBudgetEnvSpec] at hp
        rw [sepConj_assoc] at hp
        exact not_satisfies_false_sepConj hp)) ?_
    intro sf2 hpcf2 hrunf2 hspf2 hsp_alf2 hcsf2 hclf2 hLf2 hpost2
    dsimp only [formatInnerBudgetEnvSpec] at hpost2
    rw [hsp_2] at hspf2 hpost2
    have hsp_alf2' : (sf2.sp &&& 15#64 == 0#64) = true := hsp_alf2
    have hcs2 := hcsf2
    rcases hcs2 with ⟨hx19_f2, hx20_f2, _, _, _, hx24_f2, hx25_f2, hx26_f2, _, _, hfp_f2, hvregs_f2⟩
    rw [hx19_2] at hx19_f2; rw [hx20_2] at hx20_f2
    rw [hx25_2] at hx25_f2; rw [hx26_2] at hx26_f2; rw [hfp_2] at hfp_f2; rw [hvregs_2] at hvregs_f2
    have hw24_f2 : (sf2.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_f2]; exact hw24_2
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost2
    rcases hpost2 with ⟨evs2, hpost2⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost2
    rcases hpost2 with ⟨⟨htr_f2, hevs2⟩, hpost2⟩
    rw [htr_2] at htr_f2
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost2
    rcases hpost2 with ⟨fmtBs, hpost2⟩
    unfold vecU8 at hpost2
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost2
    rcases hpost2 with ⟨fmtCap, fmtPtr, hpost2⟩
    set st_f := M.stepEvents evs2 st
    have hpost2' : sf2.mem ⊨
        vecU8At A.repAlloc (sp + 408#64) fmtCap fmtPtr fmtBs ∗
        (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         trAt A.repAlloc (sp + 56#64) trG tr ∗
         (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
           (seedPtr ↦ₛ mkg.seed) ∗
           memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
             (seedCap.toNat - mkg.seed.length)) ∗
         memRegion x.ret 48 ∗
         memRegion sp 16 ∗
         ((sp + 16#64) ↦₆₄ seedPtr) ∗
         memRegion (sp + 24#64) 4 ∗
         ((sp + 28#64) ↦₃₂ msgW) ∗
         memRegion (sp + 32#64) 8 ∗
         ((sp + 40#64) ↦₆₄ seedCap) ∗
         memRegion (sp + 48#64) 8 ∗
         memRegion (sp + 320#64) 88 ∗
         memRegion (sp + 432#64) 976 ∗
         protocolAddressAt A.repAlloc x.rem x.remA ∗
         protocolAddressAt A.repAlloc x.loc x.locA ∗
         signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
         cliTapeAfter ctl x.cur x.rest draws ∗
         logOff tryDecryptPlacedImg ∗
         stackAt sp tryDecryptSubStack ∗
         tryDecryptSavedRegs s0.sp s0 ∗
         A.pool lim st_f sf2) ∗ R := by
      rw [stackAt_sub sp tryDecryptSubStack extHookStack]
      simp only [sepConj_assoc] at hpost2 ⊢
      arm64_sep_close
    unfold vecU8At vecHeader at hpost2'
    simp only [sepConj_assoc] at hpost2'
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
      satisfies_pure_sepConj] at hpost2'
    rcases hpost2' with ⟨⟨hfb1, hfb2, hfb3⟩, hpost2'⟩
    have hfb : fmtBs.length ≤ fmtCap.toNat ∧ fmtCap.toNat < 2 ^ 63 ∧ fmtPtr ≠ 0 :=
      ⟨hfb1, hfb2, hfb3⟩
    simp only [← sepConj_assoc] at hpost2'
    refine steps_of_sepWP_placed_state hpost2' hLf2 hclf2
      (mid := (blkPl_434).base + 2500#64)
      (RegMid := fun st2 =>
        st2.readReg64 .x19 = x.ret ∧
        st2.readReg64 .x20 = sp + 320#64 ∧
        st2.readReg64 .x26 = speTag (.invalidMessage x.msgType .pqRatchet) ∧
        st2.readReg64 .fp = sp + 1408#64 ∧
        st2.sp = sp ∧ st2.spAligned = true ∧ st2.trace = s0.trace ∧
        calleeSavedVRegs st2 = calleeSavedVRegs s0)
      (P_mid := fun st2 =>
        sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
        trAt A.repAlloc (sp + 56#64) trG tr ∗
        (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
          (seedPtr ↦ₛ mkg.seed) ∗
          memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
            (seedCap.toNat - mkg.seed.length)) ∗
        memRegion x.ret 48 ∗
        memRegion sp 16 ∗
        ((sp + 16#64) ↦₆₄ seedPtr) ∗
        memRegion (sp + 24#64) 16 ∗
        ((sp + 40#64) ↦₆₄ seedCap) ∗
        memRegion (sp + 48#64) 8 ∗
        memRegion (sp + 320#64) 40 ∗
        speBodyAt A.repAlloc (utf8 "decrypt") (sp + 360#64)
          (.invalidMessage x.msgType .pqRatchet) ∗
        memRegion (sp + 400#64) 1008 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗
        signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
        cliTapeAfter ctl x.cur x.rest draws ∗
        logOff tryDecryptPlacedImg ∗
        stackAt sp tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool lim st_f st2) ?_ ?_
    · wp_conv_pre =>
        rw [mr_cut sp 320 40 48 88 360#64,
          mr_cut sp 360 8 40 48 368#64,
          mr_cut sp 368 8 32 40 376#64,
          mr_cut sp 376 8 24 32 384#64,
          mr_cut sp 384 8 16 24 392#64,
          mr_cut sp 392 8 8 16 400#64,
          mr_cut sp 432 1 975 976 433#64,
          mr_cut sp 433 7 968 975 440#64,
          mr_cut sp 440 8 960 968 448#64]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc,
          memRegion_eight (sp + 360#64),
          memRegion_eight (sp + 368#64),
          memRegion_eight (sp + 376#64),
          memRegion_eight (sp + 384#64),
          memRegion_eight (sp + 392#64),
          memRegion_eight (sp + 400#64),
          memRegion_one (sp + 432#64),
          memRegion_eight (sp + 440#64)]
      wp_pull_exists
      apply sepWP_seg_ls_vm
        (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
        blkLib_eq_434 (mid := (blkPl_434).base + 2500#64)
      intro _m_strip
      wp_steps
      rw [show sp + 433#64 = (sp + 432#64) + 1#64 by rw [BitVec.add_assoc]; rfl]
      refine SepWP.focus_weaken
        (pointsTo8_memRegion7_to_64 (sp + 432#64) (msgTypeByte x.msgType)) (by sep_focus) ?_
      wp_pull_exists
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
      refine SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by wp_norm_lhs))
        (hnext := ?_)
      refine SepWP.focus_weaken
        (pointsTo64_to_8_memRegion7 (sp + 384#64) _ (msgTypeByte x.msgType)) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (speBodyAt_pqRatchet_fold A.repAlloc sp fmtCap fmtPtr _ fmtBs x.msgType hfb)
        (by sep_focus) ?_
      have hm24 : memRegion (sp + 24#64) 16 =
          memRegion (sp + 24#64) 4 ∗ (memRegion (sp + 28#64) 4 ∗ memRegion (sp + 32#64) 8) := by
        rw [mr_cut_add sp 24 4 12 (by decide), mr_cut_add sp 28 4 8 (by decide)]
      have hm400 : memRegion (sp + 400#64) 1008 =
          memRegion (sp + 400#64) 8 ∗ (memRegion (sp + 408#64) 8 ∗ (memRegion (sp + 416#64) 8 ∗
          (memRegion (sp + 424#64) 8 ∗ (memRegion (sp + 432#64) 8 ∗ (memRegion (sp + 440#64) 8 ∗
          memRegion (sp + 448#64) 960))))) := by
        rw [mr_cut_add sp 400 8 1000 (by decide),
          mr_cut_add sp 408 8 992 (by decide),
          mr_cut_add sp 416 8 984 (by decide),
          mr_cut_add sp 424 8 976 (by decide),
          mr_cut_add sp 432 8 968 (by decide),
          mr_cut_add sp 440 8 960 (by decide)]
      rw [hm24, hm400]
      wp_done
    · intro st2 hpc2 hrun2 hcl2 hL2 ⟨hx19_2, hx20_2, hx26_2, hfp_2, hsp_2, hsp_al2, htr_2, hvregs_2⟩ hm2
      rw [← lsLogOff_eq_logOff_placed] at hm2
      obtain ⟨s', hsteps, (⟨evs3, hevs3, hok⟩ | hpan)⟩ :=
        pqRecv_dealloc_tail_433_placed C A lim st_f ctl S H x trG tr st1 mkg draws R s0
          (seedPtr := seedPtr) hsp0_al' hseed1 hseed2 hdealloc_call hsp_def
          (.invalidMessage x.msgType .pqRatchet)
          st2 hpc2 hrun2 hsp_2 hsp_al2 hfp_2 htr_2 hvregs_2 hcl2 hL2 hx19_2 hx20_2 hx26_2 hm2
      · exact ⟨s', hsteps, Or.inl ⟨evs2, evs3, hevs2, hevs3, hok⟩⟩
      · exact ⟨s', hsteps, Or.inr hpan⟩

end LibsignalBinary.Proofs.Cli.SpqrV1.M4.SpqrRecvErrPlacedBudget
