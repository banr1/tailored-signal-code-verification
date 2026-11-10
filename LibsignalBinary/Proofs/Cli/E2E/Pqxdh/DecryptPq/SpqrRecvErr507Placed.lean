/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.VerifyMacTrap507Placed
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecv
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import all Init.Data.String.Defs

/-!
# Relocatable `[LibsignalPlacement]` SPQR Recv Error-Path Helpers (`blkPl_508`)

Proves `pqRecv_dealloc_tail_507_placed`, `pqRecv_recv_err_true_507_placed`, and
`pqRecv_recv_err_false_507_placed` for
`try_decrypt_with_state::<signal_session_handshake::Coins>` (`blkPC_508` / `blkPl_508`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.CliHandshake.TryDecPlaced

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet hiding memRegion_eight
open CryptoVerification.LibsignalTripleRatchet.Decrypt hiding
  ErrTailStatePlaced ErrTailStateXPlaced LoadRatchetStatePlaced FindChainStatePlaced
  DhStepStatePlaced ConsumeMsgKeyStatePlaced PqRecvStatePlaced DeriveKeysStatePlaced
  VerifyMacStatePlaced AesDecryptStatePlaced ApplyRatchetStatePlaced
  ErrTailSeamPlaced S0SeamPlaced S1SeamPlaced S2SeamPlaced S3SeamPlaced S4SeamPlaced
  S5SeamPlaced S6SeamPlaced S7SeamPlaced S8SeamPlaced S9SeamPlaced
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt
open CryptoVerification.Cli.SpqrV1.M4

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

abbrev lsTryDecryptHsCoinsRoSym : String :=
  "libsignal_cli_handshake:.rodata..Lanon.54"

theorem lsroCheck_tryDecryptHsCoinsRoSym :
    lsroCheck lsTryDecryptHsCoinsRoSym (utf8 "decrypt") = true := by
  decide +kernel

set_option maxHeartbeats 1200000 in
theorem pqRecv_dealloc_tail_507_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {sp seedCap seedPtr : BitVec 64}
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hdealloc_call : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (e : SignalProtocolError) (st2 : State)
    (hpc2 : st2.pc = (blkPl_508).base + 2500#64)
    (hrun2 : st2.status = .Running)
    (hsp2 : st2.sp = sp)
    (hsp_al2 : st2.spAligned = true)
    (hfp2 : st2.readReg64 .fp = sp + 1408#64)
    (htr2 : st2.trace = s0.trace)
    (hvregs2 : calleeSavedVRegs st2 = calleeSavedVRegs s0)
    (hcl2 : LibsignalCodeRoLoaded lsmpl st2.mem)
    (hL2 : ((blkPC_508).rebase (blkPl_508).base H).CodeLoaded st2.mem)
    (hx19_2 : st2.readReg64 .x19 = x.ret)
    (hx20_2 : st2.readReg64 .x20 = sp + 320#64)
    (hx26_2 : st2.readReg64 .x26 = speTag e)
    (hm2 : st2.mem ⊨
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG tr ∗
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
       speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
       memRegion (sp + 400#64) 1008 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       cliTapeAfter ctl x.cur x.rest draws ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps ((blkPC_508).rebase (blkPl_508).base H) st2 s' ∧
      (ErrTailStatePlaced (blkPl_508).base A ctl x trG tr st1 e draws R s0 s' ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)) := by
  have hsp_al2' : (st2.sp &&& 15#64 == 0#64) = true := hsp_al2
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp2]; exact hsp_al2
  rw [lsLogOff_eq_logOff_placed] at hm2
  simp only [← sepConj_assoc] at hm2
  by_cases hsc : seedCap = 0
  · simp only [hsc, ↓reduceIte] at hm2
    subst hsc
    unfold ErrTailStatePlaced
    refine steps_done_of_sepWP_midMeta_placed (s0 := s0)
      (Rest := fun sf =>
        sf.readReg64 .x19 = x.ret ∧
        sf.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64 ∧
        sf.readReg64 .x26 = speTag e ∧
        (sf.mem ⊨
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
          memRegion x.ret 48 ∗
          memRegion (s0.sp - 1504#64) 0x38 ∗
          memRegion ((s0.sp - 1504#64) + 0x140#64) 0x28 ∗
          speBodyAt A (utf8 "decrypt") ((s0.sp - 1504#64) + 0x168#64) e ∗
          memRegion ((s0.sp - 1504#64) + 0x190#64) 0x3f0 ∗
          cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R))
      hm2 hL2 hcl2 ?_
    unfold errTailPC_at tryDecryptMidMetaCore cliTryDecryptCommonHeapPlaced
    rw [lsLogOff_eq_logOff_placed]
    rw [show (0x30c#64 : BitVec 64) = 780#64 by rfl]
    have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
    rw [hsp29_eq]; clear hsp29_eq
    rw [hsp_def]
    wp_conv_pre => simp only [sepConj_assoc]
    wp_steps
    refine SepWP.focus_weaken (sp56_weaken sp seedPtr 0#64) (by sep_focus) ?_
    wp_done
  · simp only [hsc, ↓reduceIte] at hm2
    have hsc_beq : (seedCap == 0#64) = false := beq_false_of_ne hsc
    refine steps_of_sepWP_placed hm2 hL2 hcl2
      (mid := lsρ lsRustDeallocSym)
      (RegMid := fun sm3 =>
        sm3.readReg64 .x0 = seedPtr ∧
        sm3.readReg64 .x1 = seedCap ∧
        sm3.readReg64 .x2 = 1#64 ∧
        sm3.readReg64 .lr = (blkPl_508).base + 2520#64 ∧
        sm3.readReg64 .x19 = x.ret ∧
        sm3.readReg64 .x20 = sp + 320#64 ∧
        sm3.readReg64 .x26 = speTag e ∧
        sm3.readReg64 .fp = sp + 1408#64 ∧
        sm3.sp = sp ∧ sm3.spAligned = true ∧ sm3.trace = s0.trace ∧
        calleeSavedVRegs sm3 = calleeSavedVRegs s0)
      (P_mid :=
        A.pool ∗ A.live seedPtr seedCap.toNat 1 ∗ memRegion seedPtr seedCap.toNat ∗
        stackAt sp allocHookStack ∗
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 56#64) trG tr ∗
        memRegion x.ret 48 ∗
        memRegion sp 56 ∗
        memRegion (sp + 320#64) 40 ∗
        speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
        memRegion (sp + 400#64) 1008 ∗
        protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        cliTapeAfter ctl x.cur x.rest draws ∗
        logOff tryDecryptPlacedImg ∗
        memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - allocHookStack) ∗
        tryDecryptSavedRegs s0.sp s0) ?_ ?_
    · wp_conv_pre =>
        rw [stackAt_sub sp tryDecryptSubStack allocHookStack]
        simp only [sepConj_assoc]
      wp_steps
      refine SepWP.focus_weaken (sp56_weaken sp seedPtr seedCap) (by sep_focus) ?_
      refine SepWP.focus_weaken (buf_to_mr seedPtr mkg.seed seedCap.toNat hseed1 hseed2) (by sep_focus) ?_
      wp_done
    · intro sm3 hpcm3 hrunm3 hclm3 hLm3 ⟨hx0_3, hx1_3, hx2_3, hlr_3,
        hx19_3, hx20_3, hx26_3, hfp_3, hsp_3, hsp_al3, htr_3, hvregs_3⟩ hmm3
      have hpre_dealloc : sm3.mem ⊨
          ((rustDeallocSpec A).pre (seedPtr, seedCap.toNat, 1) sm3 ∗
           (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
            trAt A (sp + 56#64) trG tr ∗
            memRegion x.ret 48 ∗
            memRegion sp 56 ∗
            memRegion (sp + 320#64) 40 ∗
            speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
            memRegion (sp + 400#64) 1008 ∗
            protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            cliTapeAfter ctl x.cur x.rest draws ∗
            logOff tryDecryptPlacedImg ∗
            memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - allocHookStack) ∗
            tryDecryptSavedRegs s0.sp s0) ∗ R) := by
        dsimp only [rustDeallocSpec]
        rw [hsp_3, sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0_3, by rw [hx1_3], by rw [hx2_3]; rfl⟩, ?_⟩
        simp only [sepConj_assoc] at hmm3 ⊢
        arm64_sep_close
      refine steps_call_placed (seedPtr, seedCap.toNat, 1) hdealloc_call
        hpcm3 hrunm3 hsp_al3 hlr_3 hclm3 hLm3 hpre_dealloc
        (fun sf _ hp => False.elim (by
          dsimp only [rustDeallocSpec] at hp
          rw [sepConj_assoc] at hp
          exact not_satisfies_false_sepConj hp)) ?_
      intro sf3 hpcf3 hrunf3 hspf3 hsp_alf3 hcsf3 hclf3 hLf3 hpost3
      dsimp only [rustDeallocSpec] at hpost3
      rw [hsp_3] at hspf3 hpost3
      have hsp_alf3' : (sf3.sp &&& 15#64 == 0#64) = true := hsp_alf3
      have hcs3 := hcsf3
      rcases hcs3 with ⟨hx19_f3, hx20_f3, _, _, _, _, _, hx26_f3, _, _, hfp_f3, hvregs_f3⟩
      rw [hx19_3] at hx19_f3; rw [hx20_3] at hx20_f3
      rw [hx26_3] at hx26_f3; rw [hfp_3] at hfp_f3; rw [hvregs_3] at hvregs_f3
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost3
      rcases hpost3 with ⟨htr_f3, hpost3⟩
      rw [htr_3] at htr_f3
      have hpost3' : sf3.mem ⊨
          (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 56#64) trG tr ∗
           memRegion x.ret 48 ∗
           memRegion sp 56 ∗
           memRegion (sp + 320#64) 40 ∗
           speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
           memRegion (sp + 400#64) 1008 ∗
           protocolAddressAt A x.rem x.remA ∗
           protocolAddressAt A x.loc x.locA ∗
           signalMessageAt A x.msgG x.msgA x.msg ∗
           cliTapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R := by
        rw [stackAt_sub sp tryDecryptSubStack allocHookStack]
        simp only [sepConj_assoc] at hpost3 ⊢
        arm64_sep_close
      simp only [← sepConj_assoc] at hpost3'
      unfold ErrTailStatePlaced
      refine steps_done_of_sepWP_midMeta_placed (s0 := s0)
        (Rest := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64 ∧
          sf.readReg64 .x26 = speTag e ∧
          (sf.mem ⊨
            sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
            trAt A ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
            memRegion x.ret 48 ∗
            memRegion (s0.sp - 1504#64) 0x38 ∗
            memRegion ((s0.sp - 1504#64) + 0x140#64) 0x28 ∗
            speBodyAt A (utf8 "decrypt") ((s0.sp - 1504#64) + 0x168#64) e ∗
            memRegion ((s0.sp - 1504#64) + 0x190#64) 0x3f0 ∗
            cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R))
        hpost3' hLf3 hclf3 ?_
      unfold errTailPC_at tryDecryptMidMetaCore cliTryDecryptCommonHeapPlaced
      rw [lsLogOff_eq_logOff_placed]
      rw [show (0x30c#64 : BitVec 64) = 780#64 by rfl]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]; clear hsp29_eq
      rw [hsp_def]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps
      wp_done

set_option maxHeartbeats 1200000 in
theorem pqRecv_recv_err_true_507_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {sp seedCap seedPtr : BitVec 64} {msgW : BitVec 32}
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hfmt_call : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (sf1 : State)
    (hpcf1 : sf1.pc = (blkPl_508).base + 1488#64)
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
    (hLf1 : ((blkPC_508).rebase (blkPl_508).base H).CodeLoaded sf1.mem)
    (hpost1' : sf1.mem ⊨
      (((sp + 1288#64) ↦₈ 0#8) ∗
       memRegion ((sp + 1288#64) + 1#64) 7 ∗
       ((sp + 1280#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
       memRegion (sp + 1296#64) 32 ∗
       trAt A (sp + 56#64) trG tr ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
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
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       cliTapeAfter ctl x.cur x.rest draws ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps ((blkPC_508).rebase (blkPl_508).base H) sf1 s' ∧
      (ErrTailStatePlaced (blkPl_508).base A ctl x trG tr st1 .invalidState draws R s0 s' ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)) := by
  have hdealloc_tail := pqRecv_dealloc_tail_507_placed C A ctl S H x trG tr st1 mkg draws R s0
    (seedPtr := seedPtr) hsp0_al' hseed1 hseed2 hdealloc_call hsp_def .invalidState
  have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hspf1]; exact hsp_alf1
  rw [lsLogOff_eq_logOff_placed] at hpost1'
  simp only [← sepConj_assoc] at hpost1'
  refine steps_of_sepWP_placed hpost1' hLf1 hclf1
    (mid := lsρ lsFormatInnerSym)
    (RegMid := fun sm2 =>
      sm2.readReg64 .x8 = sp + 408#64 ∧
      sm2.readReg64 .lr = (blkPl_508).base + 2452#64 ∧
      sm2.readReg64 .x19 = x.ret ∧
      sm2.readReg64 .x20 = sp + 320#64 ∧
      (sm2.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm2.readReg64 .x25 = sp + 400#64 ∧
      sm2.readReg64 .fp = sp + 1408#64 ∧
      sm2.sp = sp ∧ sm2.spAligned = true ∧ sm2.trace = s0.trace ∧
      calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (P_mid :=
      memRegion (sp + 408#64) 24 ∗ A.pool ∗ stackAt sp extHookStack ∗
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG tr ∗
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
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
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
    wp_steps
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
        ((formatInnerSpec A).pre (sp + 408#64) sm2 ∗
         (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG tr ∗
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
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          cliTapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptPlacedImg ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - extHookStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ R) := by
      dsimp only [formatInnerSpec]
      rw [hsp_2, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hx8_2, ?_⟩
      simp only [sepConj_assoc] at hmm2 ⊢
      arm64_sep_close
    refine steps_call_placed (sp + 408#64) hfmt_call
      hpcm2 hrunm2 hsp_al2 hlr_2 hclm2 hLm2 hpre_fmt
      (fun sf hpan hpost => ⟨hpan, onPanic_of_formatInner_placed (ctl := ctl) htr_2 hpost⟩) ?_
    intro sf2 hpcf2 hrunf2 hspf2 hsp_alf2 hcsf2 hclf2 hLf2 hpost2
    dsimp only [formatInnerSpec] at hpost2
    rw [hsp_2] at hspf2 hpost2
    have hsp_alf2' : (sf2.sp &&& 15#64 == 0#64) = true := hsp_alf2
    have hcs2 := hcsf2
    rcases hcs2 with ⟨hx19_f2, hx20_f2, _, _, _, hx24_f2, hx25_f2, _, _, _, hfp_f2, hvregs_f2⟩
    rw [hx19_2] at hx19_f2; rw [hx20_2] at hx20_f2
    rw [hx25_2] at hx25_f2; rw [hfp_2] at hfp_f2; rw [hvregs_2] at hvregs_f2
    have hw24_f2 : (sf2.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_f2]; exact hw24_2
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost2
    rcases hpost2 with ⟨htr_f2, hpost2⟩
    rw [htr_2] at htr_f2
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost2
    rcases hpost2 with ⟨fmtBs, hpost2⟩
    unfold vecU8 at hpost2
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost2
    rcases hpost2 with ⟨fmtCap, fmtPtr, hpost2⟩
    have hpost2' : sf2.mem ⊨
        vecU8At A (sp + 408#64) fmtCap fmtPtr fmtBs ∗
        (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         trAt A (sp + 56#64) trG tr ∗
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
         protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         cliTapeAfter ctl x.cur x.rest draws ∗
         logOff tryDecryptPlacedImg ∗
         stackAt sp tryDecryptSubStack ∗
         tryDecryptSavedRegs s0.sp s0 ∗
         A.pool) ∗ R := by
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
    have hpost2_ro := lsro_intro_chk hclf2.2 lsroCheck_tryDecryptHsCoinsRoSym hpost2'
    simp only [← sepConj_assoc] at hpost2_ro
    refine steps_of_sepWP_placed hpost2_ro hLf2 hclf2
      (mid := (blkPl_508).base + 2500#64)
      (RegMid := fun st2 =>
        st2.readReg64 .x19 = x.ret ∧
        st2.readReg64 .x20 = sp + 320#64 ∧
        st2.readReg64 .x26 = speTag .invalidState ∧
        st2.readReg64 .fp = sp + 1408#64 ∧
        st2.sp = sp ∧ st2.spAligned = true ∧ st2.trace = s0.trace ∧
        calleeSavedVRegs st2 = calleeSavedVRegs s0)
      (P_mid :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 56#64) trG tr ∗
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
        speBodyAt A (utf8 "decrypt") (sp + 360#64) .invalidState ∗
        memRegion (sp + 400#64) 1008 ∗
        protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        cliTapeAfter ctl x.cur x.rest draws ∗
        logOff tryDecryptPlacedImg ∗
        stackAt sp tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool) ?_ ?_
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
      wp_steps
      refine SepWP.focus_weaken
        (speBodyAt_invalidState_fold A sp fmtCap fmtPtr _ fmtBs hfb) (by sep_focus) ?_
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
      exact hdealloc_tail st2 hpc2 hrun2 hsp_2 hsp_al2 hfp_2 htr_2 hvregs_2 hcl2 hL2
        hx19_2 hx20_2 hx26_2 hm2

set_option maxHeartbeats 1200000 in
theorem pqRecv_recv_err_false_507_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {sp seedCap seedPtr : BitVec 64} {msgW : BitVec 32} {d : BitVec 8}
    (hmsgW : msgW.setWidth 8 = msgTypeByte x.msgType)
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hfmt_call : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hd_ne : d ≠ 0#8)
    (sf1 : State)
    (hpcf1 : sf1.pc = (blkPl_508).base + 1488#64)
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
    (hLf1 : ((blkPC_508).rebase (blkPl_508).base H).CodeLoaded sf1.mem)
    (hpost1' : sf1.mem ⊨
      (((sp + 1288#64) ↦₈ d) ∗
       memRegion ((sp + 1288#64) + 1#64) 7 ∗
       ((sp + 1280#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
       memRegion (sp + 1296#64) 32 ∗
       trAt A (sp + 56#64) trG tr ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
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
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       cliTapeAfter ctl x.cur x.rest draws ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps ((blkPC_508).rebase (blkPl_508).base H) sf1 s' ∧
      (ErrTailStatePlaced (blkPl_508).base A ctl x trG tr st1 (.invalidMessage x.msgType .pqRatchet) draws R s0 s' ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)) := by
  have hdealloc_tail := pqRecv_dealloc_tail_507_placed C A ctl S H x trG tr st1 mkg draws R s0
    (seedPtr := seedPtr) hsp0_al' hseed1 hseed2 hdealloc_call hsp_def (.invalidMessage x.msgType .pqRatchet)
  have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hspf1]; exact hsp_alf1
  rw [lsLogOff_eq_logOff_placed] at hpost1'
  simp only [← sepConj_assoc] at hpost1'
  refine steps_of_sepWP_placed hpost1' hLf1 hclf1
    (mid := lsρ lsFormatInnerSym)
    (RegMid := fun sm2 =>
      sm2.readReg64 .x8 = sp + 408#64 ∧
      sm2.readReg64 .lr = (blkPl_508).base + 2156#64 ∧
      sm2.readReg64 .x19 = x.ret ∧
      sm2.readReg64 .x20 = sp + 320#64 ∧
      (sm2.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm2.readReg64 .x25 = sp + 400#64 ∧
      sm2.readReg64 .x26 = speTag (.invalidMessage x.msgType .pqRatchet) ∧
      sm2.readReg64 .fp = sp + 1408#64 ∧
      sm2.sp = sp ∧ sm2.spAligned = true ∧ sm2.trace = s0.trace ∧
      calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (P_mid :=
      memRegion (sp + 408#64) 24 ∗ A.pool ∗ stackAt sp extHookStack ∗
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG tr ∗
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
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
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
    wp_steps
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
        ((formatInnerSpec A).pre (sp + 408#64) sm2 ∗
         (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG tr ∗
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
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          cliTapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptPlacedImg ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - extHookStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ R) := by
      dsimp only [formatInnerSpec]
      rw [hsp_2, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hx8_2, ?_⟩
      simp only [sepConj_assoc] at hmm2 ⊢
      arm64_sep_close
    refine steps_call_placed (sp + 408#64) hfmt_call
      hpcm2 hrunm2 hsp_al2 hlr_2 hclm2 hLm2 hpre_fmt
      (fun sf hpan hpost => ⟨hpan, onPanic_of_formatInner_placed (ctl := ctl) htr_2 hpost⟩) ?_
    intro sf2 hpcf2 hrunf2 hspf2 hsp_alf2 hcsf2 hclf2 hLf2 hpost2
    dsimp only [formatInnerSpec] at hpost2
    rw [hsp_2] at hspf2 hpost2
    have hsp_alf2' : (sf2.sp &&& 15#64 == 0#64) = true := hsp_alf2
    have hcs2 := hcsf2
    rcases hcs2 with ⟨hx19_f2, hx20_f2, _, _, _, hx24_f2, hx25_f2, hx26_f2, _, _, hfp_f2, hvregs_f2⟩
    rw [hx19_2] at hx19_f2; rw [hx20_2] at hx20_f2
    rw [hx25_2] at hx25_f2; rw [hx26_2] at hx26_f2; rw [hfp_2] at hfp_f2; rw [hvregs_2] at hvregs_f2
    have hw24_f2 : (sf2.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_f2]; exact hw24_2
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost2
    rcases hpost2 with ⟨htr_f2, hpost2⟩
    rw [htr_2] at htr_f2
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost2
    rcases hpost2 with ⟨fmtBs, hpost2⟩
    unfold vecU8 at hpost2
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost2
    rcases hpost2 with ⟨fmtCap, fmtPtr, hpost2⟩
    have hpost2' : sf2.mem ⊨
        vecU8At A (sp + 408#64) fmtCap fmtPtr fmtBs ∗
        (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         trAt A (sp + 56#64) trG tr ∗
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
         protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         cliTapeAfter ctl x.cur x.rest draws ∗
         logOff tryDecryptPlacedImg ∗
         stackAt sp tryDecryptSubStack ∗
         tryDecryptSavedRegs s0.sp s0 ∗
         A.pool) ∗ R := by
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
    refine steps_of_sepWP_placed hpost2' hLf2 hclf2
      (mid := (blkPl_508).base + 2500#64)
      (RegMid := fun st2 =>
        st2.readReg64 .x19 = x.ret ∧
        st2.readReg64 .x20 = sp + 320#64 ∧
        st2.readReg64 .x26 = speTag (.invalidMessage x.msgType .pqRatchet) ∧
        st2.readReg64 .fp = sp + 1408#64 ∧
        st2.sp = sp ∧ st2.spAligned = true ∧ st2.trace = s0.trace ∧
        calleeSavedVRegs st2 = calleeSavedVRegs s0)
      (P_mid :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 56#64) trG tr ∗
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
        speBodyAt A (utf8 "decrypt") (sp + 360#64) (.invalidMessage x.msgType .pqRatchet) ∗
        memRegion (sp + 400#64) 1008 ∗
        protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        cliTapeAfter ctl x.cur x.rest draws ∗
        logOff tryDecryptPlacedImg ∗
        stackAt sp tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool) ?_ ?_
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
      wp_steps
      rw [show sp + 433#64 = (sp + 432#64) + 1#64 by rw [BitVec.add_assoc]; rfl]
      refine SepWP.focus_weaken
        (pointsTo8_memRegion7_to_64 (sp + 432#64) (msgTypeByte x.msgType)) (by sep_focus) ?_
      wp_pull_exists
      wp_steps
      refine SepWP.focus_weaken
        (pointsTo64_to_8_memRegion7 (sp + 384#64) _ (msgTypeByte x.msgType)) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (speBodyAt_pqRatchet_fold A sp fmtCap fmtPtr _ fmtBs x.msgType hfb) (by sep_focus) ?_
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
      exact hdealloc_tail st2 hpc2 hrun2 hsp_2 hsp_al2 hfp_2 htr_2 hvregs_2 hcl2 hL2
        hx19_2 hx20_2 hx26_2 hm2

end CryptoVerification.CliHandshake.TryDecPlaced
