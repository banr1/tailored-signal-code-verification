/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TryDecryptHsCodeSym
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyHelpersPlaced
public import ProofLib.RegChain
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Segment `S4` (`ConsumeMsgKey`) Post-Call Sub-Lemmas on Block `507`

Relocatable `[LibsignalPlacement]` `Ok`- and `Err`-branch symbolic continuations after
`RatchetState::consume_message_key` in `try_decrypt_with_state::<signal_session_handshake::Coins>`
(Block `507`).
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
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive hiding pointsTo64_split32
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt
open CryptoVerification.Cli.SpqrV1.M4
open CryptoVerification.CliHandshake.TryDecPlaced

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

@[local simp, local wp_norm, local arm64_norm]
private theorem extractLsb32_32_append32 (hi lo : BitVec 32) :
    (hi ++ lo).extractLsb' 32 32 = hi := by bv_kernel

set_option maxHeartbeats 1200000 in
theorem consumeMsgKey_cmk_ok_507_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG' : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (r2 : RatchetState) (mkg : MessageKeyGenerator)
    (draws : Nat) (R : SepProp) (s0 : State)
    {sp dispCap dispPtr : BitVec 64} {dispBs : List (BitVec 8)} {msgW : BitVec 32}
    (hsp0_al : s0.spAligned = true)
    (hsp_al' : (sp &&& 15#64 == 0#64) = true)
    (hdealloc : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hdisp1 : dispBs.length ≤ dispCap.toNat)
    (hdisp2 : dispCap.toNat < 2 ^ 63)
    (hmsgW_byte : msgW.setWidth 8 = msgTypeByte x.msgType)
    (sf2 : State)
    (hpcf2 : sf2.pc = (blkPl_508).base + 1144#64)
    (hrunf2 : sf2.status = .Running)
    (hsp_f2 : sf2.sp = sp)
    (hsp_alf2 : sf2.spAligned = true)
    (hx19_f2 : sf2.readReg64 .x19 = x.ret)
    (hx20_f2 : sf2.readReg64 .x20 = sp + 320#64)
    (hx21_f2 : sf2.readReg64 .x21 = x.ss)
    (hx22_f2 : sf2.readReg64 .x22 = x.msgA)
    (hx23_f2 : sf2.readReg64 .x23 = sp + 1280#64)
    (hx25_f2 : sf2.readReg64 .x25 = sp + 400#64)
    (hx27_f2 : sf2.readReg64 .x27 = dispPtr)
    (hx28_f2 : sf2.readReg64 .x28 = dispCap)
    (hfp_f2 : sf2.readReg64 .fp = sp + 1408#64)
    (htr_f2' : sf2.trace = s0.trace)
    (hvregs_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hclf2 : LibsignalCodeRoLoaded lsmpl sf2.mem)
    (hLf2 : ((blkPC_508).rebase (blkPl_508).base H).CodeLoaded sf2.mem)
    (hm_post2 : sf2.mem ⊨
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
       (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
         (dispPtr ↦ₛ dispBs) ∗
         memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
       consumeMessageKeyResultAt A (sp + 400#64) (.ok mkg) ∗
       memRegion x.ret 48 ∗
       memRegion sp 28 ∗
       ((sp + 28#64) ↦₃₂ msgW) ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 80 ∗
       memRegion (sp + 488#64) 920 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       cliTapeAfter ctl x.cur x.rest draws ∗
       logOff tryDecryptPlacedImg ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps ((blkPC_508).rebase (blkPl_508).base H) sf2 s' ∧
      ((∃ trG'', PqRecvStatePlaced (blkPl_508).base A ctl x trG'' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  dsimp only [consumeMessageKeyResultAt, vecU8, vecU8At, vecHeader] at hm_post2
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_post2
  rcases hm_post2 with ⟨seedCap, seedPtr, hm_post2⟩
  simp only [sepConj_pure_left_comm, satisfies_pure_sepConj] at hm_post2
  rcases hm_post2 with ⟨⟨hseed1, hseed2, hseed3⟩, hm_post2⟩
  simp only [← sepConj_assoc] at hm_post2
  refine steps_of_sepWP_placed hm_post2 hLf2 hclf2
    (mid := (blkPl_508).base + 1396#64)
    (RegMid := fun sm3 =>
      (sm3.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm3.readReg64 .x19 = x.ret ∧
      sm3.readReg64 .x20 = sp + 320#64 ∧
      sm3.readReg64 .x21 = x.ss ∧
      sm3.readReg64 .x22 = x.msgA ∧
      sm3.readReg64 .x23 = sp + 1280#64 ∧
      sm3.readReg64 .x25 = sp + 400#64 ∧
      sm3.readReg64 .x27 = dispPtr ∧
      sm3.readReg64 .x28 = dispCap ∧
      sm3.readReg64 .fp = sp + 1408#64 ∧
      sm3.sp = sp ∧ sm3.spAligned = true ∧ sm3.trace = s0.trace ∧
      calleeSavedVRegs sm3 = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
      (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
        (dispPtr ↦ₛ dispBs) ∗
        memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
          (seedCap.toNat - mkg.seed.length)) ∗
      ((sp + 400#64) ↦₃₂ 1#32) ∗
      memRegion (sp + 404#64) 4 ∗
      ((sp + 408#64) ↦₆₄ seedCap) ∗
      ((sp + 416#64) ↦₆₄ seedPtr) ∗
      ((sp + 424#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 432#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 436#64) 52 ∗
      memRegion x.ret 48 ∗
      memRegion sp 28 ∗
      ((sp + 28#64) ↦₃₂ msgW) ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
      memRegion (sp + 44#64) 4 ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 80 ∗
      memRegion (sp + 488#64) 920 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      cliTapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool) ?_ ?_
  · wp_conv_pre => simp only [sepConj_assoc]
    wp_steps
    wp_done
  · intro sm3 hpc3 hrun3 hcl3 hL3
      ⟨hx24_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx25_3, hx27_3, hx28_3,
       hfp3, hsp3, hsp_al3, htr3, hvregs3⟩
      hm3
    refine steps_of_sepWP_placed hm3 hL3 hcl3
      (mid := (blkPl_508).base + 1444#64)
      (RegMid := fun sm4 =>
        (sm4.readReg64 .x24).setWidth 32 = 1#32 ∧
        sm4.readReg64 .x19 = x.ret ∧
        sm4.readReg64 .x20 = sp + 320#64 ∧
        sm4.readReg64 .x21 = x.ss ∧
        sm4.readReg64 .x22 = x.msgA ∧
        sm4.readReg64 .x23 = sp + 1280#64 ∧
        sm4.readReg64 .x25 = sp + 400#64 ∧
        sm4.readReg64 .x27 = dispPtr ∧
        sm4.readReg64 .x28 = dispCap ∧
        sm4.readReg64 .fp = sp + 1408#64 ∧
        sm4.sp = sp ∧ sm4.spAligned = true ∧ sm4.trace = s0.trace ∧
        calleeSavedVRegs sm4 = calleeSavedVRegs s0)
      (P_mid :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
        (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
          (dispPtr ↦ₛ dispBs) ∗
          memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
        (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
          (seedPtr ↦ₛ mkg.seed) ∗
          memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
            (seedCap.toNat - mkg.seed.length)) ∗
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
        memRegion (sp + 1116#64) 292 ∗
        protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        cliTapeAfter ctl x.cur x.rest draws ∗
        logOff tryDecryptPlacedImg ∗
        stackAt sp tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool) ?_ ?_
    · have hsp0 : memRegion sp 28 =
          memRegion sp 16 ∗ (memRegion (sp + 16#64) 8 ∗ memRegion (sp + 24#64) 4) := by
        have h1 := mr_cut_add sp 0 16 12 (by decide)
        simp only [BitVec.add_zero] at h1
        rw [h1, mr_cut_add sp 16 8 4 (by decide)]
      wp_conv_pre =>
        rw [mr_cut sp 436 4 48 52 440#64,
          memRegion_four (sp + 404#64),
          memRegion_four (sp + 436#64),
          memRegion_four (sp + 44#64)]
        simp only [sepConj_assoc]
      wp_pull_exists
      rename_i pad44 pad436 pad404
      have hmerge432 :
          ((sp + 432#64) ↦₃₂ mkg.counter) ∗ ((sp + 436#64) ↦₃₂ pad436) ⊢
          ((sp + 432#64) ↦₆₄ (pad436 ++ mkg.counter)) := by
        have hm := pointsTo32_merge64 (sp + 432#64) mkg.counter pad436
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
        rw [hm]; exact Entails.refl _
      have hmerge40 :
          ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ ((sp + 44#64) ↦₃₂ pad44) ⊢
          ((sp + 40#64) ↦₆₄ (pad44 ++ x.msg.counter)) := by
        have hm := pointsTo32_merge64 (sp + 40#64) x.msg.counter pad44
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
        rw [hm]; exact Entails.refl _
      refine SepWP.focus_weaken hmerge432 (by sep_focus) ?_
      refine SepWP.focus_weaken hmerge40 (by sep_focus) ?_
      wp_conv_pre =>
        rw [hsp0,
          mr_cut sp 440 8 40 48 448#64,
          mr_cut sp 448 8 32 40 456#64,
          mr_cut sp 456 8 24 32 464#64,
          mr_cut sp 464 8 16 24 472#64,
          mr_cut sp 472 8 8 16 480#64,
          mr_cut sp 488 616 304 920 1104#64,
          mr_cut sp 1104 8 296 304 1112#64,
          mr_cut sp 1112 8 288 296 1120#64,
          mr_cut sp 1120 8 280 288 1128#64,
          mr_cut sp 1128 8 272 280 1136#64,
          mr_cut sp 1136 8 264 272 1144#64,
          mr_cut sp 1144 8 256 264 1152#64,
          mr_cut sp 1152 8 248 256 1160#64,
          mr_cut sp 1160 8 240 248 1168#64,
          mr_cut sp 1168 112 128 240 1280#64,
          mr_cut sp 1280 8 120 128 1288#64,
          mr_cut sp 1288 8 112 120 1296#64,
          mr_cut sp 1296 8 104 112 1304#64,
          mr_cut sp 1304 8 96 104 1312#64]
        simp only [sepConj_assoc,
          memRegion_eight (sp + 16#64),
          memRegion_eight (sp + 440#64),
          memRegion_eight (sp + 448#64),
          memRegion_eight (sp + 456#64),
          memRegion_eight (sp + 464#64),
          memRegion_eight (sp + 472#64),
          memRegion_eight (sp + 480#64),
          memRegion_eight (sp + 1104#64),
          memRegion_eight (sp + 1112#64),
          memRegion_eight (sp + 1120#64),
          memRegion_eight (sp + 1128#64),
          memRegion_eight (sp + 1136#64),
          memRegion_eight (sp + 1144#64),
          memRegion_eight (sp + 1152#64),
          memRegion_eight (sp + 1160#64),
          memRegion_eight (sp + 1280#64),
          memRegion_eight (sp + 1288#64),
          memRegion_eight (sp + 1296#64),
          memRegion_eight (sp + 1304#64)]
      wp_pull_exists
      wp_steps
      have hsplit1112 :
          ((sp + 1112#64) ↦₆₄ (pad436 ++ mkg.counter)) ⊢
          ((sp + 1112#64) ↦₃₂ mkg.counter) ∗ memRegion (sp + 1116#64) 4 := by
        have hs := (pointsTo32_merge64 (sp + 1112#64) mkg.counter pad436).symm
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
        rw [hs]
        exact sepConj_mono_right (pointsTo32_entails_memRegion (sp + 1116#64) pad436)
      refine SepWP.focus_weaken hsplit1112 (by sep_focus) ?_
      refine SepWP.focus_weaken (pointsTo32_entails_memRegion (sp + 400#64) 1#32) (by sep_focus) ?_
      refine SepWP.focus_weaken (pointsTo32_entails_memRegion (sp + 404#64) pad404) (by sep_focus) ?_
      have hm320 : memRegion (sp + 320#64) 784 =
          memRegion (sp + 320#64) 80 ∗ (memRegion (sp + 400#64) 4 ∗ (memRegion (sp + 404#64) 4 ∗
          (memRegion (sp + 408#64) 8 ∗ (memRegion (sp + 416#64) 8 ∗ (memRegion (sp + 424#64) 8 ∗
          (memRegion (sp + 432#64) 8 ∗ (memRegion (sp + 440#64) 8 ∗ (memRegion (sp + 448#64) 8 ∗
          (memRegion (sp + 456#64) 8 ∗ (memRegion (sp + 464#64) 8 ∗ (memRegion (sp + 472#64) 8 ∗
          (memRegion (sp + 480#64) 8 ∗ memRegion (sp + 488#64) 616)))))))))))) := by
        rw [mr_cut_add sp 320 80 704 (by decide),
          mr_cut_add sp 400 4 700 (by decide),
          mr_cut_add sp 404 4 696 (by decide),
          mr_cut_add sp 408 8 688 (by decide),
          mr_cut_add sp 416 8 680 (by decide),
          mr_cut_add sp 424 8 672 (by decide),
          mr_cut_add sp 432 8 664 (by decide),
          mr_cut_add sp 440 8 656 (by decide),
          mr_cut_add sp 448 8 648 (by decide),
          mr_cut_add sp 456 8 640 (by decide),
          mr_cut_add sp 464 8 632 (by decide),
          mr_cut_add sp 472 8 624 (by decide),
          mr_cut_add sp 480 8 616 (by decide)]
      have hm1116 : memRegion (sp + 1116#64) 292 =
          memRegion (sp + 1116#64) 4 ∗ (memRegion (sp + 1120#64) 8 ∗
          (memRegion (sp + 1128#64) 8 ∗ (memRegion (sp + 1136#64) 8 ∗
          (memRegion (sp + 1144#64) 8 ∗ (memRegion (sp + 1152#64) 8 ∗
          (memRegion (sp + 1160#64) 8 ∗ (memRegion (sp + 1168#64) 112 ∗
          (memRegion (sp + 1280#64) 8 ∗ (memRegion (sp + 1288#64) 8 ∗
          (memRegion (sp + 1296#64) 8 ∗ (memRegion (sp + 1304#64) 8 ∗
           memRegion (sp + 1312#64) 96))))))))))) := by
        rw [mr_cut_add sp 1116 4 288 (by decide),
          mr_cut_add sp 1120 8 280 (by decide),
          mr_cut_add sp 1128 8 272 (by decide),
          mr_cut_add sp 1136 8 264 (by decide),
          mr_cut_add sp 1144 8 256 (by decide),
          mr_cut_add sp 1152 8 248 (by decide),
          mr_cut_add sp 1160 8 240 (by decide),
          mr_cut_add sp 1168 112 128 (by decide),
          mr_cut_add sp 1280 8 120 (by decide),
          mr_cut_add sp 1288 8 112 (by decide),
          mr_cut_add sp 1296 8 104 (by decide),
          mr_cut_add sp 1304 8 96 (by decide)]
      rw [hm320, hm1116]
      wp_done
    · intro sm4 hpc4 hrun4 hcl4 hL4
        ⟨hx24_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx25_4, hx27_4, hx28_4,
         hfp4, hsp4, hsp_al4, htr4, hvregs4⟩
        hm4
      by_cases hcap : dispCap = 0
      · simp only [hcap, ↓reduceIte, emp_sepConj] at hm4
        subst hcap
        refine steps_of_sepWP_placed hm4 hL4 hcl4
          (mid := (blkPl_508).base + 1464#64)
          (RegMid := fun sf =>
            (sf.readReg64 .x24).setWidth 32 = 1#32 ∧
            sf.readReg64 .x19 = x.ret ∧
            sf.readReg64 .x20 = sp + 320#64 ∧
            sf.readReg64 .x21 = x.ss ∧
            sf.readReg64 .x22 = x.msgA ∧
            sf.readReg64 .x23 = sp + 1280#64 ∧
            sf.readReg64 .x25 = sp + 400#64 ∧
            sf.readReg64 .fp = sp + 1408#64 ∧
            sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
            calleeSavedVRegs sf = calleeSavedVRegs s0)
          (P_mid :=
            sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
            trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
            (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
              (seedPtr ↦ₛ mkg.seed) ∗
              memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                (seedCap.toNat - mkg.seed.length)) ∗
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
            memRegion (sp + 1116#64) 292 ∗
            protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            cliTapeAfter ctl x.cur x.rest draws ∗
            logOff tryDecryptPlacedImg ∗
            stackAt sp tryDecryptSubStack ∗
            tryDecryptSavedRegs s0.sp s0 ∗
            A.pool) ?_ ?_
        · wp_steps
          wp_done
        · intro sf hpcf hrunf hclf _
            ⟨hx24_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx25_f, hfp_f, hsp_f, hsp_alf, htr_f, hvregs_f⟩
            hmf
          subst hsp_def
          refine ⟨sf, .refl _, Or.inl ⟨trG', ?_⟩⟩
          have hpc_s5 : sf.pc = segPqRecvPC_at (blkPl_508).base := by
            rw [hpcf]
          have hfp_f' : sf.readReg64 .x29 = s0.sp - 96#64 := by
            change sf.readReg64 .fp = s0.sp - 96#64
            rw [hfp_f]; exact (sp_fp_eq rfl).symm
          refine ⟨hpc_s5, ⟨hrunf, hsp_f, hsp0_al, hsp_alf, hfp_f', htr_f, hclf, hvregs_f⟩,
            hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f,
            seedCap, seedPtr, msgW, hmsgW_byte, hseed1, hseed2, hseed3, ?_⟩
          dsimp only [cliTryDecryptCommonHeapPlaced]
          rw [lsLogOff_eq_logOff_placed]
          simp only [sepConj_assoc] at hmf ⊢
          arm64_sep_close
      · simp only [hcap, ↓reduceIte] at hm4
        have hcap_beq : (dispCap == 0#64) = false := beq_false_of_ne hcap
        refine steps_of_sepWP_placed hm4 hL4 hcl4
          (mid := lsρ lsRustDeallocSym)
          (RegMid := fun sm5 =>
            sm5.readReg64 .x0 = dispPtr ∧
            sm5.readReg64 .x1 = dispCap ∧
            sm5.readReg64 .x2 = 1#64 ∧
            (sm5.readReg64 .x24).setWidth 32 = 1#32 ∧
            sm5.readReg64 .x19 = x.ret ∧
            sm5.readReg64 .x20 = sp + 320#64 ∧
            sm5.readReg64 .x21 = x.ss ∧
            sm5.readReg64 .x22 = x.msgA ∧
            sm5.readReg64 .x23 = sp + 1280#64 ∧
            sm5.readReg64 .x25 = sp + 400#64 ∧
            sm5.readReg64 .fp = sp + 1408#64 ∧
            sm5.readReg64 .lr = (blkPl_508).base + 1464#64 ∧
            sm5.sp = sp ∧ sm5.spAligned = true ∧ sm5.trace = s0.trace ∧
            calleeSavedVRegs sm5 = calleeSavedVRegs s0)
          (P_mid :=
            sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
            trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
            A.live dispPtr dispCap.toNat 1 ∗
            memRegion dispPtr dispCap.toNat ∗
            (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
              (seedPtr ↦ₛ mkg.seed) ∗
              memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                (seedCap.toNat - mkg.seed.length)) ∗
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
            memRegion (sp + 1116#64) 292 ∗
            protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            cliTapeAfter ctl x.cur x.rest draws ∗
            logOff tryDecryptPlacedImg ∗
            stackAt sp tryDecryptSubStack ∗
            tryDecryptSavedRegs s0.sp s0 ∗
            A.pool) ?_ ?_
        · wp_conv_pre => simp only [sepConj_assoc]
          wp_steps
          refine SepWP.focus_weaken (buf_to_mr dispPtr dispBs dispCap.toNat hdisp1 hdisp2)
            (by sep_focus) ?_
          wp_done
        · intro sm5 hpc5 hrun5 hcl5 hL5
            ⟨hx0_5, hx1_5, hx2_5, hx24_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5,
             hx25_5, hfp5, hlr5, hsp5, hsp_al5, htr5, hvregs5⟩
            hm5
          have hstack_dealloc := stackAt_sub sp tryDecryptSubStack allocHookStack (by decide) (by decide)
          have hpre_dealloc : sm5.mem ⊨
              (rustDeallocSpec A).pre (dispPtr, dispCap.toNat, 1) sm5 ∗
              ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
                trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
                (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
                  (seedPtr ↦ₛ mkg.seed) ∗
                  memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                    (seedCap.toNat - mkg.seed.length)) ∗
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
                memRegion (sp + 1116#64) 292 ∗
                protocolAddressAt A x.rem x.remA ∗
                protocolAddressAt A x.loc x.locA ∗
                signalMessageAt A x.msgG x.msgA x.msg ∗
                cliTapeAfter ctl x.cur x.rest draws ∗
                logOff tryDecryptPlacedImg ∗
                memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
                  (tryDecryptSubStack - allocHookStack) ∗
                tryDecryptSavedRegs s0.sp s0) ∗ R) := by
            dsimp only [rustDeallocSpec]
            rw [hsp5, sepConj_assoc, satisfies_pure_sepConj]
            refine ⟨⟨hx0_5, by rw [hx1_5], by rw [hx2_5]; rfl⟩, ?_⟩
            rw [hstack_dealloc] at hm5
            simp only [sepConj_assoc] at hm5 ⊢
            arm64_sep_close
          refine steps_call_out_placed (dispPtr, dispCap.toNat, 1) hdealloc
            hpc5 hrun5 hsp_al5 hlr5 hcl5 hL5 hpre_dealloc ?_ ?_
          · intro sf _ hpost
            dsimp only [rustDeallocSpec] at hpost
            rw [sepConj_assoc] at hpost
            exact (not_satisfies_false_sepConj hpost).elim
          · intro sf hpcf hrunf hspf hsp_alf hcsf hclf _ hpost
            have hx24_f : (sf.readReg64 .x24).setWidth 32 = 1#32 := by
              rw [show sf.readReg64 .x24 = sm5.readReg64 .x24 by reg_chain]; exact hx24_5
            have hfp_f_sp : sf.readReg64 .fp = sp + 1408#64 := by reg_chain
            dsimp only [rustDeallocSpec] at hpost
            rw [hsp5, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
            rcases hpost with ⟨htr_f, hpost⟩
            subst hsp_def
            refine ⟨sf, .refl _, Or.inl ⟨trG', ?_⟩⟩
            have hpc_s5 : sf.pc = segPqRecvPC_at (blkPl_508).base := by
              rw [hpcf]
            have hfp_f : sf.readReg64 .x29 = s0.sp - 96#64 := by
              change sf.readReg64 .fp = s0.sp - 96#64
              rw [hfp_f_sp]; exact (sp_fp_eq rfl).symm
            refine ⟨hpc_s5, ⟨hrunf, by reg_chain, hsp0_al, hsp_alf, hfp_f, by reg_chain, hclf, by reg_chain⟩,
              by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, hx24_f,
              by reg_chain, seedCap, seedPtr, msgW, hmsgW_byte, hseed1, hseed2, hseed3, ?_⟩
            dsimp only [cliTryDecryptCommonHeapPlaced]
            rw [lsLogOff_eq_logOff_placed]
            rw [hstack_dealloc]
            simp only [sepConj_assoc] at hpost ⊢
            arm64_sep_close

set_option maxHeartbeats 1200000 in
theorem consumeMsgKey_cmk_err_507_placed [LibsignalPlacement] (_C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (_parse : UuidParser) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG' : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (r2 : RatchetState) (e : SignalProtocolError)
    (draws : Nat) (R : SepProp) (s0 : State)
    {sp dispCap dispPtr : BitVec 64} {dispBs : List (BitVec 8)} {msgW : BitVec 32}
    (hne_panic : e ≠ .panic)
    (hsp0_al : s0.spAligned = true)
    (hsp_al' : (sp &&& 15#64 == 0#64) = true)
    (hdealloc : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hdisp1 : dispBs.length ≤ dispCap.toNat)
    (hdisp2 : dispCap.toNat < 2 ^ 63)
    (sf2 : State)
    (hpcf2 : sf2.pc = (blkPl_508).base + 1144#64)
    (hrunf2 : sf2.status = .Running)
    (hsp_f2 : sf2.sp = sp)
    (hsp_alf2 : sf2.spAligned = true)
    (hx19_f2 : sf2.readReg64 .x19 = x.ret)
    (hx20_f2 : sf2.readReg64 .x20 = sp + 320#64)
    (_hx23_f2 : sf2.readReg64 .x23 = sp + 1280#64)
    (hx25_f2 : sf2.readReg64 .x25 = sp + 400#64)
    (hx27_f2 : sf2.readReg64 .x27 = dispPtr)
    (hx28_f2 : sf2.readReg64 .x28 = dispCap)
    (hfp_f2 : sf2.readReg64 .fp = sp + 1408#64)
    (htr_f2' : sf2.trace = s0.trace)
    (hvregs_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hclf2 : LibsignalCodeRoLoaded lsmpl sf2.mem)
    (hLf2 : ((blkPC_508).rebase (blkPl_508).base H).CodeLoaded sf2.mem)
    (hm_post2 : sf2.mem ⊨
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
       (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
         (dispPtr ↦ₛ dispBs) ∗
         memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
       consumeMessageKeyResultAt A (sp + 400#64) (.error e) ∗
       memRegion x.ret 48 ∗
       memRegion sp 28 ∗
       ((sp + 28#64) ↦₃₂ msgW) ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 80 ∗
       memRegion (sp + 488#64) 920 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       cliTapeAfter ctl x.cur x.rest draws ∗
       logOff tryDecryptPlacedImg ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps ((blkPC_508).rebase (blkPl_508).base H) sf2 s' ∧
      ((e ≠ .panic ∧ ∃ trG'',
          ErrTailStatePlaced (blkPl_508).base A ctl x trG'' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
       (s'.status = .Panicked ∧
         ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
         (s'.mem ⊨ anyHeap ∗ R))) := by
  have hm_err : sf2.mem ⊨
      (∃∗ w416 : BitVec 64, ∃∗ w424 : BitVec 64, ∃∗ w432 : BitVec 64,
       ∃∗ w440 : BitVec 64, ∃∗ w448 : BitVec 64, ∃∗ restHeap : SepProp,
        ⌜ErrWordsRel A e w416 w424 w432 w440 restHeap ∧ speTag e + 2#64 ≠ 0#64⌝ ∗
        ((sp + 400#64) ↦₃₂ 2#32) ∗
        memRegion (sp + 404#64) 4 ∗
        ((sp + 408#64) ↦₆₄ speTag e) ∗
        ((sp + 416#64) ↦₆₄ w416) ∗
        ((sp + 424#64) ↦₆₄ w424) ∗
        ((sp + 432#64) ↦₆₄ w432) ∗
        ((sp + 440#64) ↦₆₄ w440) ∗
        ((sp + 448#64) ↦₆₄ w448) ∗
        memRegion (sp + 456#64) 32 ∗
        restHeap) ∗
      ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
        (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
          (dispPtr ↦ₛ dispBs) ∗
          memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
        memRegion x.ret 48 ∗
        memRegion sp 56 ∗
        memRegion (sp + 320#64) 80 ∗
        memRegion (sp + 488#64) 920 ∗
        protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        cliTapeAfter ctl x.cur x.rest draws ∗
        logOff tryDecryptPlacedImg ∗
        stackAt sp tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool) ∗ R) := by
    have hsp56 : memRegion sp 56 =
        memRegion sp 28 ∗ (memRegion (sp + 28#64) 4 ∗ (memRegion (sp + 32#64) 8 ∗
        (memRegion (sp + 40#64) 4 ∗ (memRegion (sp + 44#64) 4 ∗ memRegion (sp + 48#64) 8)))) := by
      have h1 := mr_cut_add sp 0 28 28 (by decide)
      simp only [BitVec.add_zero] at h1
      rw [h1,
        mr_cut_add sp 28 4 24 (by decide),
        mr_cut_add sp 32 8 16 (by decide),
        mr_cut_add sp 40 4 12 (by decide),
        mr_cut_add sp 44 4 8 (by decide)]
    rw [hsp56]
    refine Satisfies.mono (sepConj_mono_left (resultAt_err_unpack A sp e)) ?_
    have hm_post2' : sf2.mem ⊨
        (((sp + 28#64) ↦₃₂ msgW) ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
         ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ ((sp + 48#64) ↦₆₄ x.remA)) ∗
        (consumeMessageKeyResultAt A (sp + 400#64) (.error e) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
         (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
           (dispPtr ↦ₛ dispBs) ∗
           memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
         memRegion x.ret 48 ∗
         memRegion sp 28 ∗
         memRegion (sp + 44#64) 4 ∗
         memRegion (sp + 320#64) 80 ∗
         memRegion (sp + 488#64) 920 ∗
         protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         cliTapeAfter ctl x.cur x.rest draws ∗
         logOff tryDecryptPlacedImg ∗
         stackAt sp tryDecryptSubStack ∗
         tryDecryptSavedRegs s0.sp s0 ∗
         A.pool ∗ R) := by
      simp only [sepConj_assoc] at hm_post2 ⊢
      arm64_sep_close
    have hm_post2'' := Satisfies.mono (sepConj_mono_left (sepConj_mono
      (pointsTo32_entails_memRegion (sp + 28#64) msgW)
      (sepConj_mono (pts64_to_mr (sp + 32#64) x.locA)
        (sepConj_mono (pointsTo32_entails_memRegion (sp + 40#64) x.msg.counter)
          (pts64_to_mr (sp + 48#64) x.remA))))) hm_post2'
    change sf2.mem ⊨ _ at hm_post2'' ⊢
    simp only [sepConj_assoc] at hm_post2'' ⊢
    arm64_sep_close
  simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hm_err
  rcases hm_err with ⟨w416, w424, w432, w440, w448, restHeap, hm_err⟩
  rw [satisfies_pure_sepConj] at hm_err
  rcases hm_err with ⟨⟨hrel, htag_ne⟩, hm_err⟩
  simp only [← sepConj_assoc] at hm_err
  refine steps_of_sepWP_placed hm_err hLf2 hclf2
    (mid := (blkPl_508).base + 1180#64)
    (RegMid := fun sm3 =>
      sm3.readReg64 .x19 = x.ret ∧
      sm3.readReg64 .x20 = sp + 320#64 ∧
      sm3.readReg64 .x26 = speTag e ∧
      sm3.readReg64 .x27 = dispPtr ∧
      sm3.readReg64 .x28 = dispCap ∧
      sm3.readReg64 .fp = sp + 1408#64 ∧
      sm3.sp = sp ∧ sm3.spAligned = true ∧ sm3.trace = s0.trace ∧
      calleeSavedVRegs sm3 = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
      (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
        (dispPtr ↦ₛ dispBs) ∗
        memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
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
      A.pool) ?_ ?_
  · wp_conv_pre =>
      rw [mr_cut sp 320 40 40 80 360#64,
        mr_cut sp 360 8 32 40 368#64,
        mr_cut sp 368 8 24 32 376#64,
        mr_cut sp 376 8 16 24 384#64,
        mr_cut sp 384 8 8 16 392#64,
        mr_cut sp 488 792 128 920 1280#64,
        mr_cut sp 1280 8 120 128 1288#64,
        mr_cut sp 1288 8 112 120 1296#64,
        mr_cut sp 1296 8 104 112 1304#64,
        mr_cut sp 1304 8 96 104 1312#64]
      simp only [sepConj_assoc,
        memRegion_eight (sp + 360#64),
        memRegion_eight (sp + 368#64),
        memRegion_eight (sp + 376#64),
        memRegion_eight (sp + 384#64),
        memRegion_eight (sp + 392#64),
        memRegion_eight (sp + 1280#64),
        memRegion_eight (sp + 1288#64),
        memRegion_eight (sp + 1296#64),
        memRegion_eight (sp + 1304#64)]
    wp_pull_exists
    have htag_beq : (speTag e + 2#64 == 0#64) = false := beq_false_of_ne htag_ne
    have htag_beq0 : (speTag e + 2#64 + 0#64 == 0#64) = false := by
      rw [BitVec.add_zero]; exact htag_beq
    wp_steps
    refine SepWP.focus_weaken
      (speBodyAt_err_pack A sp e w416 w424 w432 w440 w448 restHeap hrel)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (pointsTo32_entails_memRegion (sp + 400#64) 2#32) (by sep_focus) ?_
    have hm400 : memRegion (sp + 400#64) 1008 =
        memRegion (sp + 400#64) 4 ∗ (memRegion (sp + 404#64) 4 ∗ (memRegion (sp + 408#64) 8 ∗
        (memRegion (sp + 416#64) 8 ∗ (memRegion (sp + 424#64) 8 ∗ (memRegion (sp + 432#64) 8 ∗
        (memRegion (sp + 440#64) 8 ∗ (memRegion (sp + 448#64) 8 ∗ (memRegion (sp + 456#64) 32 ∗
        (memRegion (sp + 488#64) 792 ∗ (memRegion (sp + 1280#64) 8 ∗
        (memRegion (sp + 1288#64) 8 ∗ (memRegion (sp + 1296#64) 8 ∗
        (memRegion (sp + 1304#64) 8 ∗ memRegion (sp + 1312#64) 96))))))))))))) := by
      rw [mr_cut_add sp 400 4 1004 (by decide),
        mr_cut_add sp 404 4 1000 (by decide),
        mr_cut_add sp 408 8 992 (by decide),
        mr_cut_add sp 416 8 984 (by decide),
        mr_cut_add sp 424 8 976 (by decide),
        mr_cut_add sp 432 8 968 (by decide),
        mr_cut_add sp 440 8 960 (by decide),
        mr_cut_add sp 448 8 952 (by decide),
        mr_cut_add sp 456 32 920 (by decide),
        mr_cut_add sp 488 792 128 (by decide),
        mr_cut_add sp 1280 8 120 (by decide),
        mr_cut_add sp 1288 8 112 (by decide),
        mr_cut_add sp 1296 8 104 (by decide),
        mr_cut_add sp 1304 8 96 (by decide)]
    rw [hm400]
    wp_done
  · intro sm3 hpc3 hrun3 hcl3 hL3
      ⟨hx19_3, hx20_3, hx26_3, hx27_3, hx28_3, hfp3, hsp3, hsp_al3, htr3, hvregs3⟩
      hm3
    have herr_tail : ∀ st4 : State,
        st4.pc = (blkPl_508).base + 1200#64 → st4.status = .Running →
        st4.sp = sp → st4.spAligned = true →
        st4.readReg64 .fp = sp + 1408#64 → st4.trace = s0.trace →
        calleeSavedVRegs st4 = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl st4.mem →
        ((blkPC_508).rebase (blkPl_508).base H).CodeLoaded st4.mem →
        st4.readReg64 .x19 = x.ret →
        st4.readReg64 .x20 = sp + 320#64 →
        st4.readReg64 .x26 = speTag e →
        (st4.mem ⊨
          (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
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
           A.pool) ∗ R) →
        ∃ s', Steps ((blkPC_508).rebase (blkPl_508).base H) st4 s' ∧
          ((e ≠ .panic ∧ ∃ trG'',
              ErrTailStatePlaced (blkPl_508).base A ctl x trG'' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R))) := by
      intro st4 hpc4 hrun4 hsp4 hsp_al4 hfp4 htr4 hvregs4 hcl4 hL4 hx19_4 hx20_4 hx26_4 hm4
      refine steps_of_sepWP_placed hm4 hL4 hcl4
        (mid := (blkPl_508).base + 780#64)
        (RegMid := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = sp + 320#64 ∧
          sf.readReg64 .x26 = speTag e ∧
          sf.readReg64 .fp = sp + 1408#64 ∧
          sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
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
          A.pool) ?_ ?_
      · wp_steps
        wp_done
      · intro sf hpcf hrunf hclf _ ⟨hx19_f, hx20_f, hx26_f, hfp_f, hsp_f, hsp_alf, htr_f, hvregs_f⟩ hmf
        subst hsp_def
        refine ⟨sf, .refl _, Or.inl ⟨hne_panic, trG', ?_⟩⟩
        have hpc_err : sf.pc = errTailPC_at (blkPl_508).base := by
          rw [hpcf]
        have hfp_f' : sf.readReg64 .x29 = s0.sp - 96#64 := by
          change sf.readReg64 .fp = s0.sp - 96#64
          rw [hfp_f]; exact (sp_fp_eq rfl).symm
        refine ⟨hpc_err, ⟨hrunf, hsp_f, hsp0_al, hsp_alf, hfp_f', htr_f, hclf, hvregs_f⟩,
          hx19_f, hx20_f, hx26_f, ?_⟩
        dsimp only [cliTryDecryptCommonHeapPlaced]
        rw [lsLogOff_eq_logOff_placed]
        simp only [sepConj_assoc] at hmf ⊢
        arm64_sep_close
    by_cases hcap : dispCap = 0
    · simp only [hcap, ↓reduceIte, emp_sepConj] at hm3
      subst hcap
      refine steps_of_sepWP_placed hm3 hL3 hcl3
        (mid := (blkPl_508).base + 1200#64)
        (RegMid := fun st4 =>
          st4.readReg64 .x19 = x.ret ∧
          st4.readReg64 .x20 = sp + 320#64 ∧
          st4.readReg64 .x26 = speTag e ∧
          st4.readReg64 .fp = sp + 1408#64 ∧
          st4.sp = sp ∧ st4.spAligned = true ∧ st4.trace = s0.trace ∧
          calleeSavedVRegs st4 = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
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
          A.pool) ?_ ?_
      · wp_steps
        wp_done
      · intro st4 hpc4 hrun4 hcl4 hL4 ⟨hx19_4, hx20_4, hx26_4, hfp4, hsp4, hsp_al4, htr4, hvregs4⟩ hm4
        exact herr_tail st4 hpc4 hrun4 hsp4 hsp_al4 hfp4 htr4 hvregs4 hcl4 hL4 hx19_4 hx20_4 hx26_4 hm4
    · simp only [hcap, ↓reduceIte] at hm3
      have hcap_beq : (dispCap == 0#64) = false := beq_false_of_ne hcap
      refine steps_of_sepWP_placed hm3 hL3 hcl3
        (mid := lsρ lsRustDeallocSym)
        (RegMid := fun sm4 =>
          sm4.readReg64 .x0 = dispPtr ∧
          sm4.readReg64 .x1 = dispCap ∧
          sm4.readReg64 .x2 = 1#64 ∧
          sm4.readReg64 .x19 = x.ret ∧
          sm4.readReg64 .x20 = sp + 320#64 ∧
          sm4.readReg64 .x26 = speTag e ∧
          sm4.readReg64 .fp = sp + 1408#64 ∧
          sm4.readReg64 .lr = (blkPl_508).base + 1200#64 ∧
          sm4.sp = sp ∧ sm4.spAligned = true ∧ sm4.trace = s0.trace ∧
          calleeSavedVRegs sm4 = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
          A.live dispPtr dispCap.toNat 1 ∗
          memRegion dispPtr dispCap.toNat ∗
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
          A.pool) ?_ ?_
      · wp_conv_pre => simp only [sepConj_assoc]
        wp_steps
        refine SepWP.focus_weaken (buf_to_mr dispPtr dispBs dispCap.toNat hdisp1 hdisp2)
          (by sep_focus) ?_
        wp_done
      · intro sm4 hpc4 hrun4 hcl4 hL4
          ⟨hx0_4, hx1_4, hx2_4, hx19_4, hx20_4, hx26_4, hfp4, hlr4, hsp4, hsp_al4, htr4, hvregs4⟩
          hm4
        have hstack_dealloc := stackAt_sub sp tryDecryptSubStack allocHookStack (by decide) (by decide)
        have hpre_dealloc : sm4.mem ⊨
            (rustDeallocSpec A).pre (dispPtr, dispCap.toNat, 1) sm4 ∗
            ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
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
              memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
                (tryDecryptSubStack - allocHookStack) ∗
              tryDecryptSavedRegs s0.sp s0) ∗ R) := by
          dsimp only [rustDeallocSpec]
          rw [hsp4, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0_4, by rw [hx1_4], by rw [hx2_4]; rfl⟩, ?_⟩
          rw [hstack_dealloc] at hm4
          simp only [sepConj_assoc] at hm4 ⊢
          arm64_sep_close
        refine steps_call_out_placed (dispPtr, dispCap.toNat, 1) hdealloc
          hpc4 hrun4 hsp_al4 hlr4 hcl4 hL4 hpre_dealloc ?_ ?_
        · intro sf _ hpost
          dsimp only [rustDeallocSpec] at hpost
          rw [sepConj_assoc] at hpost
          exact (not_satisfies_false_sepConj hpost).elim
        · intro st5 hpc5 hrun5 hsp5 hsp_al5 hcs5 hcl5 hL5 hpost5
          dsimp only [rustDeallocSpec] at hpost5
          rw [hsp4, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost5
          rcases hpost5 with ⟨htr5, hpost5⟩
          refine herr_tail st5 hpc5 hrun5 (by reg_chain) hsp_al5 (by reg_chain) (by reg_chain) (by reg_chain)
            hcl5 hL5 (by reg_chain) (by reg_chain) (by reg_chain) ?_
          rw [hstack_dealloc]
          simp only [sepConj_assoc] at hpost5 ⊢
          arm64_sep_close

end CryptoVerification.CliHandshake.TryDecPlaced
