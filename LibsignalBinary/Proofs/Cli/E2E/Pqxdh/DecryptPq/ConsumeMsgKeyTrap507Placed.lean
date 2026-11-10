/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ConsumeMsgKeySub507Placed
import Arm64.Trusted.Spec.Hoare
import all Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegMidS4A

/-!
# Relocatable Segment `S4` (`ConsumeMsgKey`) Seam on Block `507`

Relocatable `[LibsignalPlacement]` verification of Segment `S4` (`<ProtocolAddress as Display>::fmt`,
`RatchetState::consume_message_key`, and formatted-string drop, `S4SeamPlaced`) on Block `507`.
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

private def trNonRatchetAt (A : RustAlloc) (sp : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  vecU8At A (sp + 232#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
  ((sp + 256#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
  ((sp + 288#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)

private theorem trAt_split_ratchet (A : RustAlloc) (sp : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    trAt A (sp + 56#64) trG tr =
      ⌜∀ sc, tr.ratchet.senderChain = some sc →
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
      ratchetAt A (sp + 56#64) trG.ratchet tr.ratchet ∗
      trNonRatchetAt A sp trG tr := by
  unfold trAt trNonRatchetAt
  rw [BitVec.add_assoc, show (56#64 : BitVec 64) + 176#64 = 232#64 by rfl,
    BitVec.add_assoc, show (56#64 : BitVec 64) + 200#64 = 256#64 by rfl,
    BitVec.add_assoc, show (56#64 : BitVec 64) + 232#64 = 288#64 by rfl]

private def signalMessageNonTheirAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + 24#64) g.ctPtr m.ciphertext ∗
    boxU8At A (a + 40#64) g.serPtr m.serialized ∗
    optBoxU8At A (a + 88#64) g.addrPtr m.addresses ∗
    ((a + 104#64) ↦₃₂ m.counter) ∗ ((a + 108#64) ↦₃₂ m.previousCounter) ∗
    ((a + 112#64) ↦₈ m.messageVersion) ∗ memRegion (a + 113#64) 7

private theorem signalMessageAt_split_their (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      ((a + 56#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
      signalMessageNonTheirAt A g a m := by
  unfold signalMessageAt signalMessageNonTheirAt
  ac_rfl

theorem consumeMsgKey_507_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (haddrDisplay : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H) (lsmpl.base 215)
      (withLsCodeRoLoaded lsmpl (addrDisplaySpec A)))
    (hcmk_call : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H) (lsmpl.base 24)
      (withLsCodeRoLoaded lsmpl (cmkRawSpecPlaced C.F A)))
    (hdealloc : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    S4SeamPlaced ((blkPC_508).rebase (blkPl_508).base H) (blkPl_508).base C A ctl uuidTryParse S := by
  intro x trG tr st1 ck draws R s0 s hS4 hL
  rcases hS4 with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hfp, htrace, hcl, hvregs⟩,
    hx12, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hmem⟩
  change s.pc = (blkPl_508).base + 996#64 at hpc
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hfp
  rw [hsp29_eq] at hfp
  clear hsp29_eq
  unfold cliTryDecryptCommonHeapPlaced at hmem
  rw [lsLogOff_eq_logOff_placed] at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx12 hx20 hx23 hx25 hfp hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, hdrop, htake, hfull⟩ := split_chainKeyBytes ck
  let Out : State → Prop := fun s' =>
    match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
        x.msgType) tr.ratchet with
    | (.ok mkg, r2) =>
      (∃ trG', PqRecvStatePlaced (blkPl_508).base A ctl x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
      (s'.status = .Panicked ∧
        (s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))
    | (.error e, r2) =>
      (e ≠ .panic ∧ ∃ trG',
        ErrTailStatePlaced (blkPl_508).base A ctl x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
      (s'.status = .Panicked ∧
        ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
        (s'.mem ⊨ anyHeap ∗ R))
  have hOut_split : ∀ (prog : Program) (sm : State),
      (∃ s', Steps prog sm s' ∧ Out s') →
      match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
          x.msgType) tr.ratchet with
      | (.ok mkg, r2) =>
        ∃ s', Steps prog sm s' ∧
          ((∃ trG', PqRecvStatePlaced (blkPl_508).base A ctl x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (cliTryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)))
      | (.error e, r2) =>
        ∃ s', Steps prog sm s' ∧
          ((e ≠ .panic ∧ ∃ trG',
              ErrTailStatePlaced (blkPl_508).base A ctl x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R))) := by
    intro prog sm ⟨s', hst, hout⟩
    dsimp only [Out] at hout
    split at hout <;> exact ⟨s', hst, hout⟩
  apply hOut_split
  have hmem0 : s.mem ⊨
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 32 ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 368 ∗
       ((sp + 688#64) ↦₆₄ (w6 ++ w5)) ∗
       ((sp + 696#64) ↦₆₄ (w8 ++ w7)) ∗
       ((sp + 704#64) ↦₆₄ (w1 ++ w0)) ∗
       ((sp + 712#64) ↦₆₄ (w3 ++ w2)) ∗
       ((sp + 720#64) ↦₃₂ w4) ∗
       memRegion (sp + 724#64) 684 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       cliTapeAfter ctl x.cur x.rest draws ∗
       logOff tryDecryptPlacedImg ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R := by
    have hd := hdrop (sp + 688#64)
    have ht := htake (sp + 704#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hd ht
    rw [hd, ht] at hmem
    simp only [sepConj_assoc] at hmem
    simp only [sepConj_assoc]
    exact hmem
  refine steps_of_sepWP_placed hmem0 hL hcl
    (mid := lsmpl.base 215)
    (RegMid := fun sm1 =>
      sm1.readReg64 .x1 = sp + 1024#64 ∧
      sm1.readReg64 .x19 = x.ret ∧
      sm1.readReg64 .x20 = sp + 320#64 ∧
      sm1.readReg64 .x21 = x.ss ∧
      sm1.readReg64 .x22 = x.msgA ∧
      sm1.readReg64 .x23 = sp + 1280#64 ∧
      (sm1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
      sm1.readReg64 .x25 = sp + 400#64 ∧
      sm1.readReg64 .fp = sp + 1408#64 ∧
      sm1.readReg64 .lr = (blkPl_508).base + 1092#64 ∧
      sm1.sp = sp ∧ sm1.spAligned = true ∧ sm1.trace = s0.trace ∧
      calleeSavedVRegs sm1 = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG tr ∗
      memRegion x.ret 48 ∗
      memRegion sp 32 ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
      memRegion (sp + 44#64) 4 ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 416 ∗
      ((sp + 736#64) ↦ₛ chainKeyBytes ck) ∗
      memRegion (sp + 772#64) 204 ∗
      vecU8 A (sp + 976#64) [] ∗
      memRegion (sp + 1000#64) 24 ∗
      ((sp + 1024#64) ↦₆₄ (sp + 976#64)) ∗
      memRegion (sp + 1032#64) 40 ∗
      memRegion (sp + 1072#64) 336 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      cliTapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool) ?_ ?_
  · wp_conv_pre =>
      rw [mr_cut sp 320 96 272 368 416#64,
        mr_cut sp 416 4 268 272 420#64,
        mr_cut sp 420 8 260 268 428#64,
        mr_cut sp 428 8 252 260 436#64,
        mr_cut sp 724 12 672 684 736#64,
        mr_cut sp 736 8 664 672 744#64,
        mr_cut sp 744 8 656 664 752#64,
        mr_cut sp 752 8 648 656 760#64,
        mr_cut sp 760 8 640 648 768#64,
        mr_cut sp 768 4 636 640 772#64,
        mr_cut sp 772 204 432 636 976#64,
        mr_cut sp 976 8 424 432 984#64,
        mr_cut sp 984 8 416 424 992#64,
        mr_cut sp 992 8 408 416 1000#64,
        mr_cut sp 1000 8 400 408 1008#64,
        mr_cut sp 1008 8 392 400 1016#64,
        mr_cut sp 1016 8 384 392 1024#64,
        mr_cut sp 1024 8 376 384 1032#64,
        mr_cut sp 1032 8 368 376 1040#64,
        mr_cut sp 1040 8 360 368 1048#64,
        mr_cut sp 1048 8 352 360 1056#64,
        mr_cut sp 1056 8 344 352 1064#64,
        mr_cut sp 1064 8 336 344 1072#64]
      simp only [sepConj_assoc,
        memRegion_four (sp + 416#64),
        memRegion_eight (sp + 420#64),
        memRegion_eight (sp + 428#64),
        memRegion_eight (sp + 736#64),
        memRegion_eight (sp + 744#64),
        memRegion_eight (sp + 752#64),
        memRegion_eight (sp + 760#64),
        memRegion_four (sp + 768#64),
        memRegion_eight (sp + 976#64),
        memRegion_eight (sp + 984#64),
        memRegion_eight (sp + 992#64),
        memRegion_eight (sp + 1000#64),
        memRegion_eight (sp + 1008#64),
        memRegion_eight (sp + 1016#64),
        memRegion_eight (sp + 1024#64),
        memRegion_eight (sp + 1032#64),
        memRegion_eight (sp + 1040#64),
        memRegion_eight (sp + 1048#64),
        memRegion_eight (sp + 1056#64),
        memRegion_eight (sp + 1064#64)]
    wp_pull_exists
    wp_steps
    refine SepWP.focus_weaken (realign_416_436 sp w4 w5 w6 w7 w8) (by sep_focus) ?_
    wp_steps
    have hck_fold :
        ((sp + 736#64) ↦₆₄ (w1 ++ w0)) ∗ ((sp + 744#64) ↦₆₄ (w3 ++ w2)) ∗
        ((sp + 752#64) ↦₆₄ (w5 ++ w4)) ∗ ((sp + 760#64) ↦₆₄ (w7 ++ w6)) ∗
        ((sp + 768#64) ↦₃₂ w8) ⊢
        ((sp + 736#64) ↦ₛ chainKeyBytes ck) := by
      have hf := (hfull (sp + 736#64)).symm
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hf ⊢
      rw [hf]
      exact Entails.refl _
    refine SepWP.focus_weaken hck_fold (by sep_focus) ?_
    have hv_empty := empty_vecU8_intro A (sp + 976#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv_empty
    refine SepWP.focus_weaken hv_empty (by sep_focus) ?_
    refine SepWP.focus_weaken (pointsTo32_entails_memRegion (sp + 432#64) w8) (by sep_focus) ?_
    refine SepWP.focus_weaken (pointsTo32_entails_memRegion (sp + 720#64) w4) (by sep_focus) ?_
    have hm320 : memRegion (sp + 320#64) 416 =
        memRegion (sp + 320#64) 96 ∗ (memRegion (sp + 416#64) 8 ∗ (memRegion (sp + 424#64) 8 ∗
        (memRegion (sp + 432#64) 4 ∗ (memRegion (sp + 436#64) 252 ∗ (memRegion (sp + 688#64) 8 ∗
        (memRegion (sp + 696#64) 8 ∗ (memRegion (sp + 704#64) 8 ∗ (memRegion (sp + 712#64) 8 ∗
        (memRegion (sp + 720#64) 4 ∗ memRegion (sp + 724#64) 12))))))))) := by
      rw [mr_cut_add sp 320 96 320 (by decide),
        mr_cut_add sp 416 8 312 (by decide),
        mr_cut_add sp 424 8 304 (by decide),
        mr_cut_add sp 432 4 300 (by decide),
        mr_cut_add sp 436 252 48 (by decide),
        mr_cut_add sp 688 8 40 (by decide),
        mr_cut_add sp 696 8 32 (by decide),
        mr_cut_add sp 704 8 24 (by decide),
        mr_cut_add sp 712 8 16 (by decide),
        mr_cut_add sp 720 4 12 (by decide)]
    have hm1000 : memRegion (sp + 1000#64) 24 =
        memRegion (sp + 1000#64) 8 ∗ (memRegion (sp + 1008#64) 8 ∗ memRegion (sp + 1016#64) 8) := by
      rw [mr_cut_add sp 1000 8 16 (by decide), mr_cut_add sp 1008 8 8 (by decide)]
    have hm1032 : memRegion (sp + 1032#64) 40 =
        memRegion (sp + 1032#64) 8 ∗ (memRegion (sp + 1040#64) 8 ∗ (memRegion (sp + 1048#64) 8 ∗
        (memRegion (sp + 1056#64) 8 ∗ memRegion (sp + 1064#64) 8))) := by
      rw [mr_cut_add sp 1032 8 32 (by decide),
        mr_cut_add sp 1040 8 24 (by decide),
        mr_cut_add sp 1048 8 16 (by decide),
        mr_cut_add sp 1056 8 8 (by decide)]
    rw [hm320, hm1000, hm1032]
    wp_done
  · intro sm1 hpc1 hrun1 hcl1 hL1
      ⟨hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hfp1, hlr1, hsp1, hsp_al1, htr1, hvregs1⟩
      hm1
    have hm1032_split : memRegion (sp + 1032#64) 40 =
        (∃∗ vt : BitVec 64, (sp + 1032#64) ↦₆₄ vt) ∗ memRegion (sp + 1040#64) 32 := by
      rw [mr_cut_add sp 1032 8 32 (by decide), memRegion_eight (sp + 1032#64)]
    rw [hm1032_split] at hm1
    simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists] at hm1
    rcases hm1 with ⟨vt, hm1⟩
    have hpre_disp : sm1.mem ⊨
        (addrDisplaySpec A).pre (sp + 1024#64, sp + 976#64, vt, []) sm1 ∗
        ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG tr ∗
          memRegion x.ret 48 ∗
          memRegion sp 32 ∗
          ((sp + 32#64) ↦₆₄ x.locA) ∗
          ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 44#64) 4 ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 320#64) 416 ∗
          ((sp + 736#64) ↦ₛ chainKeyBytes ck) ∗
          memRegion (sp + 772#64) 204 ∗
          memRegion (sp + 1000#64) 24 ∗
          memRegion (sp + 1040#64) 32 ∗
          memRegion (sp + 1072#64) 336 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          cliTapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptPlacedImg ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - addrDisplayStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ R) := by
      dsimp only [addrDisplaySpec]
      rw [hsp1]
      rw [stackAt_sub sp tryDecryptSubStack addrDisplayStack] at hm1
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hx1_1, ?_⟩
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hm1 ⊢
      arm64_sep_close
    refine steps_call_out_placed_cro (sp + 1024#64, sp + 976#64, vt, []) haddrDisplay
      hpc1 hrun1 hsp_al1 hlr1 hcl1 hL1 hpre_disp ?_ ?_
    · intro sf hpan hpost
      dsimp only [addrDisplaySpec] at hpost
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨⟨halloc, htr_sub⟩, hpost⟩
      have halloc0 : allocFailedIn s0 sf := by
        unfold allocFailedIn at halloc ⊢; rw [← htr1]; exact halloc
      have htr0 : s0.trace <+: sf.trace := by rw [← htr1]; exact htr_sub
      rw [← sepConj_assoc] at hpost
      have hany : sf.mem ⊨ anyHeap ∗ R :=
        Satisfies.mono (sepConj_mono_left (Entails.top_right (fun _ => True.intro))) hpost
      dsimp only [Out]
      split
      · refine Or.inr ⟨hpan, ?_⟩
        rw [cliTryDecryptSpecPlaced_onPanic_eq]
        dsimp only [tryDecryptSpecPlaced, withLsCodeRoLoaded,
          tryDecryptRawSpecPlaced, tryDecryptSpec, Spec.inImage]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨Or.inr (Or.inr halloc0), htr0⟩, hany⟩
      · exact Or.inr ⟨hpan, ⟨Or.inr halloc0, htr0⟩, hany⟩
    · intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hclf1 hLf1 hpost1
      rcases hcsf1 with ⟨hx19_cs1, hx20_cs1, hx21_cs1, hx22_cs1, hx23_cs1, hx24_cs1, hx25_cs1, _, _, _, hfp_cs1, hvregs_cs1⟩
      have hx19_f1 : sf1.readReg64 .x19 = x.ret := hx19_cs1.trans hx19_1
      have hx20_f1 : sf1.readReg64 .x20 = sp + 320#64 := hx20_cs1.trans hx20_1
      have hx21_f1 : sf1.readReg64 .x21 = x.ss := hx21_cs1.trans hx21_1
      have hx22_f1 : sf1.readReg64 .x22 = x.msgA := hx22_cs1.trans hx22_1
      have hx23_f1 : sf1.readReg64 .x23 = sp + 1280#64 := hx23_cs1.trans hx23_1
      have hx24_f1 : (sf1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType := by
        rw [hx24_cs1]; exact hx24_1
      have hx25_f1 : sf1.readReg64 .x25 = sp + 400#64 := hx25_cs1.trans hx25_1
      have hfp_f1 : sf1.readReg64 .fp = sp + 1408#64 := hfp_cs1.trans hfp1
      have hvregs_f1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0 := hvregs_cs1.trans hvregs1
      have hsp_f1 : sf1.sp = sp := hspf1.trans hsp1
      dsimp only [addrDisplaySpec] at hpost1
      rw [hsp1] at hpost1
      simp only [vecU8, vecU8At, vecHeader, sepConj_assoc, sepExists_sepConj_left,
        sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨dispBs, dispCap, dispPtr, hpost1⟩
      rw [satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨hw0_f1, htr_f1⟩, hpost1⟩
      have htr_f1' : sf1.trace = s0.trace := htr_f1.trans htr1
      simp only [sepConj_pure_left_comm, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨hdisp1, hdisp2, _hdisp3⟩, hpost1⟩
      have hpost1' : sf1.mem ⊨
          (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 56#64) trG tr ∗
           (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
             (dispPtr ↦ₛ dispBs) ∗
             memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
           ((sp + 976#64) ↦₆₄ dispCap) ∗
           ((sp + 984#64) ↦₆₄ dispPtr) ∗
           ((sp + 992#64) ↦₆₄ BitVec.ofNat 64 dispBs.length) ∗
           ((sp + 1024#64) ↦₆₄ (sp + 976#64)) ∗
           memRegion x.ret 48 ∗
           memRegion sp 32 ∗
           ((sp + 32#64) ↦₆₄ x.locA) ∗
           ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 44#64) 4 ∗
           ((sp + 48#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 320#64) 416 ∗
           ((sp + 736#64) ↦ₛ chainKeyBytes ck) ∗
           memRegion (sp + 772#64) 204 ∗
           memRegion (sp + 1000#64) 24 ∗
           memRegion (sp + 1032#64) 40 ∗
           memRegion (sp + 1072#64) 336 ∗
           protocolAddressAt A x.rem x.remA ∗
           protocolAddressAt A x.loc x.locA ∗
           signalMessageAt A x.msgG x.msgA x.msg ∗
           cliTapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R := by
        rw [hm1032_split, stackAt_sub sp tryDecryptSubStack addrDisplayStack]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc,
          sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1 ⊢
        refine ⟨vt, ?_⟩
        arm64_sep_close
      let msgW : BitVec 32 := (sf1.readReg64 .x24).setWidth 32
      have hmsgW_byte : msgW.setWidth 8 = msgTypeByte x.msgType := by
        have h8 : msgW.setWidth 8 = (sf1.readReg64 .x24).setWidth 8 :=
          BitVec.setWidth_setWidth_of_le (sf1.readReg64 .x24) (by decide)
        exact h8.trans hx24_f1
      refine steps_of_sepWP_placed hpost1' hLf1 hclf1
        (mid := lsmpl.base 24)
        (RegMid := fun sm2 =>
          sm2.readReg64 .x0 = sp + 56#64 ∧
          sm2.readReg64 .x1 = x.msgA + 56#64 ∧
          sm2.readReg64 .x2 = sp + 736#64 ∧
          (sm2.readReg64 .x3).setWidth 32 = x.msg.counter ∧
          (sm2.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧
          sm2.readReg64 .x8 = sp + 400#64 ∧
          sm2.readReg64 .x19 = x.ret ∧
          sm2.readReg64 .x20 = sp + 320#64 ∧
          sm2.readReg64 .x21 = x.ss ∧
          sm2.readReg64 .x22 = x.msgA ∧
          sm2.readReg64 .x23 = sp + 1280#64 ∧
          sm2.readReg64 .x25 = sp + 400#64 ∧
          sm2.readReg64 .x27 = dispPtr ∧
          sm2.readReg64 .x28 = dispCap ∧
          sm2.readReg64 .fp = sp + 1408#64 ∧
          sm2.readReg64 .lr = (blkPl_508).base + 1144#64 ∧
          sm2.sp = sp ∧ sm2.spAligned = true ∧ sm2.trace = s0.trace ∧
          calleeSavedVRegs sm2 = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG tr ∗
          (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
            (dispPtr ↦ₛ dispBs) ∗
            memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
          memRegion x.ret 48 ∗
          memRegion sp 28 ∗
          ((sp + 28#64) ↦₃₂ msgW) ∗
          ((sp + 32#64) ↦₆₄ x.locA) ∗
          ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 44#64) 4 ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 320#64) 80 ∗
          memRegion (sp + 400#64) 88 ∗
          memRegion (sp + 488#64) 248 ∗
          ((sp + 736#64) ↦ₛ chainKeyBytes ck) ∗
          memRegion (sp + 772#64) 636 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          cliTapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptPlacedImg ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · have hsp0 : memRegion sp 32 = memRegion sp 28 ∗ memRegion (sp + 28#64) 4 := by
          have hm := mr_cut_add sp 0 28 4 (by decide)
          simp only [BitVec.add_zero] at hm
          exact hm
        wp_conv_pre =>
          rw [hsp0, memRegion_four (sp + 28#64),
            mr_cut sp 320 80 336 416 400#64,
            mr_cut sp 400 88 248 336 488#64]
          simp only [sepConj_assoc]
        wp_pull_exists
        wp_steps
        have hm772 : memRegion (sp + 772#64) 636 =
            memRegion (sp + 772#64) 204 ∗ (memRegion (sp + 976#64) 8 ∗ (memRegion (sp + 984#64) 8 ∗
            (memRegion (sp + 992#64) 8 ∗ (memRegion (sp + 1000#64) 24 ∗
            (memRegion (sp + 1024#64) 8 ∗ (memRegion (sp + 1032#64) 40 ∗
             memRegion (sp + 1072#64) 336)))))) := by
          rw [mr_cut_add sp 772 204 432 (by decide),
            mr_cut_add sp 976 8 424 (by decide),
            mr_cut_add sp 984 8 416 (by decide),
            mr_cut_add sp 992 8 408 (by decide),
            mr_cut_add sp 1000 24 384 (by decide),
            mr_cut_add sp 1024 8 376 (by decide),
            mr_cut_add sp 1032 40 336 (by decide)]
        rw [hm772]
        dsimp only [msgW]
        wp_done
      · intro sm2 hpc2 hrun2 hcl2 hL2
          ⟨hx0_2, hx1_2, hx2_2, hx3_2, hx4_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2,
           hx23_2, hx25_2, hx27_2, hx28_2, hfp2, hlr2, hsp2, hsp_al2, htr2, hvregs2⟩
          hm2
        let cmkX : CryptoVerification.LibsignalSession.ConsumeMessageKeyGhost :=
          { self := sp + 56#64
            G := trG.ratchet
            st := tr.ratchet
            their := x.msg.senderRatchetKey
            theirA := x.msgA + 56#64
            ck := ck
            ckA := sp + 736#64
            counter := x.msg.counter
            msgType := x.msgType
            ret := sp + 400#64 }
        have hcmk_model : cmkX.model C.F =
            Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
              x.msgType) tr.ratchet := rfl
        have hstack_cmk := stackAt_sub sp tryDecryptSubStack CryptoVerification.LibsignalSession.cmkStack
          (by decide) (by decide)
        rw [trAt_split_ratchet, signalMessageAt_split_their] at hm2
        simp only [sepConj_assoc] at hm2
        rw [sepConj_pure_left_comm, satisfies_pure_sepConj] at hm2
        rcases hm2 with ⟨hclamp, hm2⟩
        have hpre_cmk : sm2.mem ⊨
            (cmkRawSpecPlaced C.F A).pre cmkX sm2 ∗
            ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trNonRatchetAt A sp trG tr ∗
              (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
                (dispPtr ↦ₛ dispBs) ∗
                memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
              memRegion x.ret 48 ∗
              memRegion sp 28 ∗
              ((sp + 28#64) ↦₃₂ msgW) ∗
              ((sp + 32#64) ↦₆₄ x.locA) ∗
              ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
              memRegion (sp + 44#64) 4 ∗
              ((sp + 48#64) ↦₆₄ x.remA) ∗
              memRegion (sp + 320#64) 80 ∗
              memRegion (sp + 488#64) 248 ∗
              memRegion (sp + 772#64) 636 ∗
              protocolAddressAt A x.rem x.remA ∗
              protocolAddressAt A x.loc x.locA ∗
              signalMessageNonTheirAt A x.msgG x.msgA x.msg ∗
              cliTapeAfter ctl x.cur x.rest draws ∗
              memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
                (tryDecryptSubStack - CryptoVerification.LibsignalSession.cmkStack) ∗
              tryDecryptSavedRegs s0.sp s0) ∗ R) := by
          dsimp only [cmkRawSpecPlaced, cmkX]
          rw [hsp2, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0_2, hx1_2, hx2_2, hx3_2, hx4_2, hx8_2⟩, ?_⟩
          rw [hstack_cmk] at hm2
          simp only [sepConj_assoc] at hm2 ⊢
          arm64_sep_close
        refine steps_call_out_placed_cro cmkX hcmk_call
          hpc2 hrun2 hsp_al2 hlr2 hcl2 hL2 hpre_cmk ?_ ?_
        · intro sf hpan hpost
          dsimp only [cmkRawSpecPlaced] at hpost
          rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
          rcases hpost with ⟨⟨hpan_or, htr_sub⟩, hpost⟩
          have htr0 : s0.trace <+: sf.trace := by rw [← htr2]; exact htr_sub
          rw [← sepConj_assoc] at hpost
          have hany : sf.mem ⊨ anyHeap ∗ R :=
            Satisfies.mono (sepConj_mono_left (Entails.top_right (fun _ => True.intro))) hpost
          rw [hcmk_model] at hpan_or
          dsimp only [Out]
          split
          · next mkg r2 hmod =>
            rw [hmod] at hpan_or
            rcases hpan_or with hbad | halloc
            · cases hbad
            · have halloc0 : allocFailedIn s0 sf := by
                unfold allocFailedIn at halloc ⊢; rw [← htr2]; exact halloc
              refine Or.inr ⟨hpan, ?_⟩
              rw [cliTryDecryptSpecPlaced_onPanic_eq]
              dsimp only [tryDecryptSpecPlaced, withLsCodeRoLoaded,
                tryDecryptRawSpecPlaced, tryDecryptSpec, Spec.inImage]
              rw [sepConj_assoc, satisfies_pure_sepConj]
              exact ⟨⟨Or.inr (Or.inr halloc0), htr0⟩, hany⟩
          · next e r2 hmod =>
            rw [hmod] at hpan_or
            refine Or.inr ⟨hpan, ⟨?_, htr0⟩, hany⟩
            rcases hpan_or with hbad | halloc
            · exact Or.inl (Except.error.inj hbad)
            · unfold allocFailedIn at halloc ⊢; rw [← htr2]; exact Or.inr halloc
        · intro sf2 hpcf2 hrunf2 hspf2 hsp_alf2 hcsf2 hclf2 hLf2 hpost2
          dsimp only [cmkRawSpecPlaced] at hpost2
          rw [hsp2, hcmk_model] at hpost2
          simp only [cmkX, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
            satisfies_sepExists] at hpost2
          rcases hpost2 with ⟨rG', hpost2⟩
          rw [satisfies_pure_sepConj] at hpost2
          rcases hpost2 with ⟨⟨hnot_panic, htr_f2⟩, hpost2⟩
          have htr_f2' : sf2.trace = s0.trace := htr_f2.trans htr2
          rw [satisfies_pure_sepConj] at hpost2
          rcases hpost2 with ⟨_, hpost2⟩
          let r2 := (Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck
            x.msg.counter x.msgType) tr.ratchet).2
          let trG' : TrGhost := { trG with ratchet := rG' }
          have hclamp2 : ∀ sc, r2.senderChain = some sc →
              Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes := by
            intro sc hsc
            rw [consumeMessageKey_senderChain] at hsc
            exact hclamp sc hsc
          have hm_post2 : sf2.mem ⊨
              (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
               trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
               (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
                 (dispPtr ↦ₛ dispBs) ∗
                 memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
               consumeMessageKeyResultAt A (sp + 400#64) (Mut.exec (RatchetState.consumeMessageKey C.F
                 x.msg.senderRatchetKey ck x.msg.counter x.msgType) tr.ratchet).1 ∗
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
               A.pool) ∗ R := by
            have hm488 : memRegion (sp + 488#64) 920 =
                memRegion (sp + 488#64) 248 ∗ (memRegion (sp + 736#64) 36 ∗ memRegion (sp + 772#64) 636) := by
              rw [mr_cut_add sp 488 248 672 (by decide), mr_cut_add sp 736 36 636 (by decide)]
            rw [trAt_split_ratchet, signalMessageAt_split_their, hm488, hstack_cmk]
            dsimp only [trG', r2, trNonRatchetAt] at hpost2 ⊢
            simp only [sepConj_assoc] at hpost2 ⊢
            rw [sepConj_pure_left_comm, satisfies_pure_sepConj]
            refine ⟨hclamp2, ?_⟩
            arm64_sep_close
          clear hpost2
          dsimp only [Out]
          split
          · next mkg r2' hmod =>
            have hr2_eq : r2 = r2' := congrArg Prod.snd hmod
            subst hr2_eq
            have hres_eq : (Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck
                x.msg.counter x.msgType) tr.ratchet).1 = .ok mkg := congrArg Prod.fst hmod
            rw [hres_eq] at hm_post2
            exact consumeMsgKey_cmk_ok_507_placed C A ctl S H x trG' tr st1 r2 mkg draws R s0
              hsp0_al hsp_al' hdealloc hsp_def hdisp1 hdisp2 hmsgW_byte
              sf2 hpcf2 hrunf2 (by reg_chain) hsp_alf2 (by reg_chain) (by reg_chain) (by reg_chain)
              (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
              htr_f2' (by reg_chain) hclf2 hLf2 hm_post2
          · next e r2' hmod =>
            have hr2_eq : r2 = r2' := congrArg Prod.snd hmod
            subst hr2_eq
            have hres_eq : (Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck
                x.msg.counter x.msgType) tr.ratchet).1 = .error e := congrArg Prod.fst hmod
            have hne_panic : e ≠ .panic := by
              intro hp; subst hp; exact hnot_panic hres_eq
            rw [hres_eq] at hm_post2
            exact consumeMsgKey_cmk_err_507_placed C A ctl uuidTryParse H x trG' tr st1 r2 e
              draws R s0 hne_panic hsp0_al hsp_al' hdealloc hsp_def hdisp1 hdisp2
              sf2 hpcf2 hrunf2 (by reg_chain) hsp_alf2 (by reg_chain) (by reg_chain) (by reg_chain)
              (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) htr_f2' (by reg_chain) hclf2 hLf2
              hm_post2

end CryptoVerification.CliHandshake.TryDecPlaced
