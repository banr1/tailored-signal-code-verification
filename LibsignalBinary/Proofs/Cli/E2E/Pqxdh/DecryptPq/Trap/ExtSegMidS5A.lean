/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegMidBase
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Fetch
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBase
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Contract-Backed (`Stage2ContractsExt` / `AllocContractsMem4K`) Segment `S5` Helpers A (`ExtSegMidS5A`)

Proves `BS8.s5_dealloc_tail_ext` and `BS8.s5_recv_err_true_ext` on `tripleRatchetProgAtExt`.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto MessageKeyGenerator SessionState SignalProtocolError TripleRatchet)
open CryptoVerification (libsignalSessionImage)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser protocolAddressAt sessionStateAt signalMessageAt speWord utf8)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel TrGhost TryDecryptGhost
  extHookStack formatInnerSpec logOff rustDeallocExternSpecWithStack
  rustDeallocSpecWithStack trAt tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq (speBodyAt speTag tryDecryptSavedRegs tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive (buf_to_mr concat56_8_cbz64_zero
  extractLsb0_8_append56 mr_cut mr_cut_add sepWP_8_mr7_to_64 sp56_weaken sp_fp_eq
  speBodyAt_invalidState_fold stackAt_sub steps_call steps_done_of_sepWP_midMeta steps_of_sepWP
  tryDecryptMidMetaCore)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegMidS5A

attribute [local irreducible] Program.fetch Program.externAt?
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.s5_dealloc_tail_ext
    {parse : UuidParser}
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {entry sp seedCap seedPtr : BitVec 64}
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img = entry)
    (hentry_eq : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext img.base ext = entry)
    (hdealloc_call : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (hsp_def : s0.sp - 1504#64 = sp)
    (e : SignalProtocolError) (st2 : State)
    (hpc2 : st2.pc = entry + 2500#64)
    (hrun2 : st2.status = .Running)
    (hsp2 : st2.sp = sp)
    (hsp_al2 : st2.spAligned = true)
    (hfp2 : st2.readReg64 .fp = sp + 1408#64)
    (htr2 : st2.trace = s0.trace)
    (hvregs2 : calleeSavedVRegs st2 = calleeSavedVRegs s0)
    (hf2 : img.FrozenLoaded st2)
    (hsym2 : st2.symtab = img.symtab)
    (hL2 : (tripleRatchetProgAtExt img.base ext).CodeLoaded st2.mem)
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
       CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
       logOff img ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) st2 s' ∧
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1 e draws R s0 s' ∨
        (s'.status = .Panicked ∧
          s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)) := by
  decrypt_fetches_at_cli_ext hentry_eq 2500 24
  clear hentry_eq
  examples_hide_fetches
  have hsp_al2' : (st2.sp &&& 15#64 == 0#64) = true := hsp_al2
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp2]; exact hsp_al2
  simp only [← sepConj_assoc] at hm2
  by_cases hsc : seedCap = 0
  · simp only [hsc, ↓reduceIte] at hm2
    subst hsc
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState
    refine steps_done_of_sepWP_midMeta (s0 := s0)
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
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R))
      hm2 hL2 hf2 hsym2 ?_
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC tryDecryptMidMetaCore
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap
    rw [hentry, show (0x30c#64 : BitVec 64) = 780#64 by rfl]
    have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
    rw [hsp29_eq]; clear hsp29_eq
    rw [hsp_def]
    wp_conv_pre => simp only [sepConj_assoc]
    wp_steps
    refine SepWP.focus_weaken (sp56_weaken sp seedPtr 0#64) (by sep_focus) ?_
    wp_done
  · simp only [hsc, ↓reduceIte] at hm2
    have hsc_beq : (seedCap == 0#64) = false := beq_false_of_ne hsc
    refine steps_of_sepWP hm2 hL2 hf2 hsym2
      (mid := entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
      (RegMid := fun sm3 =>
        sm3.readReg64 .x0 = seedPtr ∧
        sm3.readReg64 .x1 = seedCap ∧
        sm3.readReg64 .x2 = 1#64 ∧
        sm3.readReg64 .lr = entry + 2520#64 ∧
        sm3.readReg64 .x19 = x.ret ∧
        sm3.readReg64 .x20 = sp + 320#64 ∧
        sm3.readReg64 .x26 = speTag e ∧
        sm3.readReg64 .fp = sp + 1408#64 ∧
        sm3.sp = sp ∧ sm3.spAligned = true ∧ sm3.trace = s0.trace ∧
        calleeSavedVRegs sm3 = calleeSavedVRegs s0)
      (P_mid :=
        A.pool ∗ A.live seedPtr seedCap.toNat 1 ∗ memRegion seedPtr seedCap.toNat ∗
        stackAt sp extHookStack ∗
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
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
        logOff img ∗
        memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - extHookStack) ∗
        tryDecryptSavedRegs s0.sp s0) ?_ ?_
    · wp_conv_pre =>
        rw [stackAt_sub sp tryDecryptSubStack extHookStack]
        simp only [sepConj_assoc]
      wp_steps
      refine SepWP.focus_weaken (sp56_weaken sp seedPtr seedCap) (by sep_focus) ?_
      refine SepWP.focus_weaken (buf_to_mr seedPtr mkg.seed seedCap.toNat hseed1 hseed2) (by sep_focus) ?_
      wp_done
    · intro sm3 hpcm3 hrunm3 hfm3 hsymm3 hLm3 ⟨hx0_3, hx1_3, hx2_3, hlr_3,
        hx19_3, hx20_3, hx26_3, hfp_3, hsp_3, hsp_al3, htr_3, hvregs_3⟩ hmm3
      have hpre_dealloc : sm3.mem ⊨
          (((rustDeallocExternSpecWithStack A extHookStack).inImage img).pre (seedPtr, seedCap.toNat, 1) sm3 ∗
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
            CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
            logOff img ∗
            memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - extHookStack) ∗
            tryDecryptSavedRegs s0.sp s0) ∗ R) := by
        dsimp only [rustDeallocExternSpecWithStack, Spec.inImage]
        rw [hsp_3, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
        refine ⟨⟨hfm3, hsymm3⟩, ⟨hx0_3, by rw [hx1_3], by rw [hx2_3]; rfl,
          ⟨BitVec.toNat_pos_of_ne_zero hsc, ⟨0, rfl⟩, by omega⟩⟩, ?_⟩
        simp only [sepConj_assoc] at hmm3 ⊢
        arm64_sep_close
      refine steps_call hdealloc_call (x := (seedPtr, seedCap.toNat, 1))
        hpcm3 hrunm3 hsp_al3 hlr_3 hfm3 hsymm3 hLm3 hpre_dealloc
        (fun sf _ hp => False.elim (by
          dsimp only [rustDeallocExternSpecWithStack, Spec.inImage] at hp
          rw [sepConj_assoc] at hp
          exact not_satisfies_false_sepConj hp)) ?_
      intro sf3 hpcf3 hrunf3 hspf3 hsp_alf3 hcsf3 hff3 hsymf3 hLf3 hpost3
      dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpecWithStack, Spec.inImage] at hpost3
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
           CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
           logOff img ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R := by
        rw [stackAt_sub sp tryDecryptSubStack extHookStack]
        simp only [sepConj_assoc] at hpost3 ⊢
        arm64_sep_close
      simp only [← sepConj_assoc] at hpost3'
      unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState
      refine steps_done_of_sepWP_midMeta (s0 := s0)
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
            CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R))
        hpost3' hLf3 hff3 hsymf3 ?_
      unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC tryDecryptMidMetaCore
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap
      rw [hentry, show (0x30c#64 : BitVec 64) = 780#64 by rfl]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]; clear hsp29_eq
      rw [hsp_def]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps
      wp_done

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.s5_recv_err_true_ext
    {parse : UuidParser}
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hloads : Obj.Loads libsignalSessionImage img)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {entry sp seedCap seedPtr : BitVec 64} {msgW : BitVec 32}
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img = entry)
    (hentry_eq : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext img.base ext = entry)
    (hfmt_call : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (entry + bv% ((2^64 + ls_off% "alloc::fmt::format::format_inner" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
      ((formatInnerSpec A).inImage img))
    (hdealloc_call : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (hsp_def : s0.sp - 1504#64 = sp)
    (sf1 : State)
    (hpcf1 : sf1.pc = entry + 1488#64)
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
    (hff1 : img.FrozenLoaded sf1)
    (hsymf1 : sf1.symtab = img.symtab)
    (hLf1 : (tripleRatchetProgAtExt img.base ext).CodeLoaded sf1.mem)
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
       CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
       logOff img ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) sf1 s' ∧
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1 .invalidState draws R s0 s' ∨
        (s'.status = .Panicked ∧
          s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)) := by
  have hadrp_dec := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.adrp_decryptStr_ext
    (ProofLib.ObjectLoad.base_aligned_of_loads hloads)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.entry_eq_base_ext hentry_eq)
  have hdealloc_tail := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.s5_dealloc_tail_ext
    (parse := parse) img C A ctl S ext x trG tr st1 mkg draws R s0
    (seedPtr := seedPtr) hsp0_al' hseed1 hseed2 hentry hentry_eq hdealloc_call hsp_def .invalidState
  decrypt_fetches_at_cli_ext hentry_eq 1488 12
  decrypt_fetches_at_cli_ext hentry_eq 2076 36
  decrypt_fetches_at_cli_ext hentry_eq 2412 88
  clear hentry_eq
  examples_hide_fetches
  have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hspf1]; exact hsp_alf1
  simp only [← sepConj_assoc] at hpost1'
  refine steps_of_sepWP hpost1' hLf1 hff1 hsymf1
    (mid := entry + bv% ((2^64 + ls_off% "alloc::fmt::format::format_inner" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
    (RegMid := fun sm2 =>
      sm2.readReg64 .x8 = sp + 408#64 ∧
      sm2.readReg64 .lr = entry + 2452#64 ∧
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
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
      logOff img ∗
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
  · intro sm2 hpcm2 hrunm2 hfm2 hsymm2 hLm2 ⟨hx8_2, hlr_2, hx19_2, hx20_2,
      hw24_2, hx25_2, hfp_2, hsp_2, hsp_al2, htr_2, hvregs_2⟩ hmm2
    have hpre_fmt : sm2.mem ⊨
        (((formatInnerSpec A).inImage img).pre (sp + 408#64) sm2 ∗
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
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - extHookStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ R) := by
      dsimp only [formatInnerSpec, Spec.inImage]
      rw [hsp_2, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
      refine ⟨⟨hfm2, hsymm2⟩, hx8_2, ?_⟩
      simp only [sepConj_assoc] at hmm2 ⊢
      arm64_sep_close
    refine steps_call hfmt_call (x := sp + 408#64)
      hpcm2 hrunm2 hsp_al2 hlr_2 hfm2 hsymm2 hLm2 hpre_fmt
      (fun sf hpan hpost =>
        ⟨hpan, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.onPanic_of_formatInner_ext htr_2 hpost⟩) ?_
    intro sf2 hpcf2 hrunf2 hspf2 hsp_alf2 hcsf2 hff2 hsymf2 hLf2 hpost2
    dsimp only [formatInnerSpec, Spec.inImage] at hpost2
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
         CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
         logOff img ∗
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
    have hpost2_ro :=
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.rodata_decrypt_intro_ext
        hloads hff2.roData hpost2'
    rw [← hadrp_dec] at hpost2_ro
    simp only [← sepConj_assoc] at hpost2_ro
    refine steps_of_sepWP hpost2_ro hLf2 hff2 hsymf2
      (mid := entry + 2500#64)
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
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
        logOff img ∗
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
        (show _ ⊢ speBodyAt A (utf8 "decrypt") (sp + 360#64) .invalidState from
          speBodyAt_invalidState_fold A sp fmtCap fmtPtr _ fmtBs hfb) (by sep_focus) ?_
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
    · intro st2 hpc2 hrun2 hf2 hsym2 hL2 ⟨hx19_2, hx20_2, hx26_2, hfp_2, hsp_2, hsp_al2, htr_2, hvregs_2⟩ hm2
      exact hdealloc_tail st2 hpc2 hrun2 hsp_2 hsp_al2 hfp_2 htr_2 hvregs_2 hf2 hsym2 hL2
        hx19_2 hx20_2 hx26_2 hm2

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegMidS5A
