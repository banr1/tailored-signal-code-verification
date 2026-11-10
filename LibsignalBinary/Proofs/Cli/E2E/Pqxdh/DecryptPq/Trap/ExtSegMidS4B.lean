/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegMidBase
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Fetch
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegMidS4A
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBase
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Contract-Backed (`Stage2ContractsExt` / `AllocContractsMem4K`) Segment `S4` Helpers B (`ExtSegMidS4B`)

Proves `BS8.s4_cmk_err_ext` on `tripleRatchetProgAtExt`.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto RatchetState SessionState SignalProtocolError TripleRatchet)
open CryptoVerification.RustHeap (RustAlloc allocFailedIn)
open CryptoVerification.LibsignalSessionRepr (consumeMessageKeyResultAt)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser protocolAddressAt sessionStateAt signalMessageAt utf8)
open CryptoVerification.LibsignalTripleRatchet (TrGhost TryDecryptGhost
  extHookStack logOff rustDeallocExternSpecWithStack trAt tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq (speBodyAt speTag tryDecryptSavedRegs
  tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive (buf_to_mr extractLsb0_8_append56
  mr_cut mr_cut_add pts64_to_mr sp_fp_eq stackAt_sub steps_of_sepWP)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegMidS4A (ErrWordsRel
  resultAt_err_unpack speBodyAt_err_pack steps_call_out)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegMidS4B

attribute [local irreducible] Program.fetch Program.externAt?
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.s4_cmk_err_ext
    (img : Obj.Image) (_C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (_parse : UuidParser) (ext : String → Option (State → State))
    (x : TryDecryptGhost) (trG' : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (r2 : RatchetState) (e : SignalProtocolError)
    (draws : Nat) (R : SepProp) (s0 : State)
    {entry sp dispCap dispPtr : BitVec 64} {dispBs : List (BitVec 8)} {msgW : BitVec 32}
    (hne_panic : e ≠ .panic)
    (hsp0_al : s0.spAligned = true)
    (hsp_al' : (sp &&& 15#64 == 0#64) = true)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img = entry)
    (hentry_eq : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext img.base ext = entry)
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hdisp1 : dispBs.length ≤ dispCap.toNat)
    (hdisp2 : dispCap.toNat < 2 ^ 63)
    (sf2 : State)
    (hpcf2 : sf2.pc = entry + 1144#64)
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
    (hff2 : img.FrozenLoaded sf2)
    (hsymf2 : sf2.symtab = img.symtab)
    (hLf2 : (tripleRatchetProgAtExt img.base ext).CodeLoaded sf2.mem)
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
       CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
       logOff img ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) sf2 s' ∧
      ((e ≠ .panic ∧ ∃ trG'',
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG'' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
       (s'.status = .Panicked ∧
         ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
         (s'.mem ⊨ anyHeap ∗ R))) := by
  decrypt_fetches_at_cli_ext hentry_eq 1144 64
  clear hentry_eq
  examples_hide_fetches
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
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
        logOff img ∗
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
         CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
         logOff img ∗
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
  refine steps_of_sepWP hm_err hLf2 hff2 hsymf2
    (mid := entry + 1180#64)
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
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
      logOff img ∗
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
  · intro sm3 hpc3 hrun3 hf_fr3 hsym3 hL3
      ⟨hx19_3, hx20_3, hx26_3, hx27_3, hx28_3, hfp3, hsp3, hsp_al3, htr3, hvregs3⟩
      hm3
    have herr_tail : ∀ st4 : State,
        st4.pc = entry + 1200#64 → st4.status = .Running →
        st4.sp = sp → st4.spAligned = true →
        st4.readReg64 .fp = sp + 1408#64 → st4.trace = s0.trace →
        calleeSavedVRegs st4 = calleeSavedVRegs s0 →
        img.FrozenLoaded st4 → st4.symtab = img.symtab →
        (tripleRatchetProgAtExt img.base ext).CodeLoaded st4.mem →
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
           CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
           logOff img ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R) →
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) st4 s' ∧
          ((e ≠ .panic ∧ ∃ trG'',
              CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG'' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R))) := by
      intro st4 hpc4 hrun4 hsp4 hsp_al4 hfp4 htr4 hvregs4 hff4 hsym4 hL4 hx19_4 hx20_4 hx26_4 hm4
      refine steps_of_sepWP hm4 hL4 hff4 hsym4
        (mid := entry + 780#64)
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
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · wp_steps
        wp_done
      · intro sf hpcf hrunf hff hsymf _ ⟨hx19_f, hx20_f, hx26_f, hfp_f, hsp_f, hsp_alf, htr_f, hvregs_f⟩ hmf
        subst hsp_def
        refine ⟨sf, .refl _, Or.inl ⟨hne_panic, trG', ?_⟩⟩
        have hpc_err : sf.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC img := by
          rw [hpcf]; unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC; rw [hentry]
        have hfp_f' : sf.readReg64 .x29 = s0.sp - 96#64 := by
          change sf.readReg64 .fp = s0.sp - 96#64
          rw [hfp_f]; exact (sp_fp_eq rfl).symm
        refine ⟨hpc_err, ⟨hrunf, hsp_f, hsp0_al, hsp_alf, hfp_f', htr_f, hff, hsymf, hvregs_f⟩,
          hx19_f, hx20_f, hx26_f, ?_⟩
        dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap]
        simp only [sepConj_assoc] at hmf ⊢
        arm64_sep_close
    by_cases hcap : dispCap = 0
    · simp only [hcap, ↓reduceIte, emp_sepConj] at hm3
      subst hcap
      refine steps_of_sepWP hm3 hL3 hf_fr3 hsym3
        (mid := entry + 1200#64)
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
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · wp_steps
        wp_done
      · intro st4 hpc4 hrun4 hff4 hsym4 hL4 ⟨hx19_4, hx20_4, hx26_4, hfp4, hsp4, hsp_al4, htr4, hvregs4⟩ hm4
        exact herr_tail st4 hpc4 hrun4 hsp4 hsp_al4 hfp4 htr4 hvregs4 hff4 hsym4 hL4 hx19_4 hx20_4 hx26_4 hm4
    · simp only [hcap, ↓reduceIte] at hm3
      have hcap_beq : (dispCap == 0#64) = false := beq_false_of_ne hcap
      refine steps_of_sepWP hm3 hL3 hf_fr3 hsym3
        (mid := entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
        (RegMid := fun sm4 =>
          sm4.readReg64 .x0 = dispPtr ∧
          sm4.readReg64 .x1 = dispCap ∧
          sm4.readReg64 .x2 = 1#64 ∧
          sm4.readReg64 .x19 = x.ret ∧
          sm4.readReg64 .x20 = sp + 320#64 ∧
          sm4.readReg64 .x26 = speTag e ∧
          sm4.readReg64 .fp = sp + 1408#64 ∧
          sm4.readReg64 .lr = entry + 1200#64 ∧
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
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · wp_conv_pre => simp only [sepConj_assoc]
        wp_steps
        refine SepWP.focus_weaken (buf_to_mr dispPtr dispBs dispCap.toNat hdisp1 hdisp2)
          (by sep_focus) ?_
        wp_done
      · intro sm4 hpc4 hrun4 hf_fr4 hsym4 hL4
          ⟨hx0_4, hx1_4, hx2_4, hx19_4, hx20_4, hx26_4, hfp4, hlr4, hsp4, hsp_al4, htr4, hvregs4⟩
          hm4
        have hstack_dealloc := stackAt_sub sp tryDecryptSubStack extHookStack (by decide) (by decide)
        have hpre_dealloc : sm4.mem ⊨
            ((rustDeallocExternSpecWithStack A extHookStack).inImage img).pre
              (dispPtr, dispCap.toNat, 1) sm4 ∗
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
              CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
              logOff img ∗
              memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
                (tryDecryptSubStack - extHookStack) ∗
              tryDecryptSavedRegs s0.sp s0) ∗ R) := by
          dsimp only [rustDeallocExternSpecWithStack, Spec.inImage]
          rw [hsp4, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hf_fr4, hsym4⟩, ?_⟩
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0_4, by rw [hx1_4], by rw [hx2_4]; rfl,
            ⟨BitVec.toNat_pos_of_ne_zero hcap, ⟨0, rfl⟩, by omega⟩⟩, ?_⟩
          rw [hstack_dealloc] at hm4
          simp only [sepConj_assoc] at hm4 ⊢
          arm64_sep_close
        refine steps_call_out (dispPtr, dispCap.toNat, 1) hdealloc
          hpc4 hrun4 hsp_al4 hlr4 hf_fr4 hsym4 hL4 hpre_dealloc ?_ ?_
        · intro sf _ hpost
          dsimp only [rustDeallocExternSpecWithStack, Spec.inImage] at hpost
          rw [sepConj_assoc] at hpost
          exact (not_satisfies_false_sepConj hpost).elim
        · intro st5 hpc5 hrun5 hsp5 hsp_al5 hcs5 hff5 hsym5 hL5 hpost5
          rcases hcs5 with ⟨hx19_cs5, hx20_cs5, _, _, _, _, _, hx26_cs5, _, _, hfp_cs5, hvregs_cs5⟩
          have hx19_5 : st5.readReg64 .x19 = x.ret := hx19_cs5.trans hx19_4
          have hx20_5 : st5.readReg64 .x20 = sp + 320#64 := hx20_cs5.trans hx20_4
          have hx26_5 : st5.readReg64 .x26 = speTag e := hx26_cs5.trans hx26_4
          have hfp5 : st5.readReg64 .fp = sp + 1408#64 := hfp_cs5.trans hfp4
          have hvregs5 : calleeSavedVRegs st5 = calleeSavedVRegs s0 := hvregs_cs5.trans hvregs4
          have hsp5' : st5.sp = sp := hsp5.trans hsp4
          dsimp only [rustDeallocExternSpecWithStack, Spec.inImage] at hpost5
          rw [hsp4, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost5
          rcases hpost5 with ⟨htr5, hpost5⟩
          have htr5' : st5.trace = s0.trace := htr5.trans htr4
          refine herr_tail st5 hpc5 hrun5 hsp5' hsp_al5 hfp5 htr5' hvregs5 hff5 hsym5 hL5
            hx19_5 hx20_5 hx26_5 ?_
          rw [hstack_dealloc]
          simp only [sepConj_assoc] at hpost5 ⊢
          arm64_sep_close

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegMidS4B
