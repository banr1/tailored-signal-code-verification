/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBase
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Segment S5 (`PqRecv`) Proofs for `try_decrypt_with_state`

Verifies Segment S5 (`+0x5b8 → +0x5dc / +0x30c`) across fixed-image and relocatable
`[LibsignalPlacement]` configurations (`pqRecv_159_placed_ok`, `pqRecv_549_placed_ok`), calling
`spqr::recv` and transitioning to `DeriveKeysState` on `Ok` or formatting the error, freeing
`mkg.seed`, and entering `ErrTailState` on `Err`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56

namespace KeyDeriveCallees

theorem pqRecv_dealloc_tail (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {entry sp seedCap seedPtr : BitVec 64}
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hentry : tryDecryptEntry img = entry)
    (hentry_eq : KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry)
    (hdealloc_call : subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (e : SignalProtocolError) (st2 : State)
    (hpc2 : st2.pc = entry + bv% (2500))
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
       tapeAfter ctl x.cur x.rest draws ∗
       logOff img ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) st2 s' ∧
      (ErrTailState A ctl img x trG tr st1 e draws R s0 s' ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)) := by
  decrypt_fetches_at_ext hentry_eq 2500 24
  clear hentry_eq
  examples_hide_fetches
  have hsp_al2' : (st2.sp &&& 15#64 == 0#64) = true := hsp_al2
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp2]; exact hsp_al2
  simp only [← sepConj_assoc] at hm2
  by_cases hsc : seedCap = 0
  · simp only [hsc, ↓reduceIte] at hm2
    subst hsc
    unfold ErrTailState
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
          tryDecryptCommonHeap A ctl img x draws s0 ∗ R))
      hm2 hL2 hf2 hsym2 ?_
    unfold errTailPC tryDecryptMidMetaCore tryDecryptCommonHeap
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
      (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      (RegMid := fun sm3 =>
        sm3.readReg64 .x0 = seedPtr ∧
        sm3.readReg64 .x1 = seedCap ∧
        sm3.readReg64 .x2 = 1#64 ∧
        sm3.readReg64 .lr = entry + bv% (2520) ∧
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
        tapeAfter ctl x.cur x.rest draws ∗
        logOff img ∗
        memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - allocHookStack) ∗
        tryDecryptSavedRegs s0.sp s0) ?_ ?_
    · wp_conv_pre =>
        rw [stackAt_sub sp tryDecryptSubStack allocHookStack]
        simp only [sepConj_assoc]
      wp_steps
      refine SepWP.focus_weaken (sp56_weaken sp seedPtr seedCap) (by sep_focus) ?_
      refine SepWP.focus_weaken (buf_to_mr seedPtr mkg.seed seedCap.toNat hseed1 hseed2) (by sep_focus) ?_
      wp_done
    · intro sm3 hpcm3 hrunm3 hfm3 hsymm3 hLm3 ⟨hx0_3, hx1_3, hx2_3, hlr_3,
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
            tapeAfter ctl x.cur x.rest draws ∗
            logOff img ∗
            memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - allocHookStack) ∗
            tryDecryptSavedRegs s0.sp s0) ∗ R) := by
        dsimp only [rustDeallocSpec]
        rw [hsp_3, sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0_3, by rw [hx1_3], by rw [hx2_3]; rfl⟩, ?_⟩
        simp only [sepConj_assoc] at hmm3 ⊢
        arm64_sep_close
      refine steps_call hdealloc_call (x := (seedPtr, seedCap.toNat, 1))
        hpcm3 hrunm3 hsp_al3 hlr_3 hfm3 hsymm3 hLm3 hpre_dealloc
        (fun sf _ hp => False.elim (by
          dsimp only [rustDeallocSpec] at hp
          rw [sepConj_assoc] at hp
          exact not_satisfies_false_sepConj hp)) ?_
      intro sf3 hpcf3 hrunf3 hspf3 hsp_alf3 hcsf3 hff3 hsymf3 hLf3 hpost3
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
           tapeAfter ctl x.cur x.rest draws ∗
           logOff img ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R := by
        rw [stackAt_sub sp tryDecryptSubStack allocHookStack]
        simp only [sepConj_assoc] at hpost3 ⊢
        arm64_sep_close
      simp only [← sepConj_assoc] at hpost3'
      unfold ErrTailState
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
            tryDecryptCommonHeap A ctl img x draws s0 ∗ R))
        hpost3' hLf3 hff3 hsymf3 ?_
      unfold errTailPC tryDecryptMidMetaCore tryDecryptCommonHeap
      rw [hentry, show (0x30c#64 : BitVec 64) = 780#64 by rfl]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]; clear hsp29_eq
      rw [hsp_def]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps
      wp_done

theorem pqRecv_recv_err_true (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hloads : Obj.Loads libsignalSessionImage img)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {entry sp seedCap seedPtr : BitVec 64} {msgW : BitVec 32}
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hentry : tryDecryptEntry img = entry)
    (hentry_eq : KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry)
    (hfmt_call : subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (sf1 : State)
    (hpcf1 : sf1.pc = entry + bv% (1488))
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
       tapeAfter ctl x.cur x.rest draws ∗
       logOff img ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) sf1 s' ∧
      (ErrTailState A ctl img x trG tr st1 .invalidState draws R s0 s' ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)) := by
  have hadrp_dec := adrp_decryptStr (base_aligned_of_loads hloads) (KeyDeriveCallees.entry_eq_base_ext hentry_eq)
  have hdealloc_tail := KeyDeriveCallees.pqRecv_dealloc_tail img C A ctl S ext x trG tr st1 mkg draws R s0
    (seedPtr := seedPtr) hsp0_al' hseed1 hseed2 hentry hentry_eq hdealloc_call hsp_def .invalidState
  decrypt_fetches_at_ext hentry_eq 1488 12
  decrypt_fetches_at_ext hentry_eq 2076 36
  decrypt_fetches_at_ext hentry_eq 2412 88
  clear hentry_eq
  examples_hide_fetches
  have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hspf1]; exact hsp_alf1
  simp only [← sepConj_assoc] at hpost1'
  refine steps_of_sepWP hpost1' hLf1 hff1 hsymf1
    (mid := entry + bv% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
    (RegMid := fun sm2 =>
      sm2.readReg64 .x8 = sp + 408#64 ∧
      sm2.readReg64 .lr = entry + bv% (2452) ∧
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
      tapeAfter ctl x.cur x.rest draws ∗
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
          tapeAfter ctl x.cur x.rest draws ∗
          logOff img ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - extHookStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ R) := by
      dsimp only [formatInnerSpec]
      rw [hsp_2, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hx8_2, ?_⟩
      simp only [sepConj_assoc] at hmm2 ⊢
      arm64_sep_close
    refine steps_call hfmt_call (x := sp + 408#64)
      hpcm2 hrunm2 hsp_al2 hlr_2 hfm2 hsymm2 hLm2 hpre_fmt
      (fun sf hpan hpost => ⟨hpan, onPanic_of_formatInner htr_2 hpost⟩) ?_
    intro sf2 hpcf2 hrunf2 hspf2 hsp_alf2 hcsf2 hff2 hsymf2 hLf2 hpost2
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
         tapeAfter ctl x.cur x.rest draws ∗
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
    have hpost2_ro := rodata_decrypt_intro hloads hff2.roData hpost2'
    rw [← hadrp_dec] at hpost2_ro
    simp only [← sepConj_assoc] at hpost2_ro
    refine steps_of_sepWP hpost2_ro hLf2 hff2 hsymf2
      (mid := entry + bv% (2500))
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
        tapeAfter ctl x.cur x.rest draws ∗
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
    · intro st2 hpc2 hrun2 hf2 hsym2 hL2 ⟨hx19_2, hx20_2, hx26_2, hfp_2, hsp_2, hsp_al2, htr_2, hvregs_2⟩ hm2
      exact hdealloc_tail st2 hpc2 hrun2 hsp_2 hsp_al2 hfp_2 htr_2 hvregs_2 hf2 hsym2 hL2
        hx19_2 hx20_2 hx26_2 hm2

theorem pqRecv_recv_err_false (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {entry sp seedCap seedPtr : BitVec 64} {msgW : BitVec 32} {d : BitVec 8}
    (hmsgW : msgW.setWidth 8 = msgTypeByte x.msgType)
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hentry : tryDecryptEntry img = entry)
    (hentry_eq : KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry)
    (hfmt_call : subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hd_ne : d ≠ 0#8)
    (sf1 : State)
    (hpcf1 : sf1.pc = entry + bv% (1488))
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
       tapeAfter ctl x.cur x.rest draws ∗
       logOff img ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) sf1 s' ∧
      (ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .pqRatchet) draws R s0 s' ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)) := by
  have hdealloc_tail := KeyDeriveCallees.pqRecv_dealloc_tail img C A ctl S ext x trG tr st1 mkg draws R s0
    (seedPtr := seedPtr) hsp0_al' hseed1 hseed2 hentry hentry_eq hdealloc_call hsp_def (.invalidMessage x.msgType .pqRatchet)
  decrypt_fetches_at_ext hentry_eq 1488 12
  decrypt_fetches_at_ext hentry_eq 2076 92
  decrypt_fetches_at_ext hentry_eq 2468 32
  clear hentry_eq
  examples_hide_fetches
  have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hspf1]; exact hsp_alf1
  have hd_cbz1 : (BitVec.setWidth 32 d == 0#32) = false := byte_ne_zero_cbz32 hd_ne
  have hd_cbz2 : (BitVec.setWidth 32 (BitVec.setWidth 64 d) == 0#32) = false :=
    byte_ne_zero_cbz64_32 hd_ne
  simp only [← sepConj_assoc] at hpost1'
  refine steps_of_sepWP hpost1' hLf1 hff1 hsymf1
    (mid := entry + bv% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
    (RegMid := fun sm2 =>
      sm2.readReg64 .x8 = sp + 408#64 ∧
      sm2.readReg64 .lr = entry + bv% (2156) ∧
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
      tapeAfter ctl x.cur x.rest draws ∗
      logOff img ∗
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
  · intro sm2 hpcm2 hrunm2 hfm2 hsymm2 hLm2 ⟨hx8_2, hlr_2, hx19_2, hx20_2,
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
          tapeAfter ctl x.cur x.rest draws ∗
          logOff img ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - extHookStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ R) := by
      dsimp only [formatInnerSpec]
      rw [hsp_2, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hx8_2, ?_⟩
      simp only [sepConj_assoc] at hmm2 ⊢
      arm64_sep_close
    refine steps_call hfmt_call (x := sp + 408#64)
      hpcm2 hrunm2 hsp_al2 hlr_2 hfm2 hsymm2 hLm2 hpre_fmt
      (fun sf hpan hpost => ⟨hpan, onPanic_of_formatInner htr_2 hpost⟩) ?_
    intro sf2 hpcf2 hrunf2 hspf2 hsp_alf2 hcsf2 hff2 hsymf2 hLf2 hpost2
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
         tapeAfter ctl x.cur x.rest draws ∗
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
    simp only [← sepConj_assoc] at hpost2'
    refine steps_of_sepWP hpost2' hLf2 hff2 hsymf2
      (mid := entry + bv% (2500))
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
        tapeAfter ctl x.cur x.rest draws ∗
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
    · intro st2 hpc2 hrun2 hf2 hsym2 hL2 ⟨hx19_2, hx20_2, hx26_2, hfp_2, hsp_2, hsp_al2, htr_2, hvregs_2⟩ hm2
      exact hdealloc_tail st2 hpc2 hrun2 hsp_2 hsp_al2 hfp_2 htr_2 hvregs_2 hf2 hsym2 hL2
        hx19_2 hx20_2 hx26_2 hm2

@[irreducible] def SpqrRecvContractX (img : Obj.Image) (A : RustAlloc) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
    (spqrRecvSpec A S img)

theorem spqrRecv_ok_at_entry_of_spqr {img : Obj.Image} {A : RustAlloc} {S : SpqrModel}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hspqr : SpqrRecvContractX img A S ext)
    (hentry : fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      (spqrRecvSpec A S img) := by
  unfold SpqrRecvContractX at hspqr
  rw [← hentry, ← fnAddr_tryDecrypt_ext_eq]
  exact sub_ok_at_of_fnAddr hspqr tryDecryptName (num% (ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) hk_spqrRecv

theorem pqRecv_dealloc_tail_x (img : Obj.Image) (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {entry sp seedCap seedPtr : BitVec 64}
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hentry : tryDecryptEntry img = entry)
    (hentry_eq : KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry)
    (hdealloc_call : subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (hsp_def : s0.sp - 1504#64 = sp)
    (e : SignalProtocolError) (st2 : State)
    (hpc2 : st2.pc = entry + bv% (2500))
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
       tapeAfter ctl x.cur x.rest draws ∗
       logOff img ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) st2 s' ∧
      (ErrTailState A ctl img x trG tr st1 e draws R s0 s' ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)) := by
  decrypt_fetches_at_ext hentry_eq 2500 24
  clear hentry_eq
  examples_hide_fetches
  have hsp_al2' : (st2.sp &&& 15#64 == 0#64) = true := hsp_al2
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp2]; exact hsp_al2
  simp only [← sepConj_assoc] at hm2
  by_cases hsc : seedCap = 0
  · simp only [hsc, ↓reduceIte] at hm2
    subst hsc
    unfold ErrTailState
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
          tryDecryptCommonHeap A ctl img x draws s0 ∗ R))
      hm2 hL2 hf2 hsym2 ?_
    unfold errTailPC tryDecryptMidMetaCore tryDecryptCommonHeap
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
      (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      (RegMid := fun sm3 =>
        sm3.readReg64 .x0 = seedPtr ∧
        sm3.readReg64 .x1 = seedCap ∧
        sm3.readReg64 .x2 = 1#64 ∧
        sm3.readReg64 .lr = entry + bv% (2520) ∧
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
        tapeAfter ctl x.cur x.rest draws ∗
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
            tapeAfter ctl x.cur x.rest draws ∗
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
           tapeAfter ctl x.cur x.rest draws ∗
           logOff img ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R := by
        rw [stackAt_sub sp tryDecryptSubStack extHookStack]
        simp only [sepConj_assoc] at hpost3 ⊢
        arm64_sep_close
      simp only [← sepConj_assoc] at hpost3'
      unfold ErrTailState
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
            tryDecryptCommonHeap A ctl img x draws s0 ∗ R))
        hpost3' hLf3 hff3 hsymf3 ?_
      unfold errTailPC tryDecryptMidMetaCore tryDecryptCommonHeap
      rw [hentry, show (0x30c#64 : BitVec 64) = 780#64 by rfl]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]; clear hsp29_eq
      rw [hsp_def]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps
      wp_done

theorem pqRecv_recv_err_true_x (img : Obj.Image) (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hloads : Obj.Loads libsignalSessionImage img)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {entry sp seedCap seedPtr : BitVec 64} {msgW : BitVec 32}
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hentry : tryDecryptEntry img = entry)
    (hentry_eq : KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry)
    (hfmt_call : subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) ((formatInnerSpec A).inImage img))
    (hdealloc_call : subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (hsp_def : s0.sp - 1504#64 = sp)
    (sf1 : State)
    (hpcf1 : sf1.pc = entry + bv% (1488))
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
       tapeAfter ctl x.cur x.rest draws ∗
       logOff img ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) sf1 s' ∧
      (ErrTailState A ctl img x trG tr st1 .invalidState draws R s0 s' ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)) := by
  have hadrp_dec := adrp_decryptStr (base_aligned_of_loads hloads) (KeyDeriveCallees.entry_eq_base_ext hentry_eq)
  have hdealloc_tail := KeyDeriveCallees.pqRecv_dealloc_tail_x img C decFn A ctl S ext x trG tr st1 mkg draws R s0
    (seedPtr := seedPtr) hsp0_al' hseed1 hseed2 hentry hentry_eq hdealloc_call hsp_def .invalidState
  decrypt_fetches_at_ext hentry_eq 1488 12
  decrypt_fetches_at_ext hentry_eq 2076 36
  decrypt_fetches_at_ext hentry_eq 2412 88
  clear hentry_eq
  examples_hide_fetches
  have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hspf1]; exact hsp_alf1
  simp only [← sepConj_assoc] at hpost1'
  refine steps_of_sepWP hpost1' hLf1 hff1 hsymf1
    (mid := entry + bv% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
    (RegMid := fun sm2 =>
      sm2.readReg64 .x8 = sp + 408#64 ∧
      sm2.readReg64 .lr = entry + bv% (2452) ∧
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
      tapeAfter ctl x.cur x.rest draws ∗
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
          tapeAfter ctl x.cur x.rest draws ∗
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
      (fun sf hpan hpost => ⟨hpan, onPanic_of_formatInner_fn htr_2 hpost⟩) ?_
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
         tapeAfter ctl x.cur x.rest draws ∗
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
    have hpost2_ro := rodata_decrypt_intro hloads hff2.roData hpost2'
    rw [← hadrp_dec] at hpost2_ro
    simp only [← sepConj_assoc] at hpost2_ro
    refine steps_of_sepWP hpost2_ro hLf2 hff2 hsymf2
      (mid := entry + bv% (2500))
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
        tapeAfter ctl x.cur x.rest draws ∗
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
    · intro st2 hpc2 hrun2 hf2 hsym2 hL2 ⟨hx19_2, hx20_2, hx26_2, hfp_2, hsp_2, hsp_al2, htr_2, hvregs_2⟩ hm2
      exact hdealloc_tail st2 hpc2 hrun2 hsp_2 hsp_al2 hfp_2 htr_2 hvregs_2 hf2 hsym2 hL2
        hx19_2 hx20_2 hx26_2 hm2

theorem pqRecv_recv_err_false_x (img : Obj.Image) (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {entry sp seedCap seedPtr : BitVec 64} {msgW : BitVec 32} {d : BitVec 8}
    (hmsgW : msgW.setWidth 8 = msgTypeByte x.msgType)
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hentry : tryDecryptEntry img = entry)
    (hentry_eq : KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry)
    (hfmt_call : subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) ((formatInnerSpec A).inImage img))
    (hdealloc_call : subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hd_ne : d ≠ 0#8)
    (sf1 : State)
    (hpcf1 : sf1.pc = entry + bv% (1488))
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
       tapeAfter ctl x.cur x.rest draws ∗
       logOff img ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) sf1 s' ∧
      (ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .pqRatchet) draws R s0 s' ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)) := by
  have hdealloc_tail := KeyDeriveCallees.pqRecv_dealloc_tail_x img C decFn A ctl S ext x trG tr st1 mkg draws R s0
    (seedPtr := seedPtr) hsp0_al' hseed1 hseed2 hentry hentry_eq hdealloc_call hsp_def (.invalidMessage x.msgType .pqRatchet)
  decrypt_fetches_at_ext hentry_eq 1488 12
  decrypt_fetches_at_ext hentry_eq 2076 92
  decrypt_fetches_at_ext hentry_eq 2468 32
  clear hentry_eq
  examples_hide_fetches
  have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hspf1]; exact hsp_alf1
  have hd_cbz1 : (BitVec.setWidth 32 d == 0#32) = false := byte_ne_zero_cbz32 hd_ne
  have hd_cbz2 : (BitVec.setWidth 32 (BitVec.setWidth 64 d) == 0#32) = false :=
    byte_ne_zero_cbz64_32 hd_ne
  simp only [← sepConj_assoc] at hpost1'
  refine steps_of_sepWP hpost1' hLf1 hff1 hsymf1
    (mid := entry + bv% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
    (RegMid := fun sm2 =>
      sm2.readReg64 .x8 = sp + 408#64 ∧
      sm2.readReg64 .lr = entry + bv% (2156) ∧
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
      tapeAfter ctl x.cur x.rest draws ∗
      logOff img ∗
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
  · intro sm2 hpcm2 hrunm2 hfm2 hsymm2 hLm2 ⟨hx8_2, hlr_2, hx19_2, hx20_2,
      hw24_2, hx25_2, hx26_2, hfp_2, hsp_2, hsp_al2, htr_2, hvregs_2⟩ hmm2
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
          tapeAfter ctl x.cur x.rest draws ∗
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
      (fun sf hpan hpost => ⟨hpan, onPanic_of_formatInner_fn htr_2 hpost⟩) ?_
    intro sf2 hpcf2 hrunf2 hspf2 hsp_alf2 hcsf2 hff2 hsymf2 hLf2 hpost2
    dsimp only [formatInnerSpec, Spec.inImage] at hpost2
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
         tapeAfter ctl x.cur x.rest draws ∗
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
    simp only [← sepConj_assoc] at hpost2'
    refine steps_of_sepWP hpost2' hLf2 hff2 hsymf2
      (mid := entry + bv% (2500))
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
        tapeAfter ctl x.cur x.rest draws ∗
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
    · intro st2 hpc2 hrun2 hf2 hsym2 hL2 ⟨hx19_2, hx20_2, hx26_2, hfp_2, hsp_2, hsp_al2, htr_2, hvregs_2⟩ hm2
      exact hdealloc_tail st2 hpc2 hrun2 hsp_2 hsp_al2 hfp_2 htr_2 hvregs_2 hf2 hsym2 hL2
        hx19_2 hx20_2 hx26_2 hm2

end KeyDeriveCallees

/-- Attach a pure fact `p` to the normal-return arm of an S5 outcome (the `spqr::recv` post's no-panic
conjunct, threaded into `DeriveKeysState` / `ErrTailState`). -/
theorem s5_out_add_np {prog : Program} {s : State} {N PanicOut : State → Prop} {p : Prop}
    (hp : p) (h : ∃ s', Steps prog s s' ∧ (N s' ∨ PanicOut s')) :
    ∃ s', Steps prog s s' ∧ ((N s' ∧ p) ∨ PanicOut s') := by
  obtain ⟨s', hs, hN | hP⟩ := h
  · exact ⟨s', hs, Or.inl ⟨hN, hp⟩⟩
  · exact ⟨s', hs, Or.inr hP⟩

/-- `(Q, Pstk, F)`-parameterized Segment S5 contract on `tripleRatchetProgAtExt img.base ext`,
crossing `spqr::recv` with `spqrRecvSpecQF Q Pstk F A S img`. -/
def S5SpecExtQF (Q : List (BitVec 8) → Prop) (Pstk : Nat → Prop) (F : SepProp)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
    (spqrRecvSpecQF Q Pstk F A S img) →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
      (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      tr.pqrState = x.st.pqRatchetState →
      Pstk (s0.sp - 1504#64).toNat →
      PqRecvState A ctl img x trG tr st1 mkg draws (F ∗ R) s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws (F ∗ R) s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((ErrTailState A ctl img x trG tr st1 e draws (F ∗ R) s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- Parameterized Segment S5 verification (`S5SpecExtQF`) on `tripleRatchetProgAtExt`. -/
theorem pqRecv_ok_extQF {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F : SepProp}
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (ext : String → Option (State → State)) :
    S5SpecExtQF Q Pstk F img C A ctl uuidTryParse S ext := by
  intro hloads hS hrecvOk x trG tr st1 mkg draws R s0 s hQ hpqr_eq hstk h5 hL
  rcases h5 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25,
    seedCap, seedPtr, msgW, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfrozen, hsym, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 :=
    ⟨hseed1, hseed2, hseed3⟩
  have hentry := entryOf_eq_tripleRatchetProgAtExt (ext := ext) hloads tryDecryptName
  change tryDecryptEntry img = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName at hentry
  unfold segPqRecvPC at hpc
  rw [show (0x5b8#64 : BitVec 64) = 1464#64 by rfl] at hpc
  rw [hentry] at hpc
  have hentry_eq := (KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq img.base ext).symm
  have hrecv_call := KeyDeriveCallees.spqrRecv_ok_at_entry_extQF hrecvOk hentry_eq
  clear hrecvOk
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName = entry
  have hfmt_call := KeyDeriveCallees.formatInner_ok_at_entry_ext hS hentry_eq
  have hdealloc_call := KeyDeriveCallees.dealloc_ok_at_entry_ext hS.toAllocContracts hentry_eq
  decrypt_fetches_at_ext hentry_eq 1464 36
  examples_hide_fetches
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29
  clear hsp29_eq
  have hmsg_len : x.msg.pqRatchet.length < 2 ^ 40 := by
    have hm' := hmem
    simp only [← sepConj_assoc] at hm'
    rw [sepConj_assoc _ F R,
      sepConj_assoc _ (tryDecryptCommonHeap A ctl img x draws s0) (F ∗ R)] at hm'
    exact msg_pqRatchet_lt_of_commonHeap hm'
  unfold tryDecryptCommonHeap at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx29 hstk hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  simp only [← sepConj_assoc] at hmem
  rw [sepConj_assoc _ F R] at hmem
  suffices ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        (DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws (F ∗ R) s0 s' ∧
          S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)
      | .error sd =>
        let e := if sd = true then .invalidState else .invalidMessage x.msgType .pqRatchet
        (ErrTailState A ctl img x trG tr st1 e draws (F ∗ R) s0 s' ∧
          S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R) by
    cases hrecv_eq : S.recv tr.pqrState x.msg.pqRatchet with
    | error sd =>
      rw [hrecv_eq] at this
      exact this
    | ok pair =>
      rcases pair with ⟨newPqrState, pqrKey⟩
      rw [hrecv_eq] at this
      exact this
  refine steps_of_sepWP hmem hL hfrozen hsym
    (mid := entry + bv% (ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
    (RegMid := fun sm =>
      sm.readReg64 .x0 = sp + 232#64 ∧
      sm.readReg64 .x1 = x.msgA ∧
      sm.readReg64 .x8 = sp + 1280#64 ∧
      sm.readReg64 .lr = entry + bv% (1488) ∧
      sm.readReg64 .x19 = x.ret ∧
      sm.readReg64 .x20 = sp + 320#64 ∧
      sm.readReg64 .x21 = x.ss ∧
      sm.readReg64 .x22 = x.msgA ∧
      sm.readReg64 .x23 = sp + 1280#64 ∧
      (sm.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm.readReg64 .x25 = sp + 400#64 ∧
      sm.readReg64 .x27 = sp + 56#64 ∧
      sm.readReg64 .x28 = sp + 1280#64 ∧
      sm.readReg64 .fp = sp + 1408#64 ∧
      sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    (P_mid :=
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
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₆₄ seedCap) ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 784 ∗
      ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 1116#64) 164 ∗
      memRegion (sp + 1280#64) 48 ∗
      memRegion (sp + 1328#64) 80 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      tapeAfter ctl x.cur x.rest draws ∗
      logOff img ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool)
    ?_ ?_
  · wp_steps
    have hm1116 : memRegion (sp + 1116#64) 292 =
        memRegion (sp + 1116#64) 164 ∗ (memRegion (sp + 1280#64) 48 ∗ memRegion (sp + 1328#64) 80) := by
      rw [mr_cut_add sp 1116 164 128 (by decide), mr_cut_add sp 1280 48 80 (by decide)]
    rw [hm1116]
    wp_done
  · intro sm hpcm hrunm hfm hsymm hLm hReg hmm
    rcases hReg with ⟨hx0m, hx1m, hx8m, hlrm, hx19m, hx20m, hx21m, hx22m, hx23m, hw24m,
      hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
    let stArg : VecArg := ⟨sp + 232#64, trG.pq.cap, trG.pq.ptr, tr.pqrState⟩
    let msgArg : VecArg := ⟨x.msgA, x.msgG.pqCap, x.msgG.pqPtr, x.msg.pqRatchet⟩
    rw [trAt_split_pq, signalMessageAt_split_pq,
      stackAt_sub sp tryDecryptSubStack spqrRecvStack] at hmm
    have hpre_callQF : sm.mem ⊨ (spqrRecvSpecQF Q Pstk F A S img).pre (stArg, msgArg, sp + 1280#64) sm ∗
        ((trRestAt A sp trG tr ∗
          signalMessageRestAt A x.msgG x.msgA x.msg ∗
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
          tapeAfter ctl x.cur x.rest draws ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - spqrRecvStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ R) := by
      dsimp only [spqrRecvSpecQF, spqrRecvSpec, Spec.inImage, VecArg.at, stArg, msgArg]
      rw [hspm]
      simp only [sepConj_assoc]
      rw [satisfies_pure_sepConj]
      refine ⟨⟨by rw [hpqr_eq]; exact hQ, hmsg_len, hstk⟩, ?_⟩
      rw [sepConj_pure_left_comm, satisfies_pure_sepConj]
      refine ⟨⟨hfm, hsymm⟩, ?_⟩
      rw [sepConj_pure_left_comm, satisfies_pure_sepConj]
      refine ⟨⟨hx0m, hx1m, hx8m⟩, ?_⟩
      simp only [sepConj_assoc] at hmm ⊢
      arm64_sep_close
    cases hrecv : S.recv tr.pqrState x.msg.pqRatchet with
    | ok pair =>
      clear hentry_eq
      rcases pair with ⟨newPqrState, pqrKey⟩
      refine steps_call hrecv_call (x := (stArg, msgArg, sp + 1280#64))
        hpcm hrunm hsp_alm hlrm hfm hsymm hLm hpre_callQF
        (fun sf hpan hpost => ⟨hpan, onPanic_of_spqrRecv (st := stArg) (msg := msgArg)
          (ret := sp + 1280#64) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hff1 hsymf1 hLf1 hpost1
      dsimp only [spqrRecvSpecQF, spqrRecvSpec, Spec.inImage, VecArg.at, stArg, msgArg] at hpost1
      rw [hspm] at hspf1 hpost1
      have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      simp only [sepConj_assoc] at hpost1
      rw [sepConj_pure_left_comm, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt] at hpost1
      unfold vecU8 at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨newPqrCap, newPqrPtr, hpost1⟩
      have hpost1' : sf1.mem ⊨
          vecU8At A (sp + 1280#64) newPqrCap newPqrPtr newPqrState ∗
          (spqrRecvKeyAt A (sp + 1304#64) pqrKey ∗
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
           tapeAfter ctl x.cur x.rest draws ∗
           logOff img ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ (F ∗ R) := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 24#64 = sp + 1304#64 by rw [BitVec.add_assoc]; rfl] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      unfold vecU8At vecHeader at hpost1'
      simp only [sepConj_assoc] at hpost1'
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1'
      rcases hpost1' with ⟨⟨hnp1, hnp2, hnp3⟩, hpost1'⟩
      have hcap_not_m1 : (newPqrCap + 1#64 == 0#64) = false := cap_add_one_ne_zero hnp2
      simp only [← sepConj_assoc] at hpost1'
      rw [sepConj_assoc _ F R] at hpost1'
      refine s5_out_add_np hnpF ?_
      unfold DeriveKeysState
      refine steps_done_of_sepWP_midMeta (s0 := s0)
        (Rest := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64 ∧
          sf.readReg64 .x21 = x.ss ∧
          sf.readReg64 .x22 = x.msgA ∧
          sf.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64 ∧
          (sf.readReg64 .x24).setWidth 32 = 1#32 ∧
          sf.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64 ∧
          sf.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64 ∧
          sf.readReg64 .x28 = (s0.sp - 1504#64) + 0x500#64 ∧
          ∃ (seedCap seedPtr newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
            sf.readReg64 .x8 = newPqrCap ∧
            msgW.setWidth 8 = msgTypeByte x.msgType ∧
            mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
            (sf.mem ⊨
              sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trAt A ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
              (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
                (seedPtr ↦ₛ mkg.seed) ∗
                memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
              vecU8At A ((s0.sp - 1504#64) + 0x500#64) newPqrCap newPqrPtr newPqrState ∗
              spqrRecvKeyAt A ((s0.sp - 1504#64) + 0x518#64) pqrKey ∗
              memRegion x.ret 48 ∗
              memRegion (s0.sp - 1504#64) 0x10 ∗
              (((s0.sp - 1504#64) + 0x10#64) ↦₆₄ seedPtr) ∗
              memRegion ((s0.sp - 1504#64) + 0x18#64) 4 ∗
              (((s0.sp - 1504#64) + 0x1c#64) ↦₃₂ msgW) ∗
              (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
              (((s0.sp - 1504#64) + 0x28#64) ↦₆₄ seedCap) ∗
              (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
              memRegion ((s0.sp - 1504#64) + 0x140#64) 0x310 ∗
              (((s0.sp - 1504#64) + 0x450#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
              (((s0.sp - 1504#64) + 0x458#64) ↦₃₂ mkg.counter) ∗
              memRegion ((s0.sp - 1504#64) + 0x45c#64) 0xa4 ∗
              memRegion ((s0.sp - 1504#64) + 0x530#64) 0x50 ∗
              tryDecryptCommonHeap A ctl img x draws s0 ∗ (F ∗ R)))
        hpost1' hLf1 hff1 hsymf1 ?_
      unfold segDeriveKeysPC tryDecryptMidMetaCore tryDecryptCommonHeap
      rw [hentry, show (0x5dc#64 : BitVec 64) = 1500#64 by rfl]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]
      clear hsp29_eq
      rw [hsp_def]
      dsimp only [vecU8At, vecHeader]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps
      wp_done
    | error sd =>
      refine steps_call hrecv_call (x := (stArg, msgArg, sp + 1280#64))
        hpcm hrunm hsp_alm hlrm hfm hsymm hLm hpre_callQF
        (fun sf hpan hpost => ⟨hpan, onPanic_of_spqrRecv (st := stArg) (msg := msgArg)
          (ret := sp + 1280#64) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hff1 hsymf1 hLf1 hpost1
      dsimp only [spqrRecvSpecQF, spqrRecvSpec, Spec.inImage, VecArg.at, stArg, msgArg] at hpost1
      rw [hspm] at hspf1 hpost1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      simp only [sepConj_assoc] at hpost1
      rw [sepConj_pure_left_comm, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt, errTag] at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨d, hpost1⟩
      simp only [sepConj_assoc] at hpost1
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        sepConj_pure_left_comm, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hd_iff, hpost1⟩
      have hpost1' : sf1.mem ⊨
          (((sp + 1288#64) ↦₈ d) ∗
           memRegion (sp + 1289#64) 7 ∗
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
           tapeAfter ctl x.cur x.rest draws ∗
           logOff img ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ (F ∗ R) := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 8#64 = sp + 1288#64 by rw [BitVec.add_assoc]; rfl,
          show (sp + 1280#64) + 9#64 = sp + 1289#64 by rw [BitVec.add_assoc]; rfl,
          mr_cut sp 1289 7 32 39 1296#64] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      rw [show sp + 1289#64 = (sp + 1288#64) + 1#64 by rw [BitVec.add_assoc]; rfl] at hpost1'
      cases sd with
      | true =>
        have hd0 : d = 0#8 := hd_iff.mpr rfl
        subst hd0
        obtain ⟨s', hsteps', herr | ⟨hpan, hqp⟩⟩ :=
          KeyDeriveCallees.pqRecv_recv_err_true img C A ctl S ext hloads x trG tr st1 mkg draws (F ∗ R) s0
            hsp0_al' hseed1 hseed2 hentry hentry_eq hfmt_call hdealloc_call hsp_def
            sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
            htrace1 hvregs_1 hff1 hsymf1 hLf1 hpost1'
        · exact ⟨s', hsteps', Or.inl ⟨herr, hnpF⟩⟩
        · exact ⟨s', hsteps', Or.inr ⟨hpan, onPanic_drop_frame hqp⟩⟩
      | false =>
        have hd_ne : d ≠ 0#8 := fun h => Bool.noConfusion (hd_iff.mp h)
        obtain ⟨s', hsteps', herr | ⟨hpan, hqp⟩⟩ :=
          KeyDeriveCallees.pqRecv_recv_err_false img C A ctl S ext x trG tr st1 mkg draws (F ∗ R) s0
            hmsgW hsp0_al' hseed1 hseed2 hentry hentry_eq hfmt_call hdealloc_call hsp_def hd_ne
            sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
            htrace1 hvregs_1 hff1 hsymf1 hLf1 hpost1'
        · exact ⟨s', hsteps', Or.inl ⟨herr, hnpF⟩⟩
        · exact ⟨s', hsteps', Or.inr ⟨hpan, onPanic_drop_frame hqp⟩⟩

/-- `Q`-restricted Segment S5 contract on `tripleRatchetProgAtExt img.base ext`. -/
def S5SpecExtQ (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
    ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes)) →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
      (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      tr.pqrState = x.st.pqRatchetState →
      PqRecvState A ctl img x trG tr st1 mkg draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((ErrTailState A ctl img x trG tr st1 e draws R s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

theorem pqRecv_ok_extQ {Q : List (BitVec 8) → Prop} (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel) (ext : String → Option (State → State)) :
    S5SpecExtQ Q img C A ctl uuidTryParse S ext := by
  intro hloads hS hrecvOk x trG tr st1 mkg draws R s0 s hQ hpqr_eq h5 hL
  have h5' : PqRecvState A ctl img x trG tr st1 mkg draws (emp ∗ R) s0 s := by
    rwa [emp_sepConj]
  have h := pqRecv_ok_extQF (Q := Q) (Pstk := fun _ => True) (F := emp) img C A ctl S ext
    hloads hS (subroutine_ok_spqrRecvSpecQF_emp hrecvOk) x trG tr st1 mkg draws R s0 s
    hQ hpqr_eq trivial h5' hL
  simpa only [emp_sepConj] using h

/-- Unrestricted Segment S5 verification on `tripleRatchetProgAtExt`. -/
theorem pqRecv_ok_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hrecv : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName) (spqrRecvSpec A S img)) :
    S5SpecExt img C A ctl uuidTryParse S ext :=
  fun hloads hS x trG tr st1 mkg draws R s0 s hpqr_eq h5 hL =>
    pqRecv_ok_extQ (Q := fun _ => True) img C A ctl S ext hloads hS
      (Spec.subroutine_ok_restrictPre _ hrecv) x trG tr st1 mkg draws R s0 s trivial hpqr_eq h5 hL

theorem pqRecv_okQF {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F : SepProp}
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) :
    PqRecvSpecQF Q Pstk F img C A ctl uuidTryParse S abs := by
  intro hloads hS hrecvOk x trG tr st1 mkg draws R s0 s hQ hpqr_eq hstk h5 hL
  have hrecv : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr spqrRecvName)
      (spqrRecvSpecQF Q Pstk F A S img) := by
    have h := hrecvOk
    unfold SpqrRecvOkQF at h
    rwa [tripleRatchetProg_eq_tripleRatchetProgAt hloads,
      entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) hloads] at h
  exact pqRecv_ok_extQF img C A ctl S (tripleRatchetExterns C ctl abs) hloads
    (.of_tripleRatchetProgAt' hS) hrecv x trG tr st1 mkg draws R s0 s hQ hpqr_eq hstk h5 hL

theorem pqRecv_ok {Q : List (BitVec 8) → Prop} (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel) (abs : String → Option (State → State)) :
    PqRecvSpec Q img C A ctl uuidTryParse S abs := by
  intro hloads hS hrecvOk x trG tr st1 mkg draws R s0 s hQ hpqr_eq h5 hL
  have h5' : PqRecvState A ctl img x trG tr st1 mkg draws (emp ∗ R) s0 s := by
    rwa [emp_sepConj]
  have h := pqRecv_okQF (Q := Q) (Pstk := fun _ => True) (F := emp) img C A ctl S abs
    hloads hS (spqrRecvOkQF_of_okQ hrecvOk) x trG tr st1 mkg draws R s0 s
    hQ hpqr_eq trivial h5' hL
  simpa only [emp_sepConj] using h

theorem pqRecv_ok_x_of_spqr (img : Obj.Image) (C : Crypto)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hspqr : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
      (spqrRecvSpec A S img)) :
    S5SpecX img C encFn decFn A ctl uuidTryParse S ext := by
  have hspqr' : KeyDeriveCallees.SpqrRecvContractX img A S ext := by
    unfold KeyDeriveCallees.SpqrRecvContractX
    exact hspqr
  clear hspqr
  intro hloads hS x trG tr st1 mkg draws R s0 s hpqr_eq h5 hL
  rcases h5 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25,
    seedCap, seedPtr, msgW, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfrozen, hsym, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 :=
    ⟨hseed1, hseed2, hseed3⟩
  have hentry := entryOf_eq_tripleRatchetProgAtExt (ext := ext) hloads tryDecryptName
  change tryDecryptEntry img = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName at hentry
  unfold segPqRecvPC at hpc
  rw [show (0x5b8#64 : BitVec 64) = 1464#64 by rfl] at hpc
  rw [hentry] at hpc
  have hentry_eq := (KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq img.base ext).symm
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName = entry
  have hrecv_call := KeyDeriveCallees.spqrRecv_ok_at_entry_of_spqr hspqr' hentry_eq
  have hfmt_call := KeyDeriveCallees.formatInner_ok_at_entry_ext_x hS hentry_eq
  have hdealloc_call := KeyDeriveCallees.dealloc_ok_at_entry_ext_x hS.toAllocContractsX hentry_eq
  decrypt_fetches_at_ext hentry_eq 1464 36
  examples_hide_fetches
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29
  clear hsp29_eq
  unfold tryDecryptCommonHeap at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx29 hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  simp only [← sepConj_assoc] at hmem
  suffices ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        (DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
          S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)
      | .error sd =>
        let e := if sd = true then .invalidState else .invalidMessage x.msgType .pqRatchet
        (ErrTailState A ctl img x trG tr st1 e draws R s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 s' ∗ R) by
    cases hrecv_eq : S.recv tr.pqrState x.msg.pqRatchet with
    | error sd =>
      rw [hrecv_eq] at this
      exact this
    | ok pair =>
      rcases pair with ⟨newPqrState, pqrKey⟩
      rw [hrecv_eq] at this
      exact this
  refine steps_of_sepWP hmem hL hfrozen hsym
    (mid := entry + bv% (ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
    (RegMid := fun sm =>
      sm.readReg64 .x0 = sp + 232#64 ∧
      sm.readReg64 .x1 = x.msgA ∧
      sm.readReg64 .x8 = sp + 1280#64 ∧
      sm.readReg64 .lr = entry + bv% (1488) ∧
      sm.readReg64 .x19 = x.ret ∧
      sm.readReg64 .x20 = sp + 320#64 ∧
      sm.readReg64 .x21 = x.ss ∧
      sm.readReg64 .x22 = x.msgA ∧
      sm.readReg64 .x23 = sp + 1280#64 ∧
      (sm.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm.readReg64 .x25 = sp + 400#64 ∧
      sm.readReg64 .x27 = sp + 56#64 ∧
      sm.readReg64 .x28 = sp + 1280#64 ∧
      sm.readReg64 .fp = sp + 1408#64 ∧
      sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    (P_mid :=
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
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₆₄ seedCap) ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 784 ∗
      ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 1116#64) 164 ∗
      memRegion (sp + 1280#64) 48 ∗
      memRegion (sp + 1328#64) 80 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      tapeAfter ctl x.cur x.rest draws ∗
      logOff img ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool)
    ?_ ?_
  · wp_steps
    have hm1116 : memRegion (sp + 1116#64) 292 =
        memRegion (sp + 1116#64) 164 ∗ (memRegion (sp + 1280#64) 48 ∗ memRegion (sp + 1328#64) 80) := by
      rw [mr_cut_add sp 1116 164 128 (by decide), mr_cut_add sp 1280 48 80 (by decide)]
    rw [hm1116]
    wp_done
  · intro sm hpcm hrunm hfm hsymm hLm hReg hmm
    rcases hReg with ⟨hx0m, hx1m, hx8m, hlrm, hx19m, hx20m, hx21m, hx22m, hx23m, hw24m,
      hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
    let stArg : VecArg := ⟨sp + 232#64, trG.pq.cap, trG.pq.ptr, tr.pqrState⟩
    let msgArg : VecArg := ⟨x.msgA, x.msgG.pqCap, x.msgG.pqPtr, x.msg.pqRatchet⟩
    have hpre_call : sm.mem ⊨ (spqrRecvSpec A S img).pre (stArg, msgArg, sp + 1280#64) sm ∗
        ((trRestAt A sp trG tr ∗
          signalMessageRestAt A x.msgG x.msgA x.msg ∗
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
          tapeAfter ctl x.cur x.rest draws ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - spqrRecvStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ R) := by
      dsimp only [spqrRecvSpec, Spec.inImage, VecArg.at, stArg, msgArg]
      rw [hspm]
      rw [trAt_split_pq, signalMessageAt_split_pq,
        stackAt_sub sp tryDecryptSubStack spqrRecvStack] at hmm
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
      refine ⟨⟨hfm, hsymm⟩, ⟨hx0m, hx1m, hx8m⟩, ?_⟩
      simp only [sepConj_assoc] at hmm ⊢
      arm64_sep_close
    cases hrecv : S.recv tr.pqrState x.msg.pqRatchet with
    | ok pair =>
      clear hentry_eq
      rcases pair with ⟨newPqrState, pqrKey⟩
      refine steps_call hrecv_call (x := (stArg, msgArg, sp + 1280#64))
        hpcm hrunm hsp_alm hlrm hfm hsymm hLm hpre_call
        (fun sf hpan hpost => ⟨hpan, onPanic_of_spqrRecv_fn htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hff1 hsymf1 hLf1 hpost1
      dsimp only [Spec.restrictPre, spqrRecvSpec, Spec.inImage, VecArg.at, stArg, msgArg] at hpost1
      rw [hspm] at hspf1 hpost1
      have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt] at hpost1
      unfold vecU8 at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨newPqrCap, newPqrPtr, hpost1⟩
      have hpost1' : sf1.mem ⊨
          vecU8At A (sp + 1280#64) newPqrCap newPqrPtr newPqrState ∗
          (spqrRecvKeyAt A (sp + 1304#64) pqrKey ∗
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
           tapeAfter ctl x.cur x.rest draws ∗
           logOff img ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 24#64 = sp + 1304#64 by rw [BitVec.add_assoc]; rfl] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      unfold vecU8At vecHeader at hpost1'
      simp only [sepConj_assoc] at hpost1'
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1'
      rcases hpost1' with ⟨⟨hnp1, hnp2, hnp3⟩, hpost1'⟩
      have hcap_not_m1 : (newPqrCap + 1#64 == 0#64) = false := cap_add_one_ne_zero hnp2
      simp only [← sepConj_assoc] at hpost1'
      refine s5_out_add_np hnpF ?_
      unfold DeriveKeysState
      refine steps_done_of_sepWP_midMeta (s0 := s0)
        (Rest := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64 ∧
          sf.readReg64 .x21 = x.ss ∧
          sf.readReg64 .x22 = x.msgA ∧
          sf.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64 ∧
          (sf.readReg64 .x24).setWidth 32 = 1#32 ∧
          sf.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64 ∧
          sf.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64 ∧
          sf.readReg64 .x28 = (s0.sp - 1504#64) + 0x500#64 ∧
          ∃ (seedCap seedPtr newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
            sf.readReg64 .x8 = newPqrCap ∧
            msgW.setWidth 8 = msgTypeByte x.msgType ∧
            mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
            (sf.mem ⊨
              sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trAt A ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
              (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
                (seedPtr ↦ₛ mkg.seed) ∗
                memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
              vecU8At A ((s0.sp - 1504#64) + 0x500#64) newPqrCap newPqrPtr newPqrState ∗
              spqrRecvKeyAt A ((s0.sp - 1504#64) + 0x518#64) pqrKey ∗
              memRegion x.ret 48 ∗
              memRegion (s0.sp - 1504#64) 0x10 ∗
              (((s0.sp - 1504#64) + 0x10#64) ↦₆₄ seedPtr) ∗
              memRegion ((s0.sp - 1504#64) + 0x18#64) 4 ∗
              (((s0.sp - 1504#64) + 0x1c#64) ↦₃₂ msgW) ∗
              (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
              (((s0.sp - 1504#64) + 0x28#64) ↦₆₄ seedCap) ∗
              (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
              memRegion ((s0.sp - 1504#64) + 0x140#64) 0x310 ∗
              (((s0.sp - 1504#64) + 0x450#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
              (((s0.sp - 1504#64) + 0x458#64) ↦₃₂ mkg.counter) ∗
              memRegion ((s0.sp - 1504#64) + 0x45c#64) 0xa4 ∗
              memRegion ((s0.sp - 1504#64) + 0x530#64) 0x50 ∗
              tryDecryptCommonHeap A ctl img x draws s0 ∗ R))
        hpost1' hLf1 hff1 hsymf1 ?_
      unfold segDeriveKeysPC tryDecryptMidMetaCore tryDecryptCommonHeap
      rw [hentry, show (0x5dc#64 : BitVec 64) = 1500#64 by rfl]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]
      clear hsp29_eq
      rw [hsp_def]
      dsimp only [vecU8At, vecHeader]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps
      wp_done
    | error sd =>
      refine steps_call hrecv_call (x := (stArg, msgArg, sp + 1280#64))
        hpcm hrunm hsp_alm hlrm hfm hsymm hLm hpre_call
        (fun sf hpan hpost => ⟨hpan, onPanic_of_spqrRecv_fn htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hff1 hsymf1 hLf1 hpost1
      dsimp only [Spec.restrictPre, spqrRecvSpec, Spec.inImage, VecArg.at, stArg, msgArg] at hpost1
      rw [hspm] at hspf1 hpost1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt, errTag] at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨d, hpost1⟩
      simp only [sepConj_assoc] at hpost1
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hd_iff, hpost1⟩
      have hpost1' : sf1.mem ⊨
          (((sp + 1288#64) ↦₈ d) ∗
           memRegion (sp + 1289#64) 7 ∗
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
           tapeAfter ctl x.cur x.rest draws ∗
           logOff img ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 8#64 = sp + 1288#64 by rw [BitVec.add_assoc]; rfl,
          show (sp + 1280#64) + 9#64 = sp + 1289#64 by rw [BitVec.add_assoc]; rfl,
          mr_cut sp 1289 7 32 39 1296#64] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      rw [show sp + 1289#64 = (sp + 1288#64) + 1#64 by rw [BitVec.add_assoc]; rfl] at hpost1'
      cases sd with
      | true =>
        have hd0 : d = 0#8 := hd_iff.mpr rfl
        subst hd0
        exact s5_out_add_np hnpF (KeyDeriveCallees.pqRecv_recv_err_true_x img C decFn A ctl S ext hloads x trG tr st1 mkg draws R s0
          hsp0_al' hseed1 hseed2 hentry hentry_eq hfmt_call hdealloc_call hsp_def
          sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
          htrace1 hvregs_1 hff1 hsymf1 hLf1 hpost1')
      | false =>
        have hd_ne : d ≠ 0#8 := fun h => Bool.noConfusion (hd_iff.mp h)
        exact s5_out_add_np hnpF (KeyDeriveCallees.pqRecv_recv_err_false_x img C decFn A ctl S ext x trG tr st1 mkg draws R s0
          hmsgW hsp0_al' hseed1 hseed2 hentry hentry_eq hfmt_call hdealloc_call hsp_def hd_ne
          sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
          htrace1 hvregs_1 hff1 hsymf1 hLf1 hpost1')

/-! ## Relocatable `[LibsignalPlacement]` Segment S5 (`pqRecv_159_placed_ok`, `pqRecv_549_placed_ok`) -/

namespace KeyDeriveCallees

abbrev lsFormatInnerSym : String :=
  "_RNvNvNtCs69KKACWg7bl_5alloc3fmt6format12format_inner"

abbrev lsTryDecryptRoSym : String :=
  "libsignal_session:.rodata..Lanon.85"

abbrev lsTryDecryptCoinsRoSym : String :=
  "libsignal_cli_ratchet:.rodata..Lanon.85"

theorem lsroCheck_tryDecryptRoSym :
    lsroCheck lsTryDecryptRoSym (utf8 "decrypt") = true := by
  decide +kernel

theorem lsroCheck_tryDecryptCoinsRoSym :
    lsroCheck lsTryDecryptCoinsRoSym (utf8 "decrypt") = true := by
  decide +kernel

theorem pqRecv_dealloc_tail_159_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {sp seedCap seedPtr : BitVec 64}
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hdealloc_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (e : SignalProtocolError) (st2 : State)
    (hpc2 : st2.pc = (blkPl_131).base + 2500#64)
    (hrun2 : st2.status = .Running)
    (hsp2 : st2.sp = sp)
    (hsp_al2 : st2.spAligned = true)
    (hfp2 : st2.readReg64 .fp = sp + 1408#64)
    (htr2 : st2.trace = s0.trace)
    (hvregs2 : calleeSavedVRegs st2 = calleeSavedVRegs s0)
    (hcl2 : LibsignalCodeRoLoaded lsmpl st2.mem)
    (hL2 : ((blkPC_131).rebase (blkPl_131).base H).CodeLoaded st2.mem)
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
       tapeAfter ctl x.cur x.rest draws ∗
       logOff tryDecryptPlacedImg ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps ((blkPC_131).rebase (blkPl_131).base H) st2 s' ∧
      (ErrTailStatePlaced (blkPl_131).base A ctl x trG tr st1 e draws R s0 s' ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)) := by
  have hsp_al2' : (st2.sp &&& 15#64 == 0#64) = true := hsp_al2
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp2]; exact hsp_al2
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
          tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ R))
      hm2 hL2 hcl2 ?_
    unfold errTailPC_at tryDecryptMidMetaCore tryDecryptCommonHeap
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
        sm3.readReg64 .lr = (blkPl_131).base + 2520#64 ∧
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
        tapeAfter ctl x.cur x.rest draws ∗
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
            tapeAfter ctl x.cur x.rest draws ∗
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
           tapeAfter ctl x.cur x.rest draws ∗
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
            tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ R))
        hpost3' hLf3 hclf3 ?_
      unfold errTailPC_at tryDecryptMidMetaCore tryDecryptCommonHeap
      rw [show (0x30c#64 : BitVec 64) = 780#64 by rfl]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]; clear hsp29_eq
      rw [hsp_def]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps
      wp_done

theorem pqRecv_recv_err_true_159_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {sp seedCap seedPtr : BitVec 64} {msgW : BitVec 32}
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hfmt_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (sf1 : State)
    (hpcf1 : sf1.pc = (blkPl_131).base + 1488#64)
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
    (hLf1 : ((blkPC_131).rebase (blkPl_131).base H).CodeLoaded sf1.mem)
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
       tapeAfter ctl x.cur x.rest draws ∗
       logOff tryDecryptPlacedImg ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps ((blkPC_131).rebase (blkPl_131).base H) sf1 s' ∧
      (ErrTailStatePlaced (blkPl_131).base A ctl x trG tr st1 .invalidState draws R s0 s' ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)) := by
  have hdealloc_tail := KeyDeriveCallees.pqRecv_dealloc_tail_159_placed C A ctl S H x trG tr st1 mkg draws R s0
    (seedPtr := seedPtr) hsp0_al' hseed1 hseed2 hdealloc_call hsp_def .invalidState
  have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hspf1]; exact hsp_alf1
  simp only [← sepConj_assoc] at hpost1'
  refine steps_of_sepWP_placed hpost1' hLf1 hclf1
    (mid := lsρ lsFormatInnerSym)
    (RegMid := fun sm2 =>
      sm2.readReg64 .x8 = sp + 408#64 ∧
      sm2.readReg64 .lr = (blkPl_131).base + 2452#64 ∧
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
      tapeAfter ctl x.cur x.rest draws ∗
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
          tapeAfter ctl x.cur x.rest draws ∗
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
      (fun sf hpan hpost => ⟨hpan, onPanic_of_formatInner_placed htr_2 hpost⟩) ?_
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
         tapeAfter ctl x.cur x.rest draws ∗
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
    have hpost2_ro := lsro_intro_chk hclf2.2 lsroCheck_tryDecryptRoSym hpost2'
    simp only [← sepConj_assoc] at hpost2_ro
    refine steps_of_sepWP_placed hpost2_ro hLf2 hclf2
      (mid := (blkPl_131).base + 2500#64)
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
        tapeAfter ctl x.cur x.rest draws ∗
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
      exact hdealloc_tail st2 hpc2 hrun2 hsp_2 hsp_al2 hfp_2 htr_2 hvregs_2 hcl2 hL2
        hx19_2 hx20_2 hx26_2 hm2

theorem pqRecv_recv_err_false_159_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {sp seedCap seedPtr : BitVec 64} {msgW : BitVec 32} {d : BitVec 8}
    (hmsgW : msgW.setWidth 8 = msgTypeByte x.msgType)
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hfmt_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hd_ne : d ≠ 0#8)
    (sf1 : State)
    (hpcf1 : sf1.pc = (blkPl_131).base + 1488#64)
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
    (hLf1 : ((blkPC_131).rebase (blkPl_131).base H).CodeLoaded sf1.mem)
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
       tapeAfter ctl x.cur x.rest draws ∗
       logOff tryDecryptPlacedImg ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps ((blkPC_131).rebase (blkPl_131).base H) sf1 s' ∧
      (ErrTailStatePlaced (blkPl_131).base A ctl x trG tr st1 (.invalidMessage x.msgType .pqRatchet) draws R s0 s' ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)) := by
  have hdealloc_tail := KeyDeriveCallees.pqRecv_dealloc_tail_159_placed C A ctl S H x trG tr st1 mkg draws R s0
    (seedPtr := seedPtr) hsp0_al' hseed1 hseed2 hdealloc_call hsp_def (.invalidMessage x.msgType .pqRatchet)
  have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hspf1]; exact hsp_alf1
  have hd_cbz1 : (BitVec.setWidth 32 d == 0#32) = false := byte_ne_zero_cbz32 hd_ne
  have hd_cbz2 : (BitVec.setWidth 32 (BitVec.setWidth 64 d) == 0#32) = false :=
    byte_ne_zero_cbz64_32 hd_ne
  simp only [← sepConj_assoc] at hpost1'
  refine steps_of_sepWP_placed hpost1' hLf1 hclf1
    (mid := lsρ lsFormatInnerSym)
    (RegMid := fun sm2 =>
      sm2.readReg64 .x8 = sp + 408#64 ∧
      sm2.readReg64 .lr = (blkPl_131).base + 2156#64 ∧
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
      tapeAfter ctl x.cur x.rest draws ∗
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
          tapeAfter ctl x.cur x.rest draws ∗
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
      (fun sf hpan hpost => ⟨hpan, onPanic_of_formatInner_placed htr_2 hpost⟩) ?_
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
         tapeAfter ctl x.cur x.rest draws ∗
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
      (mid := (blkPl_131).base + 2500#64)
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
        tapeAfter ctl x.cur x.rest draws ∗
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
      exact hdealloc_tail st2 hpc2 hrun2 hsp_2 hsp_al2 hfp_2 htr_2 hvregs_2 hcl2 hL2
        hx19_2 hx20_2 hx26_2 hm2

end KeyDeriveCallees

def spqrRecvRawSpec [LibsignalPlacement] (A : RustAlloc) (S : SpqrModel) : Spec (VecArg × VecArg × BitVec 64) :=
  { pre := fun (st, msg, ret) s =>
      ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret⌝ ∗
        st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ logOff tryDecryptPlacedImg ∗ A.pool ∗ stackAt s.sp spqrRecvStack
    post := fun (st, msg, ret) s0 sf =>
      ⌜sf.trace = s0.trace ∧ ¬ S.recvPanics st.bytes msg.bytes⌝ ∗ st.at A ∗ msg.at A ∗
        spqrRecvResultAt A ret (S.recv st.bytes msg.bytes) ∗
        logOff tryDecryptPlacedImg ∗ A.pool ∗ stackAt s0.sp spqrRecvStack
    onPanic := fun (st, msg, _) s0 sf =>
      ⌜(allocFailedIn s0 sf ∨ S.recvPanics st.bytes msg.bytes) ∧ s0.trace <+: sf.trace⌝ ∗
        anyHeap }

theorem pqRecv_159_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (hrecv_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl (spqrRecvRawSpec A S)))
    (hfmt_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ KeyDeriveCallees.lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    S5SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S := by
  intro x trG tr st1 mkg draws R s0 s hpqr_eq h5 hL
  rcases h5 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25,
    seedCap, seedPtr, msgW, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 :=
    ⟨hseed1, hseed2, hseed3⟩
  unfold segPqRecvPC_at at hpc
  rw [show (0x5b8#64 : BitVec 64) = 1464#64 by rfl] at hpc
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29
  clear hsp29_eq
  unfold tryDecryptCommonHeap at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx29 hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  simp only [← sepConj_assoc] at hmem
  suffices ∃ s', Steps ((blkPC_131).rebase (blkPl_131).base H) s s' ∧
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        (DeriveKeysStatePlaced (blkPl_131).base A ctl x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
          S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)
      | .error sd =>
        let e := if sd = true then .invalidState else .invalidMessage x.msgType .pqRatchet
        (ErrTailStatePlaced (blkPl_131).base A ctl x trG tr st1 e draws R s0 s' ∧
          S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R) by
    cases hrecv_eq : S.recv tr.pqrState x.msg.pqRatchet with
    | error sd =>
      rw [hrecv_eq] at this
      exact this
    | ok pair =>
      rcases pair with ⟨newPqrState, pqrKey⟩
      rw [hrecv_eq] at this
      exact this
  refine steps_of_sepWP_placed hmem hL hcl
    (mid := lsmpl.base 329)
    (RegMid := fun sm =>
      sm.readReg64 .x0 = sp + 232#64 ∧
      sm.readReg64 .x1 = x.msgA ∧
      sm.readReg64 .x8 = sp + 1280#64 ∧
      sm.readReg64 .lr = (blkPl_131).base + 1488#64 ∧
      sm.readReg64 .x19 = x.ret ∧
      sm.readReg64 .x20 = sp + 320#64 ∧
      sm.readReg64 .x21 = x.ss ∧
      sm.readReg64 .x22 = x.msgA ∧
      sm.readReg64 .x23 = sp + 1280#64 ∧
      (sm.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm.readReg64 .x25 = sp + 400#64 ∧
      sm.readReg64 .x27 = sp + 56#64 ∧
      sm.readReg64 .x28 = sp + 1280#64 ∧
      sm.readReg64 .fp = sp + 1408#64 ∧
      sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    (P_mid :=
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
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₆₄ seedCap) ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 784 ∗
      ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 1116#64) 164 ∗
      memRegion (sp + 1280#64) 48 ∗
      memRegion (sp + 1328#64) 80 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      tapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool)
    ?_ ?_
  · wp_steps
    have hm1116 : memRegion (sp + 1116#64) 292 =
        memRegion (sp + 1116#64) 164 ∗ (memRegion (sp + 1280#64) 48 ∗ memRegion (sp + 1328#64) 80) := by
      rw [mr_cut_add sp 1116 164 128 (by decide), mr_cut_add sp 1280 48 80 (by decide)]
    rw [hm1116]
    wp_done
  · intro sm hpcm hrunm hclm hLm hReg hmm
    rcases hReg with ⟨hx0m, hx1m, hx8m, hlrm, hx19m, hx20m, hx21m, hx22m, hx23m, hw24m,
      hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
    let stArg : VecArg := ⟨sp + 232#64, trG.pq.cap, trG.pq.ptr, tr.pqrState⟩
    let msgArg : VecArg := ⟨x.msgA, x.msgG.pqCap, x.msgG.pqPtr, x.msg.pqRatchet⟩
    have hpre_call : sm.mem ⊨ (spqrRecvRawSpec A S).pre (stArg, msgArg, sp + 1280#64) sm ∗
        ((trRestAt A sp trG tr ∗
          signalMessageRestAt A x.msgG x.msgA x.msg ∗
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
          tapeAfter ctl x.cur x.rest draws ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - spqrRecvStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ R) := by
      dsimp only [spqrRecvRawSpec, VecArg.at, stArg, msgArg]
      rw [hspm]
      rw [trAt_split_pq, signalMessageAt_split_pq,
        stackAt_sub sp tryDecryptSubStack spqrRecvStack] at hmm
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0m, hx1m, hx8m⟩, ?_⟩
      simp only [sepConj_assoc] at hmm ⊢
      arm64_sep_close
    cases hrecv : S.recv tr.pqrState x.msg.pqRatchet with
    | ok pair =>
      rcases pair with ⟨newPqrState, pqrKey⟩
      refine steps_call_placed_cro (stArg, msgArg, sp + 1280#64) hrecv_call
        hpcm hrunm hsp_alm hlrm hclm hLm hpre_call
        (fun sf hpan hpost => ⟨hpan, onPanic_of_spqrRecv_placed (st := stArg) (msg := msgArg)
          (ret := sp + 1280#64) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hclf1 hLf1 hpost1
      dsimp only [spqrRecvRawSpec, VecArg.at, stArg, msgArg] at hpost1
      rw [hspm] at hspf1 hpost1
      have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt] at hpost1
      unfold vecU8 at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨newPqrCap, newPqrPtr, hpost1⟩
      have hpost1' : sf1.mem ⊨
          vecU8At A (sp + 1280#64) newPqrCap newPqrPtr newPqrState ∗
          (spqrRecvKeyAt A (sp + 1304#64) pqrKey ∗
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
           tapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 24#64 = sp + 1304#64 by rw [BitVec.add_assoc]; rfl] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      unfold vecU8At vecHeader at hpost1'
      simp only [sepConj_assoc] at hpost1'
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1'
      rcases hpost1' with ⟨⟨hnp1, hnp2, hnp3⟩, hpost1'⟩
      have hcap_not_m1 : (newPqrCap + 1#64 == 0#64) = false := cap_add_one_ne_zero hnp2
      simp only [← sepConj_assoc] at hpost1'
      refine s5_out_add_np hnpF ?_
      unfold DeriveKeysStatePlaced
      refine steps_done_of_sepWP_midMeta_placed (s0 := s0)
        (Rest := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64 ∧
          sf.readReg64 .x21 = x.ss ∧
          sf.readReg64 .x22 = x.msgA ∧
          sf.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64 ∧
          (sf.readReg64 .x24).setWidth 32 = 1#32 ∧
          sf.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64 ∧
          sf.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64 ∧
          sf.readReg64 .x28 = (s0.sp - 1504#64) + 0x500#64 ∧
          ∃ (seedCap seedPtr newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
            sf.readReg64 .x8 = newPqrCap ∧
            msgW.setWidth 8 = msgTypeByte x.msgType ∧
            mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
            (sf.mem ⊨
              sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trAt A ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
              (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
                (seedPtr ↦ₛ mkg.seed) ∗
                memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
              vecU8At A ((s0.sp - 1504#64) + 0x500#64) newPqrCap newPqrPtr newPqrState ∗
              spqrRecvKeyAt A ((s0.sp - 1504#64) + 0x518#64) pqrKey ∗
              memRegion x.ret 48 ∗
              memRegion (s0.sp - 1504#64) 0x10 ∗
              (((s0.sp - 1504#64) + 0x10#64) ↦₆₄ seedPtr) ∗
              memRegion ((s0.sp - 1504#64) + 0x18#64) 4 ∗
              (((s0.sp - 1504#64) + 0x1c#64) ↦₃₂ msgW) ∗
              (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
              (((s0.sp - 1504#64) + 0x28#64) ↦₆₄ seedCap) ∗
              (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
              memRegion ((s0.sp - 1504#64) + 0x140#64) 0x310 ∗
              (((s0.sp - 1504#64) + 0x450#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
              (((s0.sp - 1504#64) + 0x458#64) ↦₃₂ mkg.counter) ∗
              memRegion ((s0.sp - 1504#64) + 0x45c#64) 0xa4 ∗
              memRegion ((s0.sp - 1504#64) + 0x530#64) 0x50 ∗
              tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ R))
        hpost1' hLf1 hclf1 ?_
      unfold segDeriveKeysPC_at tryDecryptMidMetaCore tryDecryptCommonHeap
      rw [show (0x5dc#64 : BitVec 64) = 1500#64 by rfl]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]
      clear hsp29_eq
      rw [hsp_def]
      dsimp only [vecU8At, vecHeader]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps
      wp_done
    | error sd =>
      refine steps_call_placed_cro (stArg, msgArg, sp + 1280#64) hrecv_call
        hpcm hrunm hsp_alm hlrm hclm hLm hpre_call
        (fun sf hpan hpost => ⟨hpan, onPanic_of_spqrRecv_placed (st := stArg) (msg := msgArg)
          (ret := sp + 1280#64) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hclf1 hLf1 hpost1
      dsimp only [spqrRecvRawSpec, VecArg.at, stArg, msgArg] at hpost1
      rw [hspm] at hspf1 hpost1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt, errTag] at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨d, hpost1⟩
      simp only [sepConj_assoc] at hpost1
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hd_iff, hpost1⟩
      have hpost1' : sf1.mem ⊨
          (((sp + 1288#64) ↦₈ d) ∗
           memRegion (sp + 1289#64) 7 ∗
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
           tapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 8#64 = sp + 1288#64 by rw [BitVec.add_assoc]; rfl,
          show (sp + 1280#64) + 9#64 = sp + 1289#64 by rw [BitVec.add_assoc]; rfl,
          mr_cut sp 1289 7 32 39 1296#64] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      rw [show sp + 1289#64 = (sp + 1288#64) + 1#64 by rw [BitVec.add_assoc]; rfl] at hpost1'
      cases sd with
      | true =>
        have hd0 : d = 0#8 := hd_iff.mpr rfl
        subst hd0
        exact s5_out_add_np hnpF (KeyDeriveCallees.pqRecv_recv_err_true_159_placed C A ctl S H x trG tr st1 mkg draws R s0
          hsp0_al' hseed1 hseed2 hfmt_call hdealloc_call hsp_def
          sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
          htrace1 hvregs_1 hclf1 hLf1 hpost1')
      | false =>
        have hd_ne : d ≠ 0#8 := fun h => Bool.noConfusion (hd_iff.mp h)
        exact s5_out_add_np hnpF (KeyDeriveCallees.pqRecv_recv_err_false_159_placed C A ctl S H x trG tr st1 mkg draws R s0
          hmsgW hsp0_al' hseed1 hseed2 hfmt_call hdealloc_call hsp_def hd_ne
          sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
          htrace1 hvregs_1 hclf1 hLf1 hpost1')

theorem pqRecv_159_placed_ok_x [LibsignalPlacement] (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (hrecv_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl (spqrRecvRawSpec A S)))
    (hfmt_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ KeyDeriveCallees.lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    S5SeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C decFn A ctl uuidTryParse S := by
  unfold S5SeamXPlaced
  simp only [tryDecryptFnSpecPlaced_onPanic_eq]
  exact pqRecv_159_placed_ok C A ctl S H hrecv_call hfmt_call hdealloc_call

namespace KeyDeriveCallees

theorem pqRecv_dealloc_tail_549_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {sp seedCap seedPtr : BitVec 64}
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hdealloc_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
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
       tapeAfter ctl x.cur x.rest draws ∗
       logOff tryDecryptPlacedImg ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) st2 s' ∧
      (ErrTailStatePlaced (blkPl_434).base A ctl x trG tr st1 e draws R s0 s' ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)) := by
  have hsp_al2' : (st2.sp &&& 15#64 == 0#64) = true := hsp_al2
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp2]; exact hsp_al2
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
          tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ R))
      hm2 hL2 hcl2 ?_
    unfold errTailPC_at tryDecryptMidMetaCore tryDecryptCommonHeap
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
        sm3.readReg64 .lr = (blkPl_434).base + 2520#64 ∧
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
        tapeAfter ctl x.cur x.rest draws ∗
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
            tapeAfter ctl x.cur x.rest draws ∗
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
           tapeAfter ctl x.cur x.rest draws ∗
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
            tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ R))
        hpost3' hLf3 hclf3 ?_
      unfold errTailPC_at tryDecryptMidMetaCore tryDecryptCommonHeap
      rw [show (0x30c#64 : BitVec 64) = 780#64 by rfl]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]; clear hsp29_eq
      rw [hsp_def]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps
      wp_done

theorem pqRecv_recv_err_true_549_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {sp seedCap seedPtr : BitVec 64} {msgW : BitVec 32}
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hfmt_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
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
       tapeAfter ctl x.cur x.rest draws ∗
       logOff tryDecryptPlacedImg ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) sf1 s' ∧
      (ErrTailStatePlaced (blkPl_434).base A ctl x trG tr st1 .invalidState draws R s0 s' ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)) := by
  have hdealloc_tail := KeyDeriveCallees.pqRecv_dealloc_tail_549_placed C A ctl S H x trG tr st1 mkg draws R s0
    (seedPtr := seedPtr) hsp0_al' hseed1 hseed2 hdealloc_call hsp_def .invalidState
  have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hspf1]; exact hsp_alf1
  simp only [← sepConj_assoc] at hpost1'
  refine steps_of_sepWP_placed hpost1' hLf1 hclf1
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
      tapeAfter ctl x.cur x.rest draws ∗
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
          tapeAfter ctl x.cur x.rest draws ∗
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
      (fun sf hpan hpost => ⟨hpan, onPanic_of_formatInner_placed htr_2 hpost⟩) ?_
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
         tapeAfter ctl x.cur x.rest draws ∗
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
    have hpost2_ro := lsro_intro_chk hclf2.2 lsroCheck_tryDecryptCoinsRoSym hpost2'
    simp only [← sepConj_assoc] at hpost2_ro
    refine steps_of_sepWP_placed hpost2_ro hLf2 hclf2
      (mid := (blkPl_434).base + 2500#64)
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
        tapeAfter ctl x.cur x.rest draws ∗
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
      exact hdealloc_tail st2 hpc2 hrun2 hsp_2 hsp_al2 hfp_2 htr_2 hvregs_2 hcl2 hL2
        hx19_2 hx20_2 hx26_2 hm2

theorem pqRecv_recv_err_false_549_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 : State) {sp seedCap seedPtr : BitVec 64} {msgW : BitVec 32} {d : BitVec 8}
    (hmsgW : msgW.setWidth 8 = msgTypeByte x.msgType)
    (hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true)
    (hseed1 : mkg.seed.length ≤ seedCap.toNat)
    (hseed2 : seedCap.toNat < 2 ^ 63)
    (hfmt_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
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
       tapeAfter ctl x.cur x.rest draws ∗
       logOff tryDecryptPlacedImg ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) sf1 s' ∧
      (ErrTailStatePlaced (blkPl_434).base A ctl x trG tr st1 (.invalidMessage x.msgType .pqRatchet) draws R s0 s' ∨
        (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)) := by
  have hdealloc_tail := KeyDeriveCallees.pqRecv_dealloc_tail_549_placed C A ctl S H x trG tr st1 mkg draws R s0
    (seedPtr := seedPtr) hsp0_al' hseed1 hseed2 hdealloc_call hsp_def (.invalidMessage x.msgType .pqRatchet)
  have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hspf1]; exact hsp_alf1
  simp only [← sepConj_assoc] at hpost1'
  refine steps_of_sepWP_placed hpost1' hLf1 hclf1
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
      tapeAfter ctl x.cur x.rest draws ∗
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
          tapeAfter ctl x.cur x.rest draws ∗
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
      (fun sf hpan hpost => ⟨hpan, onPanic_of_formatInner_placed htr_2 hpost⟩) ?_
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
         tapeAfter ctl x.cur x.rest draws ∗
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
      (mid := (blkPl_434).base + 2500#64)
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
        tapeAfter ctl x.cur x.rest draws ∗
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
      exact hdealloc_tail st2 hpc2 hrun2 hsp_2 hsp_al2 hfp_2 htr_2 hvregs_2 hcl2 hL2
        hx19_2 hx20_2 hx26_2 hm2

end KeyDeriveCallees

theorem pqRecv_549_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (hrecv_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl (spqrRecvRawSpec A S)))
    (hfmt_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ KeyDeriveCallees.lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    S5SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl uuidTryParse S := by
  intro x trG tr st1 mkg draws R s0 s hpqr_eq h5 hL
  rcases h5 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25,
    seedCap, seedPtr, msgW, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 :=
    ⟨hseed1, hseed2, hseed3⟩
  unfold segPqRecvPC_at at hpc
  rw [show (0x5b8#64 : BitVec 64) = 1464#64 by rfl] at hpc
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29
  clear hsp29_eq
  unfold tryDecryptCommonHeap at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx29 hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  simp only [← sepConj_assoc] at hmem
  suffices ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        (DeriveKeysStatePlaced (blkPl_434).base A ctl x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
          S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)
      | .error sd =>
        let e := if sd = true then .invalidState else .invalidMessage x.msgType .pqRatchet
        (ErrTailStatePlaced (blkPl_434).base A ctl x trG tr st1 e draws R s0 s' ∧
          S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R) by
    cases hrecv_eq : S.recv tr.pqrState x.msg.pqRatchet with
    | error sd =>
      rw [hrecv_eq] at this
      exact this
    | ok pair =>
      rcases pair with ⟨newPqrState, pqrKey⟩
      rw [hrecv_eq] at this
      exact this
  refine steps_of_sepWP_placed hmem hL hcl
    (mid := lsmpl.base 329)
    (RegMid := fun sm =>
      sm.readReg64 .x0 = sp + 232#64 ∧
      sm.readReg64 .x1 = x.msgA ∧
      sm.readReg64 .x8 = sp + 1280#64 ∧
      sm.readReg64 .lr = (blkPl_434).base + 1488#64 ∧
      sm.readReg64 .x19 = x.ret ∧
      sm.readReg64 .x20 = sp + 320#64 ∧
      sm.readReg64 .x21 = x.ss ∧
      sm.readReg64 .x22 = x.msgA ∧
      sm.readReg64 .x23 = sp + 1280#64 ∧
      (sm.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm.readReg64 .x25 = sp + 400#64 ∧
      sm.readReg64 .x27 = sp + 56#64 ∧
      sm.readReg64 .x28 = sp + 1280#64 ∧
      sm.readReg64 .fp = sp + 1408#64 ∧
      sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    (P_mid :=
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
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₆₄ seedCap) ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 784 ∗
      ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 1116#64) 164 ∗
      memRegion (sp + 1280#64) 48 ∗
      memRegion (sp + 1328#64) 80 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      tapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool)
    ?_ ?_
  · wp_steps
    have hm1116 : memRegion (sp + 1116#64) 292 =
        memRegion (sp + 1116#64) 164 ∗ (memRegion (sp + 1280#64) 48 ∗ memRegion (sp + 1328#64) 80) := by
      rw [mr_cut_add sp 1116 164 128 (by decide), mr_cut_add sp 1280 48 80 (by decide)]
    rw [hm1116]
    wp_done
  · intro sm hpcm hrunm hclm hLm hReg hmm
    rcases hReg with ⟨hx0m, hx1m, hx8m, hlrm, hx19m, hx20m, hx21m, hx22m, hx23m, hw24m,
      hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
    let stArg : VecArg := ⟨sp + 232#64, trG.pq.cap, trG.pq.ptr, tr.pqrState⟩
    let msgArg : VecArg := ⟨x.msgA, x.msgG.pqCap, x.msgG.pqPtr, x.msg.pqRatchet⟩
    have hpre_call : sm.mem ⊨ (spqrRecvRawSpec A S).pre (stArg, msgArg, sp + 1280#64) sm ∗
        ((trRestAt A sp trG tr ∗
          signalMessageRestAt A x.msgG x.msgA x.msg ∗
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
          tapeAfter ctl x.cur x.rest draws ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - spqrRecvStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ R) := by
      dsimp only [spqrRecvRawSpec, VecArg.at, stArg, msgArg]
      rw [hspm]
      rw [trAt_split_pq, signalMessageAt_split_pq,
        stackAt_sub sp tryDecryptSubStack spqrRecvStack] at hmm
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0m, hx1m, hx8m⟩, ?_⟩
      simp only [sepConj_assoc] at hmm ⊢
      arm64_sep_close
    cases hrecv : S.recv tr.pqrState x.msg.pqRatchet with
    | ok pair =>
      rcases pair with ⟨newPqrState, pqrKey⟩
      refine steps_call_placed_cro (stArg, msgArg, sp + 1280#64) hrecv_call
        hpcm hrunm hsp_alm hlrm hclm hLm hpre_call
        (fun sf hpan hpost => ⟨hpan, onPanic_of_spqrRecv_placed (st := stArg) (msg := msgArg)
          (ret := sp + 1280#64) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hclf1 hLf1 hpost1
      dsimp only [spqrRecvRawSpec, VecArg.at, stArg, msgArg] at hpost1
      rw [hspm] at hspf1 hpost1
      have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt] at hpost1
      unfold vecU8 at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨newPqrCap, newPqrPtr, hpost1⟩
      have hpost1' : sf1.mem ⊨
          vecU8At A (sp + 1280#64) newPqrCap newPqrPtr newPqrState ∗
          (spqrRecvKeyAt A (sp + 1304#64) pqrKey ∗
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
           tapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 24#64 = sp + 1304#64 by rw [BitVec.add_assoc]; rfl] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      unfold vecU8At vecHeader at hpost1'
      simp only [sepConj_assoc] at hpost1'
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1'
      rcases hpost1' with ⟨⟨hnp1, hnp2, hnp3⟩, hpost1'⟩
      have hcap_not_m1 : (newPqrCap + 1#64 == 0#64) = false := cap_add_one_ne_zero hnp2
      simp only [← sepConj_assoc] at hpost1'
      refine s5_out_add_np hnpF ?_
      unfold DeriveKeysStatePlaced
      refine steps_done_of_sepWP_midMeta_placed (s0 := s0)
        (Rest := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64 ∧
          sf.readReg64 .x21 = x.ss ∧
          sf.readReg64 .x22 = x.msgA ∧
          sf.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64 ∧
          (sf.readReg64 .x24).setWidth 32 = 1#32 ∧
          sf.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64 ∧
          sf.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64 ∧
          sf.readReg64 .x28 = (s0.sp - 1504#64) + 0x500#64 ∧
          ∃ (seedCap seedPtr newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
            sf.readReg64 .x8 = newPqrCap ∧
            msgW.setWidth 8 = msgTypeByte x.msgType ∧
            mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
            (sf.mem ⊨
              sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trAt A ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
              (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
                (seedPtr ↦ₛ mkg.seed) ∗
                memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
              vecU8At A ((s0.sp - 1504#64) + 0x500#64) newPqrCap newPqrPtr newPqrState ∗
              spqrRecvKeyAt A ((s0.sp - 1504#64) + 0x518#64) pqrKey ∗
              memRegion x.ret 48 ∗
              memRegion (s0.sp - 1504#64) 0x10 ∗
              (((s0.sp - 1504#64) + 0x10#64) ↦₆₄ seedPtr) ∗
              memRegion ((s0.sp - 1504#64) + 0x18#64) 4 ∗
              (((s0.sp - 1504#64) + 0x1c#64) ↦₃₂ msgW) ∗
              (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
              (((s0.sp - 1504#64) + 0x28#64) ↦₆₄ seedCap) ∗
              (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
              memRegion ((s0.sp - 1504#64) + 0x140#64) 0x310 ∗
              (((s0.sp - 1504#64) + 0x450#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
              (((s0.sp - 1504#64) + 0x458#64) ↦₃₂ mkg.counter) ∗
              memRegion ((s0.sp - 1504#64) + 0x45c#64) 0xa4 ∗
              memRegion ((s0.sp - 1504#64) + 0x530#64) 0x50 ∗
              tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ R))
        hpost1' hLf1 hclf1 ?_
      unfold segDeriveKeysPC_at tryDecryptMidMetaCore tryDecryptCommonHeap
      rw [show (0x5dc#64 : BitVec 64) = 1500#64 by rfl]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]
      clear hsp29_eq
      rw [hsp_def]
      dsimp only [vecU8At, vecHeader]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps
      wp_done
    | error sd =>
      refine steps_call_placed_cro (stArg, msgArg, sp + 1280#64) hrecv_call
        hpcm hrunm hsp_alm hlrm hclm hLm hpre_call
        (fun sf hpan hpost => ⟨hpan, onPanic_of_spqrRecv_placed (st := stArg) (msg := msgArg)
          (ret := sp + 1280#64) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hclf1 hLf1 hpost1
      dsimp only [spqrRecvRawSpec, VecArg.at, stArg, msgArg] at hpost1
      rw [hspm] at hspf1 hpost1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt, errTag] at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨d, hpost1⟩
      simp only [sepConj_assoc] at hpost1
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hd_iff, hpost1⟩
      have hpost1' : sf1.mem ⊨
          (((sp + 1288#64) ↦₈ d) ∗
           memRegion (sp + 1289#64) 7 ∗
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
           tapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 8#64 = sp + 1288#64 by rw [BitVec.add_assoc]; rfl,
          show (sp + 1280#64) + 9#64 = sp + 1289#64 by rw [BitVec.add_assoc]; rfl,
          mr_cut sp 1289 7 32 39 1296#64] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      rw [show sp + 1289#64 = (sp + 1288#64) + 1#64 by rw [BitVec.add_assoc]; rfl] at hpost1'
      cases sd with
      | true =>
        have hd0 : d = 0#8 := hd_iff.mpr rfl
        subst hd0
        exact s5_out_add_np hnpF (KeyDeriveCallees.pqRecv_recv_err_true_549_placed C A ctl S H x trG tr st1 mkg draws R s0
          hsp0_al' hseed1 hseed2 hfmt_call hdealloc_call hsp_def
          sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
          htrace1 hvregs_1 hclf1 hLf1 hpost1')
      | false =>
        have hd_ne : d ≠ 0#8 := fun h => Bool.noConfusion (hd_iff.mp h)
        exact s5_out_add_np hnpF (KeyDeriveCallees.pqRecv_recv_err_false_549_placed C A ctl S H x trG tr st1 mkg draws R s0
          hmsgW hsp0_al' hseed1 hseed2 hfmt_call hdealloc_call hsp_def hd_ne
          sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
          htrace1 hvregs_1 hclf1 hLf1 hpost1')

theorem pqRecv_549_placed_ok_x [LibsignalPlacement] (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (hrecv_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl (spqrRecvRawSpec A S)))
    (hfmt_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ KeyDeriveCallees.lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    S5SeamXPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C decFn A ctl uuidTryParse S := by
  unfold S5SeamXPlaced
  simp only [tryDecryptFnSpecPlaced_onPanic_eq]
  exact pqRecv_549_placed_ok C A ctl S H hrecv_call hfmt_call hdealloc_call

end CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive

