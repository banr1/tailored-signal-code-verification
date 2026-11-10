/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.ShardFill.TryDecryptStateRatchetCoins
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.KeyDeriveBase
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.Entry
import ProofLib.SepLogic.WP.Apply

/-!
# `try_decrypt_with_state` Segment S6 (`DeriveKeys`) Proof

Proves segment S6 (`DeriveKeysSpec`, `+0x5dc → +0x63c`), staging `mkg` and `pqrKey` and invoking
`MessageKeyGenerator::generate_keys`.
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

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.deriveKeys_ok_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S6SpecExt img C A ctl ext := by
  intro hloads hgen x trG tr st1 mkg newPqrState pqrKey draws R s0 s hseed_len h6
  rcases h6 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25, hx27, hx28,
    seedCap, seedPtr, newPqrCap, newPqrPtr, msgW, hx8, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfrozen, hsym, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 :=
    ⟨hseed1, hseed2, hseed3⟩
  have hentry := entryOf_eq_tripleRatchetProgAtExt (ext := ext) hloads CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
  change CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName at hentry
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segDeriveKeysPC at hpc
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState
  refine reaches_pc_midMeta hfrozen hsym ?_
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC tryDecryptMidMetaCore
  rw [show (0x5dc#64 : BitVec 64) = 1500#64 by rfl] at hpc
  rw [show (0x63c#64 : BitVec 64) = 1596#64 by rfl]
  rw [hentry] at hpc ⊢
  unfold GenerateKeysOkExt at hgen
  rw [fnAddr_callee_of_fnOff (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") (k := (num% ((2^64 + ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))) (by decide)] at hgen
  have hentry_eq := (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq img.base ext).symm
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = entry
  decrypt_fetches_at_ext_cli hentry_eq 1500 96
  clear hentry_eq
  examples_hide_fetches
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29 ⊢
  clear hsp29_eq
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap at hmem ⊢
  generalize s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx27 hx28 hx29 hmem ⊢
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  simp only [← sepConj_assoc] at hmem
  refine reaches_pc_of_sepWP_frozen hmem hfrozen hsym
    (mid := entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
    (RegMid := fun sm =>
      newPqrState.length ≤ newPqrCap.toNat ∧ newPqrCap.toNat < 2 ^ 63 ∧ newPqrPtr ≠ 0 ∧
      sm.readReg64 .x0 = sp + 400#64 ∧
      sm.readReg64 .x1 = sp + 864#64 ∧
      sm.readReg64 .x8 = sp + 1280#64 ∧
      sm.readReg64 .lr = entry + bv% (1596) ∧
      sm.readReg64 .x19 = x.ret ∧
      sm.readReg64 .x20 = sp + 320#64 ∧
      sm.readReg64 .x21 = x.ss ∧
      sm.readReg64 .x22 = x.msgA ∧
      sm.readReg64 .x23 = sp + 976#64 ∧
      sm.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length ∧
      sm.readReg64 .x25 = sp + 400#64 ∧
      sm.readReg64 .x27 = sp + 56#64 ∧
      sm.readReg64 .x28 = sp + 1280#64 ∧
      sm.readReg64 .fp = sp + 1408#64 ∧
      sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    (P_mid :=
      mkgAt A (sp + 400#64) mkg ∗
      spqrRecvKeyAt A (sp + 864#64) pqrKey ∗
      memRegion (sp + 1280#64) 84 ∗
      A.pool ∗ stackAt sp tryDecryptSubStack ∗
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG tr ∗
      (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
        (newPqrPtr ↦ₛ newPqrState) ∗
        memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 8 ∗
      ((sp + 8#64) ↦₆₄ newPqrCap) ∗
      memRegion (sp + 16#64) 12 ∗
      ((sp + 28#64) ↦₃₂ msgW) ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₆₄ newPqrPtr) ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 80 ∗
      memRegion (sp + 440#64) 424 ∗
      memRegion (sp + 888#64) 216 ∗
      memRegion (sp + 1104#64) 176 ∗
      memRegion (sp + 1364#64) 44 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
      logOff img ∗
      tryDecryptSavedRegs s0.sp s0)
    ?_ ?_
  · wp_conv_pre =>
      simp only [sepConj_assoc]
      unfold vecU8At vecHeader
      rw [memRegion_split sp 8 8 (by decide),
        mr_cut_add sp 320 80 704 (by decide),
        mr_cut_add sp 400 8 696 (by decide),
        mr_cut_add sp 408 8 688 (by decide),
        mr_cut_add sp 416 8 680 (by decide),
        mr_cut_add sp 424 8 672 (by decide),
        mr_cut_add sp 432 8 664 (by decide),
        mr_cut_add sp 440 8 656 (by decide),
        mr_cut_add sp 448 8 648 (by decide),
        mr_cut_add sp 456 8 640 (by decide),
        mr_cut_add sp 464 8 632 (by decide),
        mr_cut_add sp 472 8 624 (by decide),
        mr_cut_add sp 480 8 616 (by decide),
        mr_cut_add sp 488 376 240 (by decide),
        mr_cut_add sp 864 8 232 (by decide),
        mr_cut_add sp 872 8 224 (by decide),
        mr_cut_add sp 880 8 216 (by decide),
        mr_cut_add sp 1116 4 160 (by decide),
        mr_cut_add sp 1120 8 152 (by decide),
        mr_cut_add sp 1128 8 144 (by decide),
        mr_cut_add sp 1136 8 136 (by decide),
        mr_cut_add sp 1144 8 128 (by decide),
        mr_cut_add sp 1152 8 120 (by decide),
        mr_cut_add sp 1160 8 112 (by decide)]
      simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        memRegion_eight (sp + 8#64),
        memRegion_eight (sp + 400#64),
        memRegion_eight (sp + 408#64),
        memRegion_eight (sp + 416#64),
        memRegion_eight (sp + 424#64),
        memRegion_eight (sp + 432#64),
        memRegion_eight (sp + 440#64),
        memRegion_eight (sp + 448#64),
        memRegion_eight (sp + 456#64),
        memRegion_eight (sp + 464#64),
        memRegion_eight (sp + 472#64),
        memRegion_eight (sp + 480#64),
        memRegion_eight (sp + 864#64),
        memRegion_eight (sp + 872#64),
        memRegion_eight (sp + 880#64),
        memRegion_four (sp + 1116#64),
        memRegion_eight (sp + 1120#64),
        memRegion_eight (sp + 1128#64),
        memRegion_eight (sp + 1136#64),
        memRegion_eight (sp + 1144#64),
        memRegion_eight (sp + 1152#64),
        memRegion_eight (sp + 1160#64),
        pointsTo64_split32 (sp + 400#64)]
    refine SepWP.focus_weaken (optKeyAt_split A (sp + 1304#64) pqrKey) (by sep_focus) ?_
    wp_pull_exists
    wp_focus_pure
    rintro ⟨hnp1, hnp2, hnp3⟩
    refine SepWP.focus_rw (pointsTo32_merge64 (sp + 1112#64) mkg.counter _) (by sep_focus) ?_
    wp_steps
    rw [show ((sp + 424#64) ↦₆₄ 32#64) = ((sp + 424#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) by
      rw [hseed_len]]
    refine SepWP.focus_weaken (optKeyAt_fold A (sp + 864#64) _ _ _ pqrKey) (by sep_focus) ?_
    refine SepWP.focus_weaken (mkgAt_fold A (sp + 400#64) seedCap seedPtr _ _ mkg hseed) (by sep_focus) ?_
    have hm16 : memRegion (sp + 16#64) 12 = memRegion (sp + 16#64) 8 ∗ memRegion (sp + 24#64) 4 := by
      simpa using mr_cut_add sp 16 8 4 (by decide)
    have hm440 : memRegion (sp + 440#64) 424 =
        memRegion (sp + 440#64) 8 ∗ (memRegion (sp + 448#64) 8 ∗ (memRegion (sp + 456#64) 8 ∗
        (memRegion (sp + 464#64) 8 ∗ (memRegion (sp + 472#64) 8 ∗ (memRegion (sp + 480#64) 8 ∗
        memRegion (sp + 488#64) 376))))) := by
      rw [mr_cut_add sp 440 8 416 (by decide),
        mr_cut_add sp 448 8 408 (by decide),
        mr_cut_add sp 456 8 400 (by decide),
        mr_cut_add sp 464 8 392 (by decide),
        mr_cut_add sp 472 8 384 (by decide),
        mr_cut_add sp 480 8 376 (by decide)]
    have hm1104 : memRegion (sp + 1104#64) 176 =
        memRegion (sp + 1104#64) 8 ∗ (memRegion (sp + 1112#64) 8 ∗ (memRegion (sp + 1120#64) 8 ∗
        (memRegion (sp + 1128#64) 8 ∗ (memRegion (sp + 1136#64) 8 ∗ (memRegion (sp + 1144#64) 8 ∗
        (memRegion (sp + 1152#64) 8 ∗ (memRegion (sp + 1160#64) 8 ∗ memRegion (sp + 1168#64) 112))))))) := by
      rw [mr_cut_add sp 1104 8 168 (by decide),
        mr_cut_add sp 1112 8 160 (by decide),
        mr_cut_add sp 1120 8 152 (by decide),
        mr_cut_add sp 1128 8 144 (by decide),
        mr_cut_add sp 1136 8 136 (by decide),
        mr_cut_add sp 1144 8 128 (by decide),
        mr_cut_add sp 1152 8 120 (by decide),
        mr_cut_add sp 1160 8 112 (by decide)]
    have hm1280 : memRegion (sp + 1280#64) 84 =
        memRegion (sp + 1280#64) 8 ∗ (memRegion (sp + 1288#64) 8 ∗ (memRegion (sp + 1296#64) 8 ∗
        (memRegion (sp + 1304#64) 8 ∗ (memRegion (sp + 1312#64) 8 ∗ (memRegion (sp + 1320#64) 8 ∗
        memRegion (sp + 1328#64) 36))))) := by
      rw [mr_cut_add sp 1280 8 76 (by decide),
        mr_cut_add sp 1288 8 68 (by decide),
        mr_cut_add sp 1296 8 60 (by decide),
        mr_cut_add sp 1304 8 52 (by decide),
        mr_cut_add sp 1312 8 44 (by decide),
        mr_cut_add sp 1320 8 36 (by decide)]
    have hm1328 : memRegion (sp + 1328#64) 80 =
        memRegion (sp + 1328#64) 36 ∗ memRegion (sp + 1364#64) 44 := by
      simpa using mr_cut_add sp 1328 36 44 (by decide)
    rw [hm16, hm440, hm1104, hm1280, hm1328]
    wp_done
  · intro sm hpcm hrunm hfm hsymm hReg
    rcases hReg with ⟨hnp1, hnp2, hnp3, hx0m, hx1m, hx8m, hlrm,
      hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
    rw [stackAt_sub sp tryDecryptSubStack generateKeysStack]
    wp_apply
    have hm320 : memRegion (sp + 320#64) 960 =
        memRegion (sp + 320#64) 80 ∗ (memRegion (sp + 400#64) 40 ∗
        (memRegion (sp + 440#64) 424 ∗ (memRegion (sp + 864#64) 24 ∗
        (memRegion (sp + 888#64) 216 ∗ memRegion (sp + 1104#64) 176)))) := by
      rw [mr_cut_add sp 320 80 880 (by decide),
        mr_cut_add sp 400 40 840 (by decide),
        mr_cut_add sp 440 424 416 (by decide),
        mr_cut_add sp 864 24 392 (by decide),
        mr_cut_add sp 888 216 176 (by decide)]
    rw [hm320]
    wp_done

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.deriveKeys_ok_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DeriveKeysSpec_trap img C A ctl abs :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.deriveKeys_ok_ext img C A ctl (trTrapExterns C abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.deriveKeys_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DeriveKeysSpec img C A ctl abs :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.deriveKeys_ok_ext img C A ctl (tripleRatchetExterns C ctl abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.deriveKeys_ok_x (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S6SpecX img C A ctl ext := by
  intro hloads hgen x trG tr st1 mkg newPqrState pqrKey draws R s0 s hseed_len h6
  rcases h6 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25, hx27, hx28,
    seedCap, seedPtr, newPqrCap, newPqrPtr, msgW, hx8, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfrozen, hsym, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 :=
    ⟨hseed1, hseed2, hseed3⟩
  have hentry := entryOf_eq_tripleRatchetProgAtExt (ext := ext) hloads CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
  change CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName at hentry
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segDeriveKeysPC at hpc
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState
  refine reaches_pc_midMeta hfrozen hsym ?_
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC tryDecryptMidMetaCore
  rw [show (0x5dc#64 : BitVec 64) = 1500#64 by rfl] at hpc
  rw [show (0x63c#64 : BitVec 64) = 1596#64 by rfl]
  rw [hentry] at hpc ⊢
  unfold GenerateKeysOkX at hgen
  rw [fnAddr_callee_of_fnOff (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") (k := (num% ((2^64 + ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))) (by decide)] at hgen
  have hentry_eq := (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq img.base ext).symm
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = entry
  decrypt_fetches_at_ext_cli hentry_eq 1500 96
  clear hentry_eq
  examples_hide_fetches
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29 ⊢
  clear hsp29_eq
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap at hmem ⊢
  generalize s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx27 hx28 hx29 hmem ⊢
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  simp only [← sepConj_assoc] at hmem
  refine reaches_pc_of_sepWP_frozen hmem hfrozen hsym
    (mid := entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
    (RegMid := fun sm =>
      newPqrState.length ≤ newPqrCap.toNat ∧ newPqrCap.toNat < 2 ^ 63 ∧ newPqrPtr ≠ 0 ∧
      sm.readReg64 .x0 = sp + 400#64 ∧
      sm.readReg64 .x1 = sp + 864#64 ∧
      sm.readReg64 .x8 = sp + 1280#64 ∧
      sm.readReg64 .lr = entry + bv% (1596) ∧
      sm.readReg64 .x19 = x.ret ∧
      sm.readReg64 .x20 = sp + 320#64 ∧
      sm.readReg64 .x21 = x.ss ∧
      sm.readReg64 .x22 = x.msgA ∧
      sm.readReg64 .x23 = sp + 976#64 ∧
      sm.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length ∧
      sm.readReg64 .x25 = sp + 400#64 ∧
      sm.readReg64 .x27 = sp + 56#64 ∧
      sm.readReg64 .x28 = sp + 1280#64 ∧
      sm.readReg64 .fp = sp + 1408#64 ∧
      sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    (P_mid :=
      mkgAt A (sp + 400#64) mkg ∗
      spqrRecvKeyAt A (sp + 864#64) pqrKey ∗
      memRegion (sp + 1280#64) 84 ∗
      A.pool ∗ stackAt sp tryDecryptSubStack ∗
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG tr ∗
      (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
        (newPqrPtr ↦ₛ newPqrState) ∗
        memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 8 ∗
      ((sp + 8#64) ↦₆₄ newPqrCap) ∗
      memRegion (sp + 16#64) 12 ∗
      ((sp + 28#64) ↦₃₂ msgW) ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₆₄ newPqrPtr) ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 80 ∗
      memRegion (sp + 440#64) 424 ∗
      memRegion (sp + 888#64) 216 ∗
      memRegion (sp + 1104#64) 176 ∗
      memRegion (sp + 1364#64) 44 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
      logOff img ∗
      tryDecryptSavedRegs s0.sp s0)
    ?_ ?_
  · wp_conv_pre =>
      simp only [sepConj_assoc]
      unfold vecU8At vecHeader
      rw [memRegion_split sp 8 8 (by decide),
        mr_cut_add sp 320 80 704 (by decide),
        mr_cut_add sp 400 8 696 (by decide),
        mr_cut_add sp 408 8 688 (by decide),
        mr_cut_add sp 416 8 680 (by decide),
        mr_cut_add sp 424 8 672 (by decide),
        mr_cut_add sp 432 8 664 (by decide),
        mr_cut_add sp 440 8 656 (by decide),
        mr_cut_add sp 448 8 648 (by decide),
        mr_cut_add sp 456 8 640 (by decide),
        mr_cut_add sp 464 8 632 (by decide),
        mr_cut_add sp 472 8 624 (by decide),
        mr_cut_add sp 480 8 616 (by decide),
        mr_cut_add sp 488 376 240 (by decide),
        mr_cut_add sp 864 8 232 (by decide),
        mr_cut_add sp 872 8 224 (by decide),
        mr_cut_add sp 880 8 216 (by decide),
        mr_cut_add sp 1116 4 160 (by decide),
        mr_cut_add sp 1120 8 152 (by decide),
        mr_cut_add sp 1128 8 144 (by decide),
        mr_cut_add sp 1136 8 136 (by decide),
        mr_cut_add sp 1144 8 128 (by decide),
        mr_cut_add sp 1152 8 120 (by decide),
        mr_cut_add sp 1160 8 112 (by decide)]
      simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        memRegion_eight (sp + 8#64),
        memRegion_eight (sp + 400#64),
        memRegion_eight (sp + 408#64),
        memRegion_eight (sp + 416#64),
        memRegion_eight (sp + 424#64),
        memRegion_eight (sp + 432#64),
        memRegion_eight (sp + 440#64),
        memRegion_eight (sp + 448#64),
        memRegion_eight (sp + 456#64),
        memRegion_eight (sp + 464#64),
        memRegion_eight (sp + 472#64),
        memRegion_eight (sp + 480#64),
        memRegion_eight (sp + 864#64),
        memRegion_eight (sp + 872#64),
        memRegion_eight (sp + 880#64),
        memRegion_four (sp + 1116#64),
        memRegion_eight (sp + 1120#64),
        memRegion_eight (sp + 1128#64),
        memRegion_eight (sp + 1136#64),
        memRegion_eight (sp + 1144#64),
        memRegion_eight (sp + 1152#64),
        memRegion_eight (sp + 1160#64),
        pointsTo64_split32 (sp + 400#64)]
    refine SepWP.focus_weaken (optKeyAt_split A (sp + 1304#64) pqrKey) (by sep_focus) ?_
    wp_pull_exists
    wp_focus_pure
    rintro ⟨hnp1, hnp2, hnp3⟩
    refine SepWP.focus_rw (pointsTo32_merge64 (sp + 1112#64) mkg.counter _) (by sep_focus) ?_
    wp_steps
    rw [show ((sp + 424#64) ↦₆₄ 32#64) = ((sp + 424#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) by
      rw [hseed_len]]
    refine SepWP.focus_weaken (optKeyAt_fold A (sp + 864#64) _ _ _ pqrKey) (by sep_focus) ?_
    refine SepWP.focus_weaken (mkgAt_fold A (sp + 400#64) seedCap seedPtr _ _ mkg hseed) (by sep_focus) ?_
    have hm16 : memRegion (sp + 16#64) 12 = memRegion (sp + 16#64) 8 ∗ memRegion (sp + 24#64) 4 := by
      simpa using mr_cut_add sp 16 8 4 (by decide)
    have hm440 : memRegion (sp + 440#64) 424 =
        memRegion (sp + 440#64) 8 ∗ (memRegion (sp + 448#64) 8 ∗ (memRegion (sp + 456#64) 8 ∗
        (memRegion (sp + 464#64) 8 ∗ (memRegion (sp + 472#64) 8 ∗ (memRegion (sp + 480#64) 8 ∗
        memRegion (sp + 488#64) 376))))) := by
      rw [mr_cut_add sp 440 8 416 (by decide),
        mr_cut_add sp 448 8 408 (by decide),
        mr_cut_add sp 456 8 400 (by decide),
        mr_cut_add sp 464 8 392 (by decide),
        mr_cut_add sp 472 8 384 (by decide),
        mr_cut_add sp 480 8 376 (by decide)]
    have hm1104 : memRegion (sp + 1104#64) 176 =
        memRegion (sp + 1104#64) 8 ∗ (memRegion (sp + 1112#64) 8 ∗ (memRegion (sp + 1120#64) 8 ∗
        (memRegion (sp + 1128#64) 8 ∗ (memRegion (sp + 1136#64) 8 ∗ (memRegion (sp + 1144#64) 8 ∗
        (memRegion (sp + 1152#64) 8 ∗ (memRegion (sp + 1160#64) 8 ∗ memRegion (sp + 1168#64) 112))))))) := by
      rw [mr_cut_add sp 1104 8 168 (by decide),
        mr_cut_add sp 1112 8 160 (by decide),
        mr_cut_add sp 1120 8 152 (by decide),
        mr_cut_add sp 1128 8 144 (by decide),
        mr_cut_add sp 1136 8 136 (by decide),
        mr_cut_add sp 1144 8 128 (by decide),
        mr_cut_add sp 1152 8 120 (by decide),
        mr_cut_add sp 1160 8 112 (by decide)]
    have hm1280 : memRegion (sp + 1280#64) 84 =
        memRegion (sp + 1280#64) 8 ∗ (memRegion (sp + 1288#64) 8 ∗ (memRegion (sp + 1296#64) 8 ∗
        (memRegion (sp + 1304#64) 8 ∗ (memRegion (sp + 1312#64) 8 ∗ (memRegion (sp + 1320#64) 8 ∗
        memRegion (sp + 1328#64) 36))))) := by
      rw [mr_cut_add sp 1280 8 76 (by decide),
        mr_cut_add sp 1288 8 68 (by decide),
        mr_cut_add sp 1296 8 60 (by decide),
        mr_cut_add sp 1304 8 52 (by decide),
        mr_cut_add sp 1312 8 44 (by decide),
        mr_cut_add sp 1320 8 36 (by decide)]
    have hm1328 : memRegion (sp + 1328#64) 80 =
        memRegion (sp + 1328#64) 36 ∗ memRegion (sp + 1364#64) 44 := by
      simpa using mr_cut_add sp 1328 36 44 (by decide)
    rw [hm16, hm440, hm1104, hm1280, hm1328]
    wp_done
  · intro sm hpcm hrunm hfm hsymm hReg
    rcases hReg with ⟨hnp1, hnp2, hnp3, hx0m, hx1m, hx8m, hlrm,
      hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
    rw [stackAt_sub sp tryDecryptSubStack generateKeysStackX]
    wp_call hgen { genA := sp + 400#64, g := mkg, pqrKeyA := sp + 864#64, pqrKey := pqrKey, ret := sp + 1280#64 }
    have hm320 : memRegion (sp + 320#64) 960 =
        memRegion (sp + 320#64) 80 ∗ (memRegion (sp + 400#64) 40 ∗
        (memRegion (sp + 440#64) 424 ∗ (memRegion (sp + 864#64) 24 ∗
        (memRegion (sp + 888#64) 216 ∗ memRegion (sp + 1104#64) 176)))) := by
      rw [mr_cut_add sp 320 80 880 (by decide),
        mr_cut_add sp 400 40 840 (by decide),
        mr_cut_add sp 440 424 416 (by decide),
        mr_cut_add sp 864 24 392 (by decide),
        mr_cut_add sp 888 216 176 (by decide)]
    rw [hm320]
    wp_done

end CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive
