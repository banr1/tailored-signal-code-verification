/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.M4.Decrypt
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalSpqrV1.Statements
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.ShardFill.TryDecryptStateRatchetCoins
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.AesDecrypt
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ApplyRatchet
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.ErrTailProof
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.FindChain
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.IdentityKeys
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProof
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ConsumeMsgKey
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepMain
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.PqRecv
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.VerifyMac
import LibsignalBinary.Proofs.Cli.TripleRatchet.RunAssembly.DecryptAssembly
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Root
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.Entry

/-!
# CLI SPQR V1 Ratchet Decryption Assembly

Composes the widened `spqr::recv` and `generate_keys` segments (`PqRecvDeriveSpecWT`) with the
remaining `try_decrypt_with_state` seams to prove `tryDecryptT_run_of_seamW` and
`tryDecryptV1_run_of_recvV1` on the CLI image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1.M4

set_option autoImplicit false

open Arm64 ProofLib CryptoGames CryptoGames.HKDF CryptoGames.LibsignalSession CryptoVerification.RustHeap

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Decrypt

/-! ## 1. Widened `PqRecv` + `DeriveKeys` Contract -/

private theorem optKeyAtW_eq_optKeyRecvAt (A : RustAlloc) (a : BitVec 64) (k : Salt) :
    optKeyAtW A a k = spqrRecvKeyAt A a k := by
  cases k <;> rfl

/-- Composed `S5 + S6` contract (`+0x5b8 → +0x63c / +0x30c` or panic) framing `TokenInit img ∗ R`
through `spqr::recv` and `generate_keys`, reaching `VerifyMacState` on `.ok`, `ErrTailState` on
`.error`, or panic under stack bound `rootStack ≤ s0.sp` (`DEV-SPQR4`). -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.PqRecvDeriveSpecWT (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  SpqrRecvOkWT img C A ctl S abs →
  GenerateKeysOkW img C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
      (R : SepProp) (s0 s : State),
      x.st.pqRatchetState.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      mkg.seed.length = 32 →
      tr.pqrState = x.st.pqRatchetState →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG tr st1 mkg draws (TokenInit img ∗ R) s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws
              (TokenInit img ∗ R) s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e draws (TokenInit img ∗ R) s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

private theorem h42b_pqr_len_lt {A : RustAlloc} {g : SignalMessageGhost} {a : BitVec 64}
    {m : SignalMessage} {Q : SepProp} {mem : Memory}
    (h : mem ⊨ KeyDerive.signalMessageRestAt A g a m ∗ Q) :
    m.pqRatchet.length < 2 ^ 40 := by
  unfold KeyDerive.signalMessageRestAt at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.1.2.2.2.1

private theorem h42b_spqrRecvStack_le {sp0 sp : BitVec 64}
    (hstack : rootStack ≤ sp0.toNat) (hsp : sp0 - 1504#64 = sp) :
    spqrRecvStack ≤ sp.toNat := by
  subst hsp
  have h1 : rootStack = 262144 := rfl
  have h2 : spqrRecvStack = 131072 := rfl
  rw [BitVec.toNat_sub_of_le]
  · simp only [BitVec.toNat_ofNat]
    omega
  · rw [BitVec.le_def]
    simp only [BitVec.toNat_ofNat]
    omega

private abbrev h42b_optKeyRestW := KeyDerive.optKeyRest

private theorem h42b_optKeyAtW_split (A : RustAlloc) (a : BitVec 64) (pqrKey : Salt) :
    optKeyAtW A a pqrKey ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        h42b_optKeyRestW A w0 w1 w2 pqrKey ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) := by
  rw [optKeyAtW_eq_optKeyRecvAt]
  exact KeyDerive.optKeyAt_split A a pqrKey

private theorem h42b_optKeyAtW_fold (A : RustAlloc) (a w0 w1 w2 : BitVec 64) (pqrKey : Salt) :
    h42b_optKeyRestW A w0 w1 w2 pqrKey ∗
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢
      optKeyAtW A a pqrKey := by
  rw [optKeyAtW_eq_optKeyRecvAt]
  exact KeyDerive.optKeyAt_fold A a w0 w1 w2 pqrKey

private def _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.h42b_DeriveKeysStateW (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
    (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segDeriveKeysPC img ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 32 = 1#32 ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x500#64 ∧
  ∃ (seedCap seedPtr newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
    s.readReg64 .x8 = newPqrCap ∧
    msgW.setWidth 8 = CryptoVerification.LibsignalSessionRepr.msgTypeByte x.msgType ∧
    mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG tr ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
      vecU8At A (sp + 0x500#64) newPqrCap newPqrPtr newPqrState ∗
      optKeyAtW A (sp + 0x518#64) pqrKey ∗
      memRegion x.ret 48 ∗
      memRegion sp 0x10 ∗
      ((sp + 0x10#64) ↦₆₄ seedPtr) ∗
      memRegion (sp + 0x18#64) 4 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₆₄ seedCap) ∗
      ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x310 ∗
      ((sp + 0x450#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 0x458#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 0x45c#64) 0xa4 ∗
      memRegion (sp + 0x530#64) 0x50 ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive in
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56 in

set_option maxHeartbeats 400000 in
private theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.h42b_s6_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hloads : Obj.Loads libsignalSessionImage img)
    (hgen : GenerateKeysOkW img C A ctl abs)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
    (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hseed_len : mkg.seed.length = 32)
    (h6 : CryptoVerification.Cli.LibsignalSpqrV1.M4.h42b_DeriveKeysStateW A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s) :
    reaches_pc (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC img) s
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1 (mkg.generateKeys C.F pqrKey)
        newPqrState draws R s0) := by
  let ext := tripleRatchetExterns C ctl abs
  change reaches_pc (tripleRatchetProgAtExt img.base ext) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC img) s _
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
  unfold GenerateKeysOkW generateKeysSpecW at hgen
  change subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr generateKeysName) _ at hgen
  rw [fnAddr_callee_of_fnOff (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys")
    (k := num% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))) (by decide)] at hgen
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
      sm.readReg64 .lr = entry + 1596#64 ∧
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
      optKeyAtW A (sp + 864#64) pqrKey ∗
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
        ProofLib.memRegion_eight (sp + 8#64),
        ProofLib.memRegion_eight (sp + 400#64),
        ProofLib.memRegion_eight (sp + 408#64),
        ProofLib.memRegion_eight (sp + 416#64),
        ProofLib.memRegion_eight (sp + 424#64),
        ProofLib.memRegion_eight (sp + 432#64),
        ProofLib.memRegion_eight (sp + 440#64),
        ProofLib.memRegion_eight (sp + 448#64),
        ProofLib.memRegion_eight (sp + 456#64),
        ProofLib.memRegion_eight (sp + 464#64),
        ProofLib.memRegion_eight (sp + 472#64),
        ProofLib.memRegion_eight (sp + 480#64),
        ProofLib.memRegion_eight (sp + 864#64),
        ProofLib.memRegion_eight (sp + 872#64),
        ProofLib.memRegion_eight (sp + 880#64),
        memRegion_four (sp + 1116#64),
        ProofLib.memRegion_eight (sp + 1120#64),
        ProofLib.memRegion_eight (sp + 1128#64),
        ProofLib.memRegion_eight (sp + 1136#64),
        ProofLib.memRegion_eight (sp + 1144#64),
        ProofLib.memRegion_eight (sp + 1152#64),
        ProofLib.memRegion_eight (sp + 1160#64),
        KeyDerive.pointsTo64_split32 (sp + 400#64)]
    refine SepWP.focus_weaken (h42b_optKeyAtW_split A (sp + 1304#64) pqrKey) (by sep_focus) ?_
    wp_pull_exists
    wp_focus_pure
    rintro ⟨hnp1, hnp2, hnp3⟩
    refine SepWP.focus_rw (pointsTo32_merge64 (sp + 1112#64) mkg.counter _) (by sep_focus) ?_
    wp_steps
    rw [show ((sp + 424#64) ↦₆₄ 32#64) = ((sp + 424#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) by
      rw [hseed_len]]
    refine SepWP.focus_weaken (h42b_optKeyAtW_fold A (sp + 864#64) _ _ _ pqrKey) (by sep_focus) ?_
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

private theorem h42b_pqr_len_lt_of_pre {P F R : SepProp} {A : RustAlloc}
    {g : SignalMessageGhost} {a : BitVec 64} {m : SignalMessage} {mem : Memory}
    (h : mem ⊨ P ∗ ((KeyDerive.signalMessageRestAt A g a m ∗ F) ∗ R)) :
    m.pqRatchet.length < 2 ^ 40 := by
  have h' : mem ⊨ KeyDerive.signalMessageRestAt A g a m ∗ (F ∗ R ∗ P) := by
    have heq : P ∗ ((KeyDerive.signalMessageRestAt A g a m ∗ F) ∗ R) =
        KeyDerive.signalMessageRestAt A g a m ∗ (F ∗ R ∗ P) := by ac_rfl
    exact heq ▸ h
  exact h42b_pqr_len_lt h'

private theorem h42b_pre_spqrRecvSpecWT {A : RustAlloc} {S : SpqrModel} {img : Obj.Image}
    {stArg msgArg : VecArg} {ret : BitVec 64} {sm : State} {F R : SepProp}
    (h1 : stArg.bytes.length < 2 ^ 32)
    (h2 : msgArg.bytes.length < 2 ^ 40)
    (h3 : spqrRecvStack ≤ sm.sp.toNat)
    (h : sm.mem ⊨ (spqrRecvSpecW A S img).pre (stArg, msgArg, ret) sm ∗ (F ∗ (TokenInit img ∗ R))) :
    sm.mem ⊨ (spqrRecvSpecWT A S img).pre (stArg, msgArg, ret) sm ∗ (F ∗ R) := by
  dsimp only [spqrRecvSpecWT]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨h1, h2, h3⟩, ?_⟩
  have heq : (TokenInit img ∗ (spqrRecvSpecW A S img).pre (stArg, msgArg, ret) sm) ∗ F ∗ R =
      (spqrRecvSpecW A S img).pre (stArg, msgArg, ret) sm ∗ (F ∗ (TokenInit img ∗ R)) := by ac_rfl
  exact heq ▸ h

private theorem h42b_post_spqrRecvSpecWT {A : RustAlloc} {S : SpqrModel} {img : Obj.Image}
    {x : VecArg × VecArg × BitVec 64} {sm sf1 : State} {F R : SepProp}
    (h : sf1.mem ⊨ ((spqrRecvSpecWT A S img).post x sm sf1 ∗ F) ∗ R) :
    sf1.mem ⊨ ((spqrRecvSpecW A S img).post x sm sf1 ∗ F) ∗ (TokenInit img ∗ R) := by
  dsimp only [spqrRecvSpecWT] at h
  have heq : ((TokenInit img ∗ (spqrRecvSpecW A S img).post x sm sf1) ∗ F) ∗ R =
      ((spqrRecvSpecW A S img).post x sm sf1 ∗ F) ∗ (TokenInit img ∗ R) := by ac_rfl
  exact heq ▸ h

private theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.h42b_onPanic_absorb {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {F R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 sf ∗ (F ∗ R)) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 sf ∗ R := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hp, hmem⟩
  refine ⟨hp, ?_⟩
  rw [← sepConj_assoc] at hmem
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmem

private theorem h42b_attach_left {prog : Program} {s : State} {A B : State → Prop} {c : Prop}
    (hc : c) (h : ∃ s', Steps prog s s' ∧ (A s' ∨ B s')) :
    ∃ s', Steps prog s s' ∧ ((A s' ∧ c) ∨ B s') := by
  obtain ⟨s', hs, h | h⟩ := h
  · exact ⟨s', hs, Or.inl ⟨h, hc⟩⟩
  · exact ⟨s', hs, Or.inr h⟩

open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive in
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56 in

set_option maxHeartbeats 400000 in
private theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.h42b_s5_ok_r (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hloads : Obj.Loads libsignalSessionImage img)
    (hHooks : TripleRatchetHooks C A S abs)
    (hrecvOk : SpqrRecvOkWT img C A ctl S abs)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hQ : x.st.pqRatchetState.length < 2 ^ 32)
    (hstack : rootStack ≤ s0.sp.toNat)
    (hpqr_eq : tr.pqrState = x.st.pqRatchetState)
    (h5 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG tr st1 mkg draws (TokenInit img ∗ R) s0 s)
    (hL : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        (CryptoVerification.Cli.LibsignalSpqrV1.M4.h42b_DeriveKeysStateW A ctl img x trG tr st1 mkg newPqrState pqrKey draws
            (TokenInit img ∗ R) s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧
            s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e draws (TokenInit img ∗ R) s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧
            s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R) := by
  let ext := tripleRatchetExterns C ctl abs
  have hS : Stage2Contracts img.base C A ctl uuidTryParse S ext := .of_tripleRatchetProgAt' hHooks
  change (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem at hL
  change ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧ _
  rcases h5 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25,
    seedCap, seedPtr, msgW, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfrozen, hsym, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 :=
    ⟨hseed1, hseed2, hseed3⟩
  have hentry := entryOf_eq_tripleRatchetProgAtExt (ext := ext) hloads CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
  change CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName at hentry
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segPqRecvPC at hpc
  rw [show (0x5b8#64 : BitVec 64) = 1464#64 by rfl] at hpc
  rw [hentry] at hpc
  have hentry_eq := (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq img.base ext).symm
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = entry
  have hrecv_call : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (entry + bv% ((2^64 + ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
      (spqrRecvSpecWT A S img) := by
    rw [← hentry_eq, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq]
    rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.tryDecrypt_add_spqrRecv_eq_fnAddr]
    exact sub_ok_at_of_fnAddr hrecvOk spqrRecvName 0 (Nat.add_zero _)
  clear hrecvOk
  have hfmt_call := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.formatInner_ok_at_entry_ext hS hentry_eq
  have hdealloc_call := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.dealloc_ok_at_entry_ext hS.toAllocContracts hentry_eq
  decrypt_fetches_at_ext_cli hentry_eq 1464 36
  examples_hide_fetches
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29
  clear hsp29_eq
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx29 hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  generalize hR'_def : (TokenInit img ∗ R) = R' at hmem
  simp only [← sepConj_assoc] at hmem
  refine steps_of_sepWP hmem hL hfrozen hsym
    (mid := entry + bv% ((2^64 + ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
    (RegMid := fun sm =>
      sm.readReg64 .x0 = sp + 232#64 ∧
      sm.readReg64 .x1 = x.msgA ∧
      sm.readReg64 .x8 = sp + 1280#64 ∧
      sm.readReg64 .lr = entry + 1488#64 ∧
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
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
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
    subst hR'_def
    rcases hReg with ⟨hx0m, hx1m, hx8m, hlrm, hx19m, hx20m, hx21m, hx22m, hx23m, hw24m,
      hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
    let stArg : VecArg := ⟨sp + 232#64, trG.pq.cap, trG.pq.ptr, tr.pqrState⟩
    let msgArg : VecArg := ⟨x.msgA, x.msgG.pqCap, x.msgG.pqPtr, x.msg.pqRatchet⟩
    have hpre_call0 : sm.mem ⊨ (spqrRecvSpecW A S img).pre (stArg, msgArg, sp + 1280#64) sm ∗
        ((signalMessageRestAt A x.msgG x.msgA x.msg ∗
          trRestAt A sp trG tr ∗
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
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - spqrRecvStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ (TokenInit img ∗ R)) := by
      dsimp only [spqrRecvSpecW, Spec.inImage, VecArg.at, stArg, msgArg]
      rw [hspm]
      rw [trAt_split_pq, signalMessageAt_split_pq,
        stackAt_sub sp tryDecryptSubStack spqrRecvStack] at hmm
      rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hfm, hsymm⟩, ⟨hx0m, hx1m, hx8m⟩, ?_⟩
      simp only [sepConj_assoc] at hmm ⊢
      arm64_sep_close
    have hpq_lt : msgArg.bytes.length < 2 ^ 40 := h42b_pqr_len_lt_of_pre hpre_call0
    have hst_lt : stArg.bytes.length < 2 ^ 32 := by
      show tr.pqrState.length < 2 ^ 32
      rw [hpqr_eq]
      exact hQ
    have hsp_lt : spqrRecvStack ≤ sm.sp.toNat := by
      rw [hspm]
      exact h42b_spqrRecvStack_le hstack hsp_def
    have hpre_callWT := h42b_pre_spqrRecvSpecWT hst_lt hpq_lt hsp_lt hpre_call0
    clear hpre_call0
    cases hrecv : S.recv tr.pqrState x.msg.pqRatchet with
    | ok pair =>
      clear hentry_eq
      rcases pair with ⟨newPqrState, pqrKey⟩
      refine steps_call hrecv_call (x := (stArg, msgArg, sp + 1280#64))
        hpcm hrunm hsp_alm hlrm hfm hsymm hLm hpre_callWT
        (fun sf hpan hpost => ⟨hpan, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.onPanic_of_spqrRecv (st := stArg) (msg := msgArg)
          (ret := sp + 1280#64) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hff1 hsymf1 hLf1 hpost1
      have hpost1W := h42b_post_spqrRecvSpecWT hpost1
      clear hpost1
      dsimp only [spqrRecvSpecW, Spec.inImage, VecArg.at, stArg, msgArg] at hpost1W
      rw [hspm] at hspf1 hpost1W
      have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1W
      rcases hpost1W with ⟨⟨htrace1, hnpR⟩, hpost1W⟩
      have hnp5 : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnpR
      clear hnpR
      rw [htracem] at htrace1
      rw [hrecv] at hpost1W
      dsimp only [recvResultAtW] at hpost1W
      unfold vecU8 at hpost1W
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1W
      rcases hpost1W with ⟨newPqrCap, newPqrPtr, hpost1W⟩
      have hpost1' : sf1.mem ⊨
          vecU8At A (sp + 1280#64) newPqrCap newPqrPtr newPqrState ∗
          (optKeyAtW A (sp + 1304#64) pqrKey ∗
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
           A.pool) ∗ (TokenInit img ∗ R) := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 24#64 = sp + 1304#64 by rw [BitVec.add_assoc]; rfl] at hpost1W
        simp only [sepConj_assoc] at hpost1W ⊢
        arm64_sep_close
      unfold vecU8At vecHeader at hpost1'
      simp only [sepConj_assoc] at hpost1'
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1'
      rcases hpost1' with ⟨⟨hnp1, hnp2, hnp3⟩, hpost1'⟩
      have hcap_not_m1 : (newPqrCap + 1#64 == 0#64) = false := cap_add_one_ne_zero hnp2
      refine h42b_attach_left hnp5 ?_
      generalize hR'_def : (TokenInit img ∗ R) = R' at hpost1' ⊢
      simp only [← sepConj_assoc] at hpost1'
      unfold CryptoVerification.Cli.LibsignalSpqrV1.M4.h42b_DeriveKeysStateW
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
            msgW.setWidth 8 = CryptoVerification.LibsignalSessionRepr.msgTypeByte x.msgType ∧
            mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
            (sf.mem ⊨
              sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trAt A ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
              (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
                (seedPtr ↦ₛ mkg.seed) ∗
                memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
              vecU8At A ((s0.sp - 1504#64) + 0x500#64) newPqrCap newPqrPtr newPqrState ∗
              optKeyAtW A ((s0.sp - 1504#64) + 0x518#64) pqrKey ∗
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
              CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R'))
        hpost1' hLf1 hff1 hsymf1 ?_
      unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segDeriveKeysPC tryDecryptMidMetaCore CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap
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
        hpcm hrunm hsp_alm hlrm hfm hsymm hLm hpre_callWT
        (fun sf hpan hpost => ⟨hpan, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.onPanic_of_spqrRecv (st := stArg) (msg := msgArg)
          (ret := sp + 1280#64) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hff1 hsymf1 hLf1 hpost1
      have hpost1W := h42b_post_spqrRecvSpecWT hpost1
      clear hpost1
      dsimp only [spqrRecvSpecW, Spec.inImage, VecArg.at, stArg, msgArg] at hpost1W
      rw [hspm] at hspf1 hpost1W
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1W
      rcases hpost1W with ⟨⟨htrace1, hnpR⟩, hpost1W⟩
      have hnp5 : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnpR
      clear hnpR
      rw [htracem] at htrace1
      rw [hrecv] at hpost1W
      dsimp only [recvResultAtW, errTag] at hpost1W
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1W
      rcases hpost1W with ⟨d, hpost1W⟩
      simp only [sepConj_assoc] at hpost1W
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1W
      rcases hpost1W with ⟨hd_iff, hpost1W⟩
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
           CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
           logOff img ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ (TokenInit img ∗ R) := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 8#64 = sp + 1288#64 by rw [BitVec.add_assoc]; rfl,
          show (sp + 1280#64) + 9#64 = sp + 1289#64 by rw [BitVec.add_assoc]; rfl,
          mr_cut sp 1289 7 32 39 1296#64] at hpost1W
        simp only [sepConj_assoc] at hpost1W ⊢
        arm64_sep_close
      rw [show sp + 1289#64 = (sp + 1288#64) + 1#64 by rw [BitVec.add_assoc]; rfl] at hpost1'
      cases sd with
      | true =>
        have hd0 : d = 0#8 := hd_iff.mpr rfl
        subst hd0
        obtain ⟨s', hsteps', herr | ⟨hpan, hq⟩⟩ :=
          CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.pqRecv_recv_err_true img C A ctl S ext hloads x trG tr st1 mkg draws
            (TokenInit img ∗ R) s0
            hsp0_al' hseed1 hseed2 hentry hentry_eq hfmt_call hdealloc_call hsp_def
            sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
            htrace1 hvregs_1 hff1 hsymf1 hLf1 hpost1'
        · exact ⟨s', hsteps', Or.inl ⟨herr, hnp5⟩⟩
        · exact ⟨s', hsteps', Or.inr ⟨hpan, CryptoVerification.Cli.LibsignalSpqrV1.M4.h42b_onPanic_absorb hq⟩⟩
      | false =>
        have hd_ne : d ≠ 0#8 := fun h => Bool.noConfusion (hd_iff.mp h)
        obtain ⟨s', hsteps', herr | ⟨hpan, hq⟩⟩ :=
          CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.pqRecv_recv_err_false img C A ctl S ext x trG tr st1 mkg draws
            (TokenInit img ∗ R) s0
            hmsgW hsp0_al' hseed1 hseed2 hentry hentry_eq hfmt_call hdealloc_call hsp_def hd_ne
            sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
            htrace1 hvregs_1 hff1 hsymf1 hLf1 hpost1'
        · exact ⟨s', hsteps', Or.inl ⟨herr, hnp5⟩⟩
        · exact ⟨s', hsteps', Or.inr ⟨hpan, CryptoVerification.Cli.LibsignalSpqrV1.M4.h42b_onPanic_absorb hq⟩⟩

private theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.h42b_pqRecvDerive_okWT_r (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel) (abs : String → Option (State → State)) :
    Obj.Loads libsignalSessionImage img →
    TripleRatchetHooks C A S abs →
    SpqrRecvOkWT img C A ctl S abs →
    GenerateKeysOkW img C A ctl abs →
      ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
        (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
        (R : SepProp) (s0 s : State),
        x.st.pqRatchetState.length < 2 ^ 32 →
        rootStack ≤ s0.sp.toNat →
        mkg.seed.length = 32 →
        tr.pqrState = x.st.pqRatchetState →
        CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG tr st1 mkg draws (TokenInit img ∗ R) s0 s →
        (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
        match S.recv tr.pqrState x.msg.pqRatchet with
        | .ok (newPqrState, pqrKey) =>
          ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
            ((CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws
                (TokenInit img ∗ R) s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
             (s'.status = .Panicked ∧
               (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))
        | .error sd =>
          let e : SignalProtocolError :=
            if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
          ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
            ((CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e draws (TokenInit img ∗ R) s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
             (s'.status = .Panicked ∧
               (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  intro hloads hHooks hrecvOk hgen x trG tr st1 mkg draws R s0 s hQ hstack hseed_len hpqr_eq h5 hL
  obtain ⟨s6, hsteps6, hs6⟩ :=
    CryptoVerification.Cli.LibsignalSpqrV1.M4.h42b_s5_ok_r img C A ctl S abs hloads hHooks hrecvOk x trG tr st1 mkg draws R s0 s
      hQ hstack hpqr_eq h5 hL
  cases hrecv : S.recv tr.pqrState x.msg.pqRatchet with
  | error sd =>
    rw [hrecv] at hs6
    exact ⟨s6, hsteps6, hs6⟩
  | ok pair =>
    rcases pair with ⟨newPqrState, pqrKey⟩
    rw [hrecv] at hs6
    rcases hs6 with hs6_state | hpan
    · have hL6 := hsteps6.codeLoaded hL
      obtain ⟨hs6_state, hnp⟩ := hs6_state
      rcases CryptoVerification.Cli.LibsignalSpqrV1.M4.h42b_s6_ok img C A ctl abs hloads hgen x trG tr st1 mkg newPqrState pqrKey draws
          (TokenInit img ∗ R) s0 s6 hseed_len hs6_state hL6 with
        ⟨s7, hsteps7, ⟨_, _, hs7_state⟩ | ⟨_, hfalse⟩⟩
      swap; · exact hfalse.elim
      exact ⟨s7, hsteps6.trans hsteps7, Or.inl ⟨hs7_state, hnp⟩⟩
    · exact ⟨s6, hsteps6, Or.inr hpan⟩

theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.pqRecvDerive_okWT (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalSpqrV1.M4.PqRecvDeriveSpecWT img C A ctl uuidTryParse S abs :=
  CryptoVerification.Cli.LibsignalSpqrV1.M4.h42b_pqRecvDerive_okWT_r img C A ctl S abs

/-! ## 2. Top-Level `try_decrypt_with_state` Composition -/

private theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.h44_reaches_outcome_specT {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : reaches_outcome prog (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img) x (TokenInit img ∗ R) s0 s) :
    reaches_outcome prog (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT C A ctl uuidTryParse S img) x R s0 s := by
  refine h.mono_outcome (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hexit, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT]
    have heq : (TokenInit img ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).post x s0 sf) ∗ R =
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).post x s0 sf ∗ (TokenInit img ∗ R) := by ac_rfl
    exact heq ▸ hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT, CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨hq.1, ?_⟩
    have hq2 := hq.2
    rw [← sepConj_assoc] at hq2
    exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hq2
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

private theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.h44_reaches_outcome_of_consumeMsgKey
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hRecv : SpqrRecvOkWT img C A ctl S abs)
    (hGK : GenerateKeysOkW img C A ctl abs)
    (hcallees : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs4 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeySpec img C A ctl uuidTryParse S abs)
    (hSeam : CryptoVerification.Cli.LibsignalSpqrV1.M4.PqRecvDeriveSpecWT img C A ctl uuidTryParse S abs)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacSpec img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptSpec img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetSpec img C A ctl uuidTryParse S abs)
    (herr : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpec img C A ctl uuidTryParse S abs)
    {x : TryDecryptGhost} {trG : TrGhost} {tr0 : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 : RatchetState}
    {draws : Nat} {R : SepProp} {s0 s4 : State}
    (hseeds : SeedsLen32 x.st)
    (hQ : x.st.pqRatchetState.length < 2 ^ 32)
    (hstk : rootStack ≤ s0.sp.toNat)
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr0.ratchet = (.ok ck, r1))
    (hdraws : draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest)
    (hs4_state : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img x trG { tr0 with ratchet := r1 } st1 ck draws
      (TokenInit img ∗ R) s0 s4)
    (hL4 : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s4.mem) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT C A ctl uuidTryParse S img) x R s0 s4 := by
  have ⟨_, _, hpqr0, _, _⟩ := Model.fromSessionState_ok_inv htr
  have hs4_step := hs4 hloads hhooks hcallees.cmk x trG { tr0 with ratchet := r1 } st1 ck draws
    (TokenInit img ∗ R) s0 s4 hs4_state hL4
  dsimp only at hs4_step
  cases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 with
  | mk cmkRes r2 =>
    rw [hcmk] at hs4_step
    cases cmkRes with
    | error e =>
      apply CryptoVerification.Cli.LibsignalSpqrV1.M4.h44_reaches_outcome_specT
      have hmodel := Model.model_of_cmk_error (S := S) htr herc hcmk
      have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
      have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
      rcases hs4_step with ⟨s4', hsteps4, ⟨hne, trG', herr_st⟩ | ⟨hpan, hp, hmem⟩⟩
      · subst hdraws
        exact Decrypt.reaches_outcome_steps hsteps4
          (herr hloads hhooks hcallees.dropChain x trG' { tr0 with ratchet := r2 } st1 e
            (TokenInit img ∗ R) s0 s4' hne hm1 hm2 herr_st)
      · exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.reaches_outcome_of_panic hsteps4 hpan (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.onPanic_of_cmk_panic hm1 hp hmem)
    | ok mkg =>
      rcases hs4_step with ⟨s5, hsteps5, ⟨trG5, hs5_state⟩ | ⟨hpan, hq⟩⟩
      · refine Decrypt.reaches_outcome_steps hsteps5 ?_
        have hL5 := hsteps5.codeLoaded hL4
        have hseed32 : mkg.seed.length = 32 := decrypt_mkg_seed hseeds htr herc hcmk
        have hs56_step := hSeam hloads hhooks hRecv hGK x trG5 { tr0 with ratchet := r2 } st1 mkg
          draws R s0 s5 hQ hstk hseed32 hpqr0 hs5_state hL5
        dsimp only at hs56_step
        cases hspqr : S.recv tr0.pqrState x.msg.pqRatchet with
        | error sd =>
          rw [hspqr] at hs56_step
          rcases hs56_step with ⟨s5', hsteps5', ⟨herr_st, hnp5⟩ | ⟨hpan, hq⟩⟩
          · have hmodel := Model.model_of_spqr_error htr herc hcmk hspqr hnp5
            let e : SignalProtocolError :=
              if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
            have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
            have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
            have hne : e ≠ .panic := by subst e; cases sd <;> nofun
            apply CryptoVerification.Cli.LibsignalSpqrV1.M4.h44_reaches_outcome_specT
            subst hdraws
            exact Decrypt.reaches_outcome_steps hsteps5'
              (herr hloads hhooks hcallees.dropChain x trG5 { tr0 with ratchet := r2 } st1 e
                (TokenInit img ∗ R) s0 s5' hne hm1 hm2 herr_st)
          · exact Decrypt.reaches_outcome_steps hsteps5'
              (reaches_outcome_refl_panic
                (spec := CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT C A ctl uuidTryParse S img) hpan hq)
        | ok pqrRes =>
          rcases pqrRes with ⟨newPqrState, pqrKey⟩
          rw [hspqr] at hs56_step
          rcases hs56_step with ⟨s7, hsteps7, ⟨hs7_state, hnp5⟩ | ⟨hpan, hq⟩⟩
          · apply CryptoVerification.Cli.LibsignalSpqrV1.M4.h44_reaches_outcome_specT
            refine Decrypt.reaches_outcome_steps hsteps7 ?_
            have hL7 := hsteps7.codeLoaded hL5
            let mks := mkg.generateKeys C.F pqrKey
            have hs7_step := hs7 hloads hhooks hcallees.verifyMac x trG5 { tr0 with ratchet := r2 }
              st1 mks newPqrState draws (TokenInit img ∗ R) s0 s7 hs7_state hL7
            dsimp only at hs7_step
            cases hmac : x.msg.verifyMacWithAddresses C.F
                (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
                tr0.remoteIdentityKey tr0.localIdentityKey mks.macKey with
            | false =>
              rw [hmac] at hs7_step
              simp only [Bool.false_eq_true, ↓reduceIte] at hs7_step
              have hmodel := Model.model_of_verifyMac_false htr herc hcmk hspqr hmac hnp5
              have hm1 : (x.model C S uuidTryParse).1 = .error (.invalidMessage x.msgType .macFailed) := by
                rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne : SignalProtocolError.invalidMessage x.msgType .macFailed ≠ .panic := nofun
              rcases hs7_step with ⟨s7', hsteps7', herr_st | ⟨hpan, hq⟩⟩
              · subst hdraws
                exact Decrypt.reaches_outcome_steps hsteps7'
                  (herr hloads hhooks hcallees.dropChain x trG5 { tr0 with ratchet := r2 } st1
                    (.invalidMessage x.msgType .macFailed) (TokenInit img ∗ R) s0 s7' hne hm1 hm2 herr_st)
              · exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.reaches_outcome_of_panic hsteps7' hpan hq
            | true =>
              rw [hmac] at hs7_step
              simp only [↓reduceIte] at hs7_step
              rcases hs7_step with ⟨s8, hsteps8, hs8_state | ⟨hpan, hq⟩⟩
              · refine Decrypt.reaches_outcome_steps hsteps8 ?_
                have hL8 := hsteps8.codeLoaded hL7
                have hs8_step := hs8 hloads hhooks x trG5 { tr0 with ratchet := r2 }
                  st1 mks newPqrState draws (TokenInit img ∗ R) s0 s8 hs8_state hL8
                cases haes : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
                | none =>
                  rw [haes] at hs8_step
                  have hmodel := Model.model_of_aesDec_none htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.model C S uuidTryParse).1 =
                      .error (.invalidMessage x.msgType .badCiphertext) := by rw [hmodel]
                  have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
                  have hne : SignalProtocolError.invalidMessage x.msgType .badCiphertext ≠ .panic :=
                    nofun
                  rcases hs8_step with ⟨s8', hsteps8', herr_st | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    exact Decrypt.reaches_outcome_steps hsteps8'
                      (herr hloads hhooks hcallees.dropChain x trG5 { tr0 with ratchet := r2 } st1
                        (.invalidMessage x.msgType .badCiphertext) (TokenInit img ∗ R) s0 s8' hne hm1 hm2 herr_st)
                  · exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.reaches_outcome_of_panic hsteps8' hpan hq
                | some pt =>
                  rw [haes] at hs8_step
                  have hmodel := Model.model_of_aesDec_some htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel]
                  have hm2 : (x.model C S uuidTryParse).2 =
                      (({ { tr0 with ratchet := r2 } with pqrState := newPqrState }).applyToSessionState
                        st1).clearUnacknowledgedPreKeyMessage := by rw [hmodel]
                  rcases hs8_step with ⟨s9, hsteps9, hs9_state | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    exact Decrypt.reaches_outcome_steps hsteps9
                      (hs9 hloads hhooks hcallees.trApply hcallees.clearUpk x trG5
                        { tr0 with ratchet := r2 } st1 newPqrState pt (TokenInit img ∗ R) s0 s9 hm1 hm2 hs9_state)
                  · exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.reaches_outcome_of_panic hsteps9 hpan hq
              · exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.reaches_outcome_of_panic hsteps8 hpan hq
          · exact Decrypt.reaches_outcome_steps hsteps7
              (reaches_outcome_refl_panic
                (spec := CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT C A ctl uuidTryParse S img) hpan hq)
      · exact CryptoVerification.Cli.LibsignalSpqrV1.M4.h44_reaches_outcome_specT (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.reaches_outcome_of_panic hsteps5 hpan hq)

private theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.h44_try_decrypt_ok_of_seamW
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hRecv : SpqrRecvOkWT img C A ctl S abs)
    (hGK : GenerateKeysOkW img C A ctl abs)
    (hcallees : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs0 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.IdentityKeysSpec img C A ctl uuidTryParse S abs)
    (hs1 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetSpec img C A ctl uuidTryParse S abs)
    (hs2 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainSpec img C A ctl abs)
    (hs3 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepSpec img C A ctl uuidTryParse S abs)
    (hs4 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeySpec img C A ctl uuidTryParse S abs)
    (hSeam : CryptoVerification.Cli.LibsignalSpqrV1.M4.PqRecvDeriveSpecWT img C A ctl uuidTryParse S abs)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacSpec img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptSpec img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetSpec img C A ctl uuidTryParse S abs)
    (herr : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpec img C A ctl uuidTryParse S abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT C A ctl uuidTryParse S img) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT] at hpre
  have hpre_eq : (⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗ TokenInit img ∗
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).pre x s0) ∗ R =
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        ((CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).pre x s0 ∗ (TokenInit img ∗ R)) := by ac_rfl
  rw [hpre_eq, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hQ, hpre⟩
  obtain ⟨hseeds, hchains, hstk⟩ := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.seedsLen32_of_pre hpre
  rcases hs0 hloads hcallees.localIk hcallees.remoteIk hcallees.sameAcc x (TokenInit img ∗ R) s0
      hpc hrun hsp hpre hL with
    ⟨s1, hsteps1, ⟨_, _, hs1_state⟩ | ⟨_, hfalse⟩⟩
  swap; · exact hfalse.elim
  refine Decrypt.reaches_outcome_steps hsteps1 ?_
  have hL1 := hsteps1.codeLoaded hL
  have hs1_step := hs1 hloads hcallees.trFrom x (TokenInit img ∗ R) s0 s1 hs1_state hL1
  cases htr : Mut.exec TripleRatchet.fromSessionState x.st with
  | mk trRes st1 =>
    rw [htr] at hs1_step
    cases trRes with
    | error e =>
      exact CryptoVerification.Cli.LibsignalSpqrV1.M4.h44_reaches_outcome_specT hs1_step
    | ok tr0 =>
      rcases hs1_step with ⟨s2, hsteps2, trG2, hs2_state⟩
      refine Decrypt.reaches_outcome_steps hsteps2 ?_
      have hL2 := hsteps2.codeLoaded hL1
      have hs2_step := hs2 hloads hcallees.findReceiverChainKey x trG2 tr0 st1
        (TokenInit img ∗ R) s0 s2 hs2_state hL2
      cases hf : tr0.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | error e =>
        rw [hf] at hs2_step
        rcases hs2_step hL2 with ⟨s2', hsteps2', ⟨_, _, herr_st⟩ | ⟨_, hfalse⟩⟩
        swap; · exact hfalse.elim
        have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
            (coinsOf x.rest)) tr0.ratchet = (.error e, tr0.ratchet) :=
          Model.ensureReceiverChain_of_find_error hf
        have hmodel := Model.model_of_ensureReceiverChain_error (S := S) htr herc
        have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
        have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
        have hne : e ≠ .panic := by
          have he := Model.findReceiverChainKey_error_eq hf
          subst he
          decide
        have hdraws : decryptDraws C x.st x.msg.senderRatchetKey x.rest = 0 :=
          Model.decryptDraws_of_find_error x.rest htr hf
        rw [← hdraws] at herr_st
        apply CryptoVerification.Cli.LibsignalSpqrV1.M4.h44_reaches_outcome_specT
        exact Decrypt.reaches_outcome_steps hsteps2'
          (herr hloads hhooks hcallees.dropChain x trG2 tr0 st1 e (TokenInit img ∗ R) s0 s2'
            hne hm1 hm2 herr_st)
      | ok optCk =>
        cases optCk with
        | some ck =>
          rw [hf] at hs2_step
          rcases hs2_step hL2 with ⟨s4, hsteps4, ⟨_, _, hs4_state⟩ | ⟨_, hfalse⟩⟩
          swap; · exact hfalse.elim
          refine Decrypt.reaches_outcome_steps hsteps4 ?_
          have hL4 := hsteps4.codeLoaded hL2
          have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet = (.ok ck, tr0.ratchet) :=
            Model.ensureReceiverChain_of_find_some hf
          have hdraws : 0 = decryptDraws C x.st x.msg.senderRatchetKey x.rest :=
            (Model.decryptDraws_of_find_some x.rest htr hf).symm
          exact CryptoVerification.Cli.LibsignalSpqrV1.M4.h44_reaches_outcome_of_consumeMsgKey hloads hhooks hRecv hGK hcallees
            hs4 hSeam hs7 hs8 hs9 herr hseeds hQ hstk htr herc hdraws hs4_state hL4
        | none =>
          rw [hf] at hs2_step
          rcases hs2_step hL2 with ⟨s3, hsteps3, ⟨_, _, hs3_state⟩ | ⟨_, hfalse⟩⟩
          swap; · exact hfalse.elim
          refine Decrypt.reaches_outcome_steps hsteps3 ?_
          have hL3 := hsteps3.codeLoaded hL2
          have htr_chains : tr0.ratchet.receiverChains.length < 2 ^ 32 := by
            rw [(Model.fromSessionState_ok_inv htr).2.1]
            exact hchains
          have hs3_step := hs3 hloads hhooks hcallees.createChain hcallees.derivePk
            hcallees.pkSer hcallees.chainKeyToPb hcallees.growOne hcallees.dropChain
            x trG2 tr0 st1 (TokenInit img ∗ R) s0 s3 htr hf htr_chains hstk hs3_state hL3
          dsimp only at hs3_step
          cases hdh : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet with
          | mk dhRes r1 =>
            rw [hdh] at hs3_step
            cases dhRes with
            | error e =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.error e, r1) := by
                rw [Model.ensureReceiverChain_of_find_none hf, hdh]
              have hmodel := Model.model_of_ensureReceiverChain_error (S := S) htr herc
              have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne : e ≠ .panic := Model.dhRatchetStep_error_ne_panic hdh
              rcases hs3_step with ⟨s3', hsteps3', ⟨trG3, r1', herr_st⟩ | ⟨hpan, hq⟩⟩
              · apply CryptoVerification.Cli.LibsignalSpqrV1.M4.h44_reaches_outcome_specT
                exact Decrypt.reaches_outcome_steps hsteps3'
                  (herr hloads hhooks hcallees.dropChain x trG3 { tr0 with ratchet := r1' } st1 e
                    (TokenInit img ∗ R) s0 s3' hne hm1 hm2 herr_st)
              · exact CryptoVerification.Cli.LibsignalSpqrV1.M4.h44_reaches_outcome_specT (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.reaches_outcome_of_panic hsteps3' hpan hq)
            | ok ck =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.ok ck, r1) := by
                rw [Model.ensureReceiverChain_of_find_none hf, hdh]
              rcases hs3_step with ⟨s4, hsteps4, ⟨trG4, hs4_state⟩ | ⟨hpan, hq⟩⟩
              · refine Decrypt.reaches_outcome_steps hsteps4 ?_
                have hL4 := hsteps4.codeLoaded hL3
                exact CryptoVerification.Cli.LibsignalSpqrV1.M4.h44_reaches_outcome_of_consumeMsgKey hloads hhooks hRecv hGK hcallees
                  hs4 hSeam hs7 hs8 hs9 herr hseeds hQ hstk htr herc rfl hs4_state hL4
              · exact CryptoVerification.Cli.LibsignalSpqrV1.M4.h44_reaches_outcome_specT (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.reaches_outcome_of_panic hsteps4 hpan hq)

/-- `try_decrypt_with_state` satisfies `tryDecryptSpecT` for any `SpqrModel` `S` whose `spqr::recv`
satisfies `SpqrRecvOkWT`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.tryDecryptT_run_of_seamW (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hRecv : SpqrRecvOkWT img C A ctl S abs)
    (hGK : GenerateKeysOkW img C A ctl abs)
    (hSeam : CryptoVerification.Cli.LibsignalSpqrV1.M4.PqRecvDeriveSpecWT img C A ctl uuidTryParse S abs) :
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT C A ctl uuidTryParse S img) := by
  rw [tripleRatchetProg_eq_tripleRatchetProgAt himg]
  exact CryptoVerification.Cli.LibsignalSpqrV1.M4.h44_try_decrypt_ok_of_seamW himg hHooks hRecv hGK
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecryptCallees C A ctl S abs img hHooks himg)
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_ok CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.loadRatchet_ok CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_ok
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.dhStep_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.consumeMsgKey_ok img C A ctl S abs)
    hSeam
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.verifyMac_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.aesDecrypt_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.applyRatchet_ok img C A ctl S abs)
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_ok

/-- `TryDecryptV1RunStmt` follows from `SpqrRecvV1Stmt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.tryDecryptV1_run_of_recvV1 (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hRecvV1 : SpqrRecvV1Stmt C A ctl K abs img) :
    CryptoVerification.Cli.LibsignalSpqrV1.TryDecryptV1RunStmt C A ctl K abs img := by
  intro hHooks hSpqr himg
  exact CryptoVerification.Cli.LibsignalSpqrV1.M4.tryDecryptT_run_of_seamW C A ctl (spqrV1 C.F K) abs img hHooks himg
    (spqrRecvOkWT_of_v1 C A ctl K abs img hRecvV1 hHooks hSpqr himg)
    (generateKeys_okW C A ctl (spqrV1 C.F K) abs img hHooks himg)
    (CryptoVerification.Cli.LibsignalSpqrV1.M4.pqRecvDerive_okWT img C A ctl (spqrV1 C.F K) abs)

end CryptoVerification.LibsignalSpqrV1.M4
