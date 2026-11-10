/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhErr
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Fetch
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhHChain
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegDhErr
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhCc1
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhErr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Trap-at-RNG DH Ratchet `create_chain` #1 & #2 Branch Sub-Segments

Proves `s3_recv_create_chain_trap`, `s3_cc2_ok_branch_trap`, and `s3_cc2_err_branch_trap` for
`try_decrypt_with_state::<signal_session_handshake::Coins>` on `trTrapProgAt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.DecryptPq

open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Step `+0x500 → +0x70c` (or `+0x30c` `ErrTailState` on `.error .invalidKeyAgreement`, or panic):
when `tr.ratchet.senderChain = some sc`, prepares the arguments for `RootKey::create_chain` #1,
zeros `tr.ratchet.rootKey` on the stack, calls `RootKey::create_chain` (`+0x544`), and branches on
the result tag (`+0x548..+0x54c`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_recv_create_chain_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hcc : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CreateChainOk_trap img C A abs)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain) (R : SepProp) (s0 s : State)
    (hsc : tr.ratchet.senderChain = some sc)
    (hrk1_ne : s0.sp - 1504#64 + 0x3b0#64 ≠ 0#64)
    (hs3 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3State A ctl img x trG tr st1 R s0 s)
    (hcode : (trTrapProgAt img.base C abs).CodeLoaded s.mem) :
    match rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | .ok (rk1, rck) =>
      ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.S3AfterCc1State A ctl img x trG tr st1 rk1 rck R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))
    | .error e =>
      ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
        ((∃ trG' r1, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e 0 R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R))) := by
  obtain ⟨hpc, hmeta, hx12, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hmem⟩ := hs3
  have hentry := entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs)
    himg CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS3PC CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry at hpc
  rw [hentry] at hpc
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfr, hsym, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") :=
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  have hfn_cc : libsignalSessionCode.fnOff createChainName = 0x14d14 :=
      libsignalSessionCode_fnOff_0x14d14
  td_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) hfn 1280 72
  have hpriv_len : sc.ratchetKey.privateKey.bytes.toList.length = 32 :=
      sc.ratchetKey.privateKey.bytes.2
  have hrk_len : (keyToBytes32 tr.ratchet.rootKey).length = 32 := length_keyToBytes32 _
  obtain ⟨p0, hp0⟩ : ∃ v, pack64 (sc.ratchetKey.privateKey.bytes.toList.take 8) = v := ⟨_, rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ v, pack64 ((sc.ratchetKey.privateKey.bytes.toList.drop 8).take 8) = v := ⟨_,
      rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ v, pack64 ((sc.ratchetKey.privateKey.bytes.toList.drop 16).take 8) = v :=
      ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ v, pack64 (sc.ratchetKey.privateKey.bytes.toList.drop 24) = v := ⟨_, rfl⟩
  obtain ⟨k0, hk0⟩ : ∃ v, pack64 ((keyToBytes32 tr.ratchet.rootKey).take 8) = v := ⟨_, rfl⟩
  obtain ⟨k1, hk1⟩ : ∃ v, pack64 (((keyToBytes32 tr.ratchet.rootKey).drop 8).take 8) = v := ⟨_, rfl⟩
  obtain ⟨k2, hk2⟩ : ∃ v, pack64 (((keyToBytes32 tr.ratchet.rootKey).drop 16).take 8) = v := ⟨_,
      rfl⟩
  obtain ⟨k3, hk3⟩ : ∃ v, pack64 ((keyToBytes32 tr.ratchet.rootKey).drop 24) = v := ⟨_, rfl⟩
  have hsc_split : ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain
      trG.ratchet.senderPad) =
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗
       ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((sp + 0x74#64) ↦₆₄ p0) ∗
       ((sp + 0x7c#64) ↦₆₄ p1) ∗
       ((sp + 0x84#64) ↦₆₄ p2) ∗
       ((sp + 0x8c#64) ↦₆₄ p3) ∗
       ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey)) := by
    rw [hsc, show sp + 0x38#64 + 24#64 = sp + 0x50#64 by bv_arith,
        optSenderChainBytes_some_split sp sc trG.ratchet.senderPad,
        pointsTo_32_as_four_64 (sp + 0x74#64) sc.ratchetKey.privateKey.bytes.toList hpriv_len,
        hp0, hp1, hp2, hp3,
        show sp + 0x74#64 + 8#64 = sp + 0x7c#64 by bv_arith,
        show sp + 0x74#64 + 16#64 = sp + 0x84#64 by bv_arith,
        show sp + 0x74#64 + 24#64 = sp + 0x8c#64 by bv_arith]
    ac_rfl
  have hrk_split : ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) =
      (((sp + 0xb8#64) ↦₆₄ k0) ∗
       ((sp + 0xc0#64) ↦₆₄ k1) ∗
       ((sp + 0xc8#64) ↦₆₄ k2) ∗
       ((sp + 0xd0#64) ↦₆₄ k3)) := by
    rw [show sp + 0x38#64 + 128#64 = sp + 0xb8#64 by bv_arith,
        pointsTo_32_as_four_64 (sp + 0xb8#64) (keyToBytes32 tr.ratchet.rootKey) hrk_len,
        hk0, hk1, hk2, hk3,
        show sp + 0xb8#64 + 8#64 = sp + 0xc0#64 by bv_arith,
        show sp + 0xb8#64 + 16#64 = sp + 0xc8#64 by bv_arith,
        show sp + 0xb8#64 + 24#64 = sp + 0xd0#64 by bv_arith]
  unfold trAt ratchetAt at hmem
  rw [hsc_split, hrk_split, split_140_for_cc1 sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u3c8, u3c0, u3b8, u3b0, u3a8, u3a0, u398, u390, hmem⟩
  have hwp1 : SepWP (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64)) s
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗
       ((sp + 0x74#64) ↦₆₄ p0) ∗
       ((sp + 0x7c#64) ↦₆₄ p1) ∗
       ((sp + 0x84#64) ↦₆₄ p2) ∗
       ((sp + 0x8c#64) ↦₆₄ p3) ∗
       ((sp + 0xb8#64) ↦₆₄ k0) ∗
       ((sp + 0xc0#64) ↦₆₄ k1) ∗
       ((sp + 0xc8#64) ↦₆₄ k2) ∗
       ((sp + 0xd0#64) ↦₆₄ k3) ∗
       ((sp + 0x390#64) ↦₆₄ u390) ∗
       ((sp + 0x398#64) ↦₆₄ u398) ∗
       ((sp + 0x3a0#64) ↦₆₄ u3a0) ∗
       ((sp + 0x3a8#64) ↦₆₄ u3a8) ∗
       ((sp + 0x3b0#64) ↦₆₄ u3b0) ∗
       ((sp + 0x3b8#64) ↦₆₄ u3b8) ∗
       ((sp + 0x3c0#64) ↦₆₄ u3c0) ∗
       ((sp + 0x3c8#64) ↦₆₄ u3c8))
      (fun sc1 P_c1 =>
        sc1.sp = s0.sp - 1504#64 ∧
        sc1.readReg64 .x0 = s0.sp - 1504#64 + 0x3b0#64 ∧
        sc1.readReg64 .x1 = x.msgA + 56#64 ∧
        sc1.readReg64 .x2 = s0.sp - 1504#64 + 0x390#64 ∧
        sc1.readReg64 .x8 = s0.sp - 1504#64 + 0x190#64 ∧
        sc1.readReg64 .x19 = x.ret ∧
        sc1.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64 ∧
        sc1.readReg64 .x21 = x.ss ∧
        sc1.readReg64 .x22 = x.msgA ∧
        sc1.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64 ∧
        (sc1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        sc1.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64 ∧
        sc1.readReg64 .x26 = s0.sp - 1504#64 + 0x2c0#64 ∧
        sc1.readReg64 .x27 = s0.sp - 1504#64 + 0x38#64 ∧
        sc1.readReg64 .x28 = s0.sp - 1504#64 + 0x2c0#64 ∧
        sc1.readReg64 .x29 = s0.sp - 96#64 ∧
        sc1.readReg64 .x30 =
          (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 1352#64 ∧
        sc1.trace = s0.trace ∧
        calleeSavedVRegs sc1 = calleeSavedVRegs s0 ∧
        (∀ m R, (m ⊨ P_c1 ∗ R) →
          (m ⊨ (((sp + 0x50#64) ↦₃₂ 1#32) ∗
                ((sp + 0x74#64) ↦₆₄ p0) ∗
                ((sp + 0x7c#64) ↦₆₄ p1) ∗
                ((sp + 0x84#64) ↦₆₄ p2) ∗
                ((sp + 0x8c#64) ↦₆₄ p3) ∗
                ((sp + 0xb8#64) ↦₆₄ 0#64) ∗
                ((sp + 0xc0#64) ↦₆₄ 0#64) ∗
                ((sp + 0xc8#64) ↦₆₄ 0#64) ∗
                ((sp + 0xd0#64) ↦₆₄ 0#64) ∗
                ((sp + 0x390#64) ↦₆₄ p0) ∗
                ((sp + 0x398#64) ↦₆₄ p1) ∗
                ((sp + 0x3a0#64) ↦₆₄ p2) ∗
                ((sp + 0x3a8#64) ↦₆₄ p3) ∗
                ((sp + 0x3b0#64) ↦₆₄ k0) ∗
                ((sp + 0x3b8#64) ↦₆₄ k1) ∗
                ((sp + 0x3c0#64) ↦₆₄ k2) ∗
                ((sp + 0x3c8#64) ↦₆₄ k3)) ∗ R))) := by
    dsimp only [trTrapProgAt] at *
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
    wp_steps
    refine SepWP.done (by change entry + bv% ((2^64 + ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
        entry + bv% ((2^64 + ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64); bv_omega) (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [sp], by simp, by simp [sp], by simp [sp],
       by simp [hx19], by simp [hx20, sp], by simp [hx21], by simp [hx22], by simp [hx23, sp],
       by simp [hx24], by simp [hx25, sp], by simp [sp], by simp [hx27, sp],
       by simp [hx28, sp], by simp [hx29], rfl, by simp [htrace], by simp [arm64_norm, hvregs],
       fun m R hm => ?_⟩
    arm64_sep_close
  have hmem_framed : s.mem ⊨
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗
       ((sp + 0x74#64) ↦₆₄ p0) ∗
       ((sp + 0x7c#64) ↦₆₄ p1) ∗
       ((sp + 0x84#64) ↦₆₄ p2) ∗
       ((sp + 0x8c#64) ↦₆₄ p3) ∗
       ((sp + 0xb8#64) ↦₆₄ k0) ∗
       ((sp + 0xc0#64) ↦₆₄ k1) ∗
       ((sp + 0xc8#64) ↦₆₄ k2) ∗
       ((sp + 0xd0#64) ↦₆₄ k3) ∗
       ((sp + 0x390#64) ↦₆₄ u390) ∗
       ((sp + 0x398#64) ↦₆₄ u398) ∗
       ((sp + 0x3a0#64) ↦₆₄ u3a0) ∗
       ((sp + 0x3a8#64) ↦₆₄ u3a8) ∗
       ((sp + 0x3b0#64) ↦₆₄ u3b0) ∗
       ((sp + 0x3b8#64) ↦₆₄ u3b8) ∗
       ((sp + 0x3c0#64) ↦₆₄ u3c0) ∗
       ((sp + 0x3c8#64) ↦₆₄ u3c8)) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       (⌜∀ sc', tr.ratchet.senderChain = some sc' →
          Ratchet.clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
        (⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
          trG.ratchet.senderPad.length = 100 ∧ tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
         vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
           (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
         ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
         ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
         ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
         ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
         memRegion (sp + 0x38#64 + 172#64) 4) ∗
        vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
        ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
        ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 72 ∗
       memRegion (sp + 0x1d8#64) 0x1b8 ∗
       memRegion (sp + 0x3d0#64) 0x1b0 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hmem
  obtain ⟨sc1, hsteps1, ⟨hpcc1, hrunc1, P_c1, hmem_c1, hsp_c1, hx0_c1, hx1_c1, hx2_c1, hx8_c1,
    hx19_c1, hx20_c1, hx21_c1, hx22_c1, hx23_c1, hx24_c1, hx25_c1, hx26_c1, hx27_c1, hx28_c1,
    hx29_c1, hx30_c1, htrace_c1, hvregs_c1, hent_c1⟩ | ⟨_, _hoom⟩⟩ :=
    hwp1.elim hmem_framed hcode
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hsp_al_c1 : sc1.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_c1, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hfr_c1 : img.FrozenLoaded sc1 := hsteps1.frozenLoaded hfr
  have hsym_c1 : sc1.symtab = img.symtab := hsteps1.symtab_eq.trans hsym
  have hpc_cc1 : sc1.pc = (trTrapProgAt img.base C abs).fnAddr createChainName := by
    rw [hpcc1]
    dsimp only [trTrapProgAt]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, hfn_cc]
    bv_arith
  have hmem_c1_0 := hent_c1 sc1.mem _ hmem_c1
  have h74_fold : ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) =
      (((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗
       ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x74#64) sc.ratchetKey.privateKey.bytes.toList hpriv_len,
        hp0, hp1, hp2, hp3,
        show sp + 0x74#64 + 8#64 = sp + 0x7c#64 by bv_arith,
        show sp + 0x74#64 + 16#64 = sp + 0x84#64 by bv_arith,
        show sp + 0x74#64 + 24#64 = sp + 0x8c#64 by bv_arith]
  have h390_fold : ((sp + 0x390#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) =
      (((sp + 0x390#64) ↦₆₄ p0) ∗ ((sp + 0x398#64) ↦₆₄ p1) ∗
       ((sp + 0x3a0#64) ↦₆₄ p2) ∗ ((sp + 0x3a8#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x390#64) sc.ratchetKey.privateKey.bytes.toList hpriv_len,
        hp0, hp1, hp2, hp3,
        show sp + 0x390#64 + 8#64 = sp + 0x398#64 by bv_arith,
        show sp + 0x390#64 + 16#64 = sp + 0x3a0#64 by bv_arith,
        show sp + 0x390#64 + 24#64 = sp + 0x3a8#64 by bv_arith]
  have h3b0_fold : ((sp + 0x3b0#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) =
      (((sp + 0x3b0#64) ↦₆₄ k0) ∗ ((sp + 0x3b8#64) ↦₆₄ k1) ∗
       ((sp + 0x3c0#64) ↦₆₄ k2) ∗ ((sp + 0x3c8#64) ↦₆₄ k3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x3b0#64) (keyToBytes32 tr.ratchet.rootKey) hrk_len,
        hk0, hk1, hk2, hk3,
        show sp + 0x3b0#64 + 8#64 = sp + 0x3b8#64 by bv_arith,
        show sp + 0x3b0#64 + 16#64 = sp + 0x3c0#64 by bv_arith,
        show sp + 0x3b0#64 + 24#64 = sp + 0x3c8#64 by bv_arith]
  have hb8_zero : ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 (0 : RootKey)) =
      (((sp + 0xb8#64) ↦₆₄ 0#64) ∗ ((sp + 0xc0#64) ↦₆₄ 0#64) ∗
       ((sp + 0xc8#64) ↦₆₄ 0#64) ∗ ((sp + 0xd0#64) ↦₆₄ 0#64)) := by
    rw [show sp + 0x38#64 + 128#64 = sp + 0xb8#64 by bv_arith,
        ← pointsTo64_zero_32 (sp + 0xb8#64),
        show sp + 0xb8#64 + 8#64 = sp + 0xc0#64 by bv_arith,
        show sp + 0xb8#64 + 16#64 = sp + 0xc8#64 by bv_arith,
        show sp + 0xb8#64 + 24#64 = sp + 0xd0#64 by bv_arith]
  have htr0_fold : trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey :=
      (0 : RootKey) } } =
      (⌜∀ sc', tr.ratchet.senderChain = some sc' →
          Ratchet.clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
       (⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
         trG.ratchet.senderPad.length = 100 ∧ tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
        vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
          (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
        (((sp + 0x50#64) ↦₃₂ 1#32) ∗
         ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
         (((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗
          ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3)) ∗
         ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey)) ∗
        (((sp + 0xb8#64) ↦₆₄ 0#64) ∗ ((sp + 0xc0#64) ↦₆₄ 0#64) ∗
         ((sp + 0xc8#64) ↦₆₄ 0#64) ∗ ((sp + 0xd0#64) ↦₆₄ 0#64)) ∗
        ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
        ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
        memRegion (sp + 0x38#64 + 172#64) 4) ∗
       vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
       ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
       ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) := by
    unfold trAt ratchetAt
    dsimp only
    rw [hsc, show sp + 0x38#64 + 24#64 = sp + 0x50#64 by bv_arith,
        optSenderChainBytes_some_split sp sc trG.ratchet.senderPad,
        h74_fold, hb8_zero]
  let ccG1 : CreateChainGhost :=
    { rkA := sp + 0x3b0#64
      rk := tr.ratchet.rootKey
      theirA := x.msgA + 56#64
      their := x.msg.senderRatchetKey
      ourA := sp + 0x390#64
      our := sc.ratchetKey.privateKey
      ret := sp + 0x190#64 }
  let Frame1 : SepProp :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1d8#64) 0x1b8 ∗
    memRegion (sp + 0x3d0#64) 0x1b0 ∗
    protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗
    signalMessageRestAt A x.msgG x.msgA x.msg ∗
    CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
    logOff img ∗
    stackAt (sp - BitVec.ofNat 64 createChainStack) (tryDecryptSubStack - createChainStack) ∗
    tryDecryptSavedRegs s0.sp s0
  have hpre_cc1 : sc1.mem ⊨ ((createChainSpec C A).inImage img).pre ccG1 sc1 ∗ (Frame1 ∗ R) := by
    dsimp only [createChainSpec, Spec.inImage, ccG1, Frame1]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfr_c1, hsym_c1⟩, ⟨hx0_c1, hx1_c1, hx2_c1, hx8_c1, hrk1_ne⟩, ?_⟩
    rw [htr0_fold, h390_fold, h3b0_fold, show sc1.sp = sp from hsp_c1]
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap at hmem_c1_0
    rw [signalMessageAt_senderRatchetKey A x.msgG x.msgA x.msg,
        show s0.sp - 1504#64 = sp from rfl,
        stackAt_subStack_createChain sp] at hmem_c1_0
    exact Eq.mp (congrArg (sc1.mem ⊨ ·) (by ac_rfl)) hmem_c1_0
  obtain ⟨sm, hsteps_cc1, hout_cc1, -⟩ :=
    subroutine_ok.no_fault_before_outcome hcc ccG1 (Frame1 ∗ R) sc1 hpc_cc1 hrunc1 hpre_cc1 hsp_al_c1
      (hsteps1.codeLoaded hcode)
  have hsteps12 : Steps (trTrapProgAt img.base C abs) s sm :=
      Steps.trans hsteps1 hsteps_cc1
  rcases hout_cc1 with ⟨hret_m, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, -, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
  · -- Normal return from `RootKey::create_chain` #1
    have hpcm : sm.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 1352#64 :=
      hret_m.1.trans hx30_c1
    have hrunm : sm.status = .Running := hret_m.2.2
    dsimp only [createChainSpec, Spec.inImage, ccG1] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hfr_m : img.FrozenLoaded sm := hsteps_cc1.frozenLoaded hfr_c1
    have hsym_m : sm.symtab = img.symtab := hsteps_cc1.symtab_eq.trans hsym_c1
    have htrace_m0 := hpost.1
    have hpost := hpost.2
    have htrace_m : sm.trace = s0.trace := htrace_m0.trans htrace_c1
    have hsp_m : sm.sp = s0.sp - 1504#64 := hspm.trans hsp_c1
    have hsp_al_m : sm.spAligned = true := by
      unfold State.spAligned at hsp_al_c1 ⊢
      rw [hspm]
      exact hsp_al_c1
    have hx19_m : sm.readReg64 .x19 = x.ret := hcsm.1.trans hx19_c1
    have hx20_m : sm.readReg64 .x20 = sp + 0x140#64 := hcsm.2.1.trans hx20_c1
    have hx21_m : sm.readReg64 .x21 = x.ss := hcsm.2.2.1.trans hx21_c1
    have hx22_m : sm.readReg64 .x22 = x.msgA := hcsm.2.2.2.1.trans hx22_c1
    have hx23_m : sm.readReg64 .x23 = sp + 0x500#64 := hcsm.2.2.2.2.1.trans hx23_c1
    have hx24_m : (sm.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType := by
      rw [hcsm.2.2.2.2.2.1]; exact hx24_c1
    have hx25_m : sm.readReg64 .x25 = sp + 0x190#64 := hcsm.2.2.2.2.2.2.1.trans hx25_c1
    have hx26_m : sm.readReg64 .x26 = sp + 0x2c0#64 := hcsm.2.2.2.2.2.2.2.1.trans hx26_c1
    have hx27_m : sm.readReg64 .x27 = sp + 0x38#64 := hcsm.2.2.2.2.2.2.2.2.1.trans hx27_c1
    have hx28_m : sm.readReg64 .x28 = sp + 0x2c0#64 := hcsm.2.2.2.2.2.2.2.2.2.1.trans hx28_c1
    have hx29_m : sm.readReg64 .x29 = s0.sp - 96#64 := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hx29_c1
    have hmeta_m : tryDecryptMidMeta img s0 sm :=
      ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m,
        hfr_m, hsym_m, hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs_c1⟩
    have hpost_grouped : sm.mem ⊨
        (memRegion (sp + 0x1d8#64) 0x1b8 ∗
         ((sp + 0x390#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
         ((sp + 0x3b0#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
         memRegion (sp + 0x3d0#64) 0x1b0) ∗
        (memRegion (sp + 0x140#64) 0x50 ∗
         createChainResultAt (sp + 0x190#64) (rootCreateChain C tr.ratchet.rootKey
           x.msg.senderRatchetKey sc.ratchetKey.privateKey) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey :=
           (0 : RootKey) } } ∗
         memRegion x.ret 48 ∗
         memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
         memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
      dsimp only [Frame1] at hpost
      rw [show sc1.sp = sp from hsp_c1] at hpost
      unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap
      rw [signalMessageAt_senderRatchetKey A x.msgG x.msgA x.msg,
          show s0.sp - 1504#64 = sp from rfl,
          stackAt_subStack_createChain sp]
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hpost
    have hpost_folded :=
      Satisfies.mono (sepConj_mono_left (fold_390_3b0_to_memRegion sp _ _ hpriv_len hrk_len))
        hpost_grouped
    unfold rootCreateChain at hpost_folded ⊢
    cases hcc1 : Ratchet.createChain C.F C.X tr.ratchet.rootKey x.msg.senderRatchetKey.bytes
        sc.ratchetKey.privateKey.bytes with
    | none =>
      rw [hcc1] at hpost_folded
      dsimp only [hcc1] at hpost_folded ⊢
      let Rest_err : SepProp :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey :=
          (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗
        memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R
      have hmem_err : sm.mem ⊨
          memRegion (sp + 0x140#64) 0x50 ∗
          createChainResultAt (sp + 0x190#64) (.error .invalidKeyAgreement) ∗
          memRegion (sp + 0x1d8#64) 0x3a8 ∗ Rest_err :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_err]; ac_rfl)) hpost_folded
      obtain ⟨s', hsteps2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_cc1_err_branch_trap (C := C) (A := A) (abs := abs)
          himg Rest_err s0 sm hpcm hmeta_m hx20_m hx23_m hx25_m hx26_m hmem_err
          (hsteps12.codeLoaded hcode)
      refine ⟨s', Steps.trans hsteps12 hsteps2, Or.inl ⟨trG, { tr.ratchet with rootKey :=
          (0 : RootKey) }, ?_⟩⟩
      refine ⟨hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s', ?_⟩
      dsimp only [Rest_err] at hmems'
      have hsp38_ent :
          (memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA)) ⊢
          memRegion sp 0x38 := by
        rw [memRegion_split' (b := sp) (b' := sp + 0x20#64) (n := 0x20) (k :=
            0x18) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x20#64) (b' := sp + 0x28#64) (n := 0x8) (k :=
              0x10) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x28#64) (b' := sp + 0x2c#64) (n := 0x4) (k :=
              0xc) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x2c#64) (b' := sp + 0x30#64) (n := 0x4) (k :=
              0x8) rfl (by bv_arith) (by decide)]
        exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo32_entails_memRegion _ _)
            (sepConj_mono_right (pointsTo64_entails_memRegion _ _))))
      have hmems1 : s'.mem ⊨
          (memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA)) ∗
          (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey :=
             (0 : RootKey) } } ∗
           memRegion x.ret 48 ∗
           memRegion (sp + 0x140#64) 0x28 ∗
           speBodyAt A (utf8 "decrypt") (sp + 0x168#64) .invalidKeyAgreement ∗
           memRegion (sp + 0x190#64) 0x3f0 ∗
           CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :=
        Eq.mp (congrArg (s'.mem ⊨ ·) (by dsimp only [sp] at hmems' ⊢; ac_rfl)) hmems'
      have hmems2 := Satisfies.mono (sepConj_mono_left hsp38_ent) hmems1
      dsimp only [sp] at hmems2 ⊢
      exact Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hmems2
    | some p1 =>
      rcases p1 with ⟨rk1, rckKey⟩
      rw [hcc1] at hpost_folded
      dsimp only [hcc1] at hpost_folded ⊢
      let Rest_ok : SepProp :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey :=
          (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗
        memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
        memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x1d8#64) 0x3a8 ∗
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R
      have hmem_ok : sm.mem ⊨
          createChainResultAt (sp + 0x190#64) (.ok (rk1, ⟨rckKey, 0⟩)) ∗ Rest_ok :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_ok]; ac_rfl)) hpost_folded
      obtain ⟨s', hsteps2, hpcs', hmetas', hcss', hmems'⟩ :=
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_cc1_ok_branch_trap (C := C) (abs := abs)
          himg rk1 ⟨rckKey, 0⟩ Rest_ok s0 sm hpcm hmeta_m hmem_ok
          (hsteps12.codeLoaded hcode)
      refine ⟨s', Steps.trans hsteps12 hsteps2, Or.inl ?_⟩
      refine ⟨hpcs', hmetas',
        hcss'.1.trans hx19_m,
        hcss'.2.1.trans hx20_m,
        hcss'.2.2.1.trans hx21_m,
        hcss'.2.2.2.1.trans hx22_m,
        hcss'.2.2.2.2.1.trans hx23_m,
        by rw [hcss'.2.2.2.2.2.1]; exact hx24_m,
        hcss'.2.2.2.2.2.2.1.trans hx25_m,
        hcss'.2.2.2.2.2.2.2.1.trans hx26_m,
        hcss'.2.2.2.2.2.2.2.2.1.trans hx27_m,
        hcss'.2.2.2.2.2.2.2.2.2.1.trans hx28_m, ?_⟩
      dsimp only [Rest_ok, sp] at hmems' ⊢
      exact Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hmems'
  · -- Panic in `RootKey::create_chain` #1
    have hpan_td := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.onPanic_of_createChain (ctl := ctl) (S := S) (x := x) htrace_c1 hpost
    cases rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | ok p1 =>
      rcases p1 with ⟨rk1, rck⟩
      exact ⟨sm, hsteps12, Or.inr ⟨hpan, hpan_td⟩⟩
    | error e =>
      exact ⟨sm, hsteps12, Or.inr ⟨hpan, hpan_td⟩⟩
  · -- Impossible `.Exited` case
    dsimp only [createChainSpec, Spec.inImage] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

/-- Success branch after `RootKey::create_chain` #2 (`+0x7d8 → +0x8ac`): when `[sp + 0x190]`
holds tag `0#32` (`.ok (finalRootKey, senderChainKey)`), `subs wzr, w8, #1; b.ne +0xcc` branches to
`segS3CommitPC img` (`+0x8ac` = `entry + 2220`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_cc2_ok_branch_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (finalRootKey : RootKey) (senderChainKey : ChainKey) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 2008#64)
    (hmeta : tryDecryptMidMeta img s0 s)
    (hmem : s.mem ⊨
      createChainResultAt (s0.sp - 1504#64 + 0x190#64) (.ok (finalRootKey, senderChainKey)) ∗ Rest)
    (hcode : (trTrapProgAt img.base C abs).CodeLoaded s.mem) :
    ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
      s'.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.segS3CommitPC img ∧
      tryDecryptMidMeta img s0 s' ∧
      CalleeSavedPreserved s s' ∧
      (s'.mem ⊨
        ((s0.sp - 1504#64 + 0x190#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 1504#64 + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
        ((s0.sp - 1504#64 + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗ Rest) := by
  have hentry := entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs)
    himg CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfr, hsym, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") :=
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  td_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) hfn 2008 12
  dsimp only [createChainResultAt] at hmem
  rw [show sp + 0x190#64 + 4#64 = sp + 0x194#64 by bv_arith,
      show sp + 0x190#64 + 0x24#64 = sp + 0x1b4#64 by bv_arith] at hmem
  have hwp : SepWP (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 2220#64) s
      ((sp + 0x190#64) ↦₃₂ 0#32)
      (fun sm P_m =>
        sm.sp = s0.sp - 1504#64 ∧
        CalleeSavedPreserved s sm ∧
        sm.trace = s0.trace ∧
        (∀ m R, (m ⊨ P_m ∗ R) → (m ⊨ ((sp + 0x190#64) ↦₃₂ 0#32) ∗ R))) := by
    dsimp only [trTrapProgAt] at *
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  have hmem_framed : s.mem ⊨
      ((sp + 0x190#64) ↦₃₂ 0#32) ∗
      (((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗ Rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hmem
  obtain ⟨sm, hsteps1, ⟨hpcm, hrunm, P_m, hmem_m, hsp_m, hcs_m, htrace_m, hent_m⟩ | ⟨_, _hoom⟩⟩ :=
    hwp.elim hmem_framed hcode
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hpcm' : sm.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.segS3CommitPC img := by
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.segS3CommitPC CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry; rw [hentry]; exact hpcm
  have hx29_m : sm.readReg64 .x29 = s0.sp - 96#64 := hcs_m.2.2.2.2.2.2.2.2.2.2.1.trans hx29
  have hmeta_m : tryDecryptMidMeta img s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m,
      hsteps1.frozenLoaded hfr, hsteps1.symtab_eq.trans hsym,
      hcs_m.2.2.2.2.2.2.2.2.2.2.2.trans hvregs⟩
  have hmem_m0 := hent_m sm.mem _ hmem_m
  exact ⟨sm, hsteps1, hpcm', hmeta_m, hcs_m, Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmem_m0⟩

/-- Error branch after `RootKey::create_chain` #2 (`+0x7d8 → +0x7f8 → +0x30c`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_cc2_err_branch_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (msgW : BitVec 32) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 2008#64)
    (hmeta : tryDecryptMidMeta img s0 s)
    (hx20 : s.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hx26 : s.readReg64 .x26 = s0.sp - 1504#64 + 0x2c0#64)
    (hmem : s.mem ⊨
      ((s0.sp - 1504#64 + 0x1c#64) ↦₃₂ msgW) ∗
      memRegion (s0.sp - 1504#64 + 0x140#64) 0x50 ∗
      createChainResultAt (s0.sp - 1504#64 + 0x190#64) (.error .invalidKeyAgreement) ∗
      memRegion (s0.sp - 1504#64 + 0x1d8#64) 0x3a8 ∗ Rest)
    (hcode : (trTrapProgAt img.base C abs).CodeLoaded s.mem) :
    ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
      s'.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC img ∧
      tryDecryptMidMeta img s0 s' ∧
      s'.readReg64 .x19 = s.readReg64 .x19 ∧
      s'.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64 ∧
      s'.readReg64 .x26 = speTag .invalidKeyAgreement ∧
      (s'.mem ⊨
        ((s0.sp - 1504#64 + 0x1c#64) ↦₃₂ msgW) ∗
        memRegion (s0.sp - 1504#64 + 0x140#64) 0x28 ∗
        speBodyAt A (utf8 "decrypt") (s0.sp - 1504#64 + 0x168#64) .invalidKeyAgreement ∗
        memRegion (s0.sp - 1504#64 + 0x190#64) 0x3f0 ∗ Rest) := by
  have hentry := entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs)
    himg CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfr, hsym, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") :=
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  td_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) hfn 2008 32
  dsimp only [createChainResultAt] at hmem
  rw [show sp + 0x190#64 + 4#64 = sp + 0x194#64 by bv_arith,
      show sp + 0x190#64 + 8#64 = sp + 0x198#64 by bv_arith,
      show sp + 0x190#64 + 16#64 = sp + 0x1a0#64 by bv_arith,
      split_1a0_56 sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u1c4, u1bc, u1b4, u1b0, u1a8, u1a0, hmem⟩
  have hwp : SepWP (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 2040#64) s
      (((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x190#64) ↦₃₂ 1#32) ∗
       ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗
       ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
       ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗
       ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
       ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗
       ((sp + 0x1c4#64) ↦₃₂ u1c4))
      (fun sm P_m =>
        sm.sp = s0.sp - 1504#64 ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64 ∧
        sm.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64 ∧
        sm.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64 ∧
        sm.readReg64 .x26 = s0.sp - 1504#64 + 0x2c0#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        (∀ m R, (m ⊨ P_m ∗ R) →
          (m ⊨ (((sp + 0x1c#64) ↦₃₂ msgW) ∗
                ((sp + 0x190#64) ↦₃₂ 1#32) ∗
                ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗
                ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
                ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗
                ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
                ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗
                ((sp + 0x1c4#64) ↦₃₂ u1c4)) ∗ R))) := by
    dsimp only [trTrapProgAt] at *
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], rfl, by simp [hx20, sp], by simp [hx23, sp],
       by simp [hx25, sp], by simp [hx26, sp], by simp [htrace], by simp [arm64_norm, hvregs],
       fun m R hm => ?_⟩
    arm64_sep_close
  have hmem_framed : s.mem ⊨
      (((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x190#64) ↦₃₂ 1#32) ∗
       ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗
       ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
       ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗
       ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
       ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗
       ((sp + 0x1c4#64) ↦₃₂ u1c4)) ∗
      (memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x194#64) 4 ∗
       ((sp + 0x198#64) ↦₆₄ speWord 10) ∗
       memRegion (sp + 0x1c8#64) 16 ∗
       memRegion (sp + 0x1d8#64) 0x3a8 ∗ Rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hmem
  obtain ⟨sm, hsteps1, ⟨hpcm, hrunm, P_m, hmem_m, hsp_m, hx29_m, hx19_m, hx20_m, hx23_m, hx25_m,
      hx26_m, htrace_m, hvregs_m, hent_m⟩ | ⟨_, _hoom⟩⟩ :=
    hwp.elim hmem_framed hcode
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hpcm' : sm.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x7f8#64 := by
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry; rw [hentry]; exact hpcm
  have hmeta_m : tryDecryptMidMeta img s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hsteps1.frozenLoaded hfr,
      hsteps1.symtab_eq.trans hsym, hvregs_m⟩
  have hmem_m0 := hent_m sm.mem _ hmem_m
  have hmem_m1 : sm.mem ⊨
      (memRegion (sp + 0x140#64) 0x50 ∗
       ((sp + 0x190#64) ↦₃₂ 1#32) ∗
       memRegion (sp + 0x194#64) 4 ∗
       ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗
       ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
       ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗
       ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
       ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗
       ((sp + 0x1c4#64) ↦₃₂ u1c4) ∗
       memRegion (sp + 0x1c8#64) 16 ∗
       memRegion (sp + 0x1d8#64) 0x3a8) ∗
      (((sp + 0x198#64) ↦₆₄ speWord 10) ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗ Rest) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmem_m0
  have hmem_m2 :=
      Satisfies.mono (sepConj_mono_left (fold_for_7f8 sp 1#32 u1a0 u1a8 u1b4 u1bc u1b0 u1c4))
      hmem_m1
  have hmem_m3 : sm.mem ⊨
      memRegion (sp + 0x140#64) 0x58 ∗
      ((sp + 0x198#64) ↦₆₄ speWord 10) ∗
      memRegion (sp + 0x1a0#64) 0x3e0 ∗ (((sp + 0x1c#64) ↦₃₂ msgW) ∗ Rest) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmem_m2
  obtain ⟨s', hsteps2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_err_tail_from_7f8_trap (C := C) (A := A) (abs := abs)
      himg (((sp + 0x1c#64) ↦₃₂ msgW) ∗
        Rest) s0 sm hpcm' hmeta_m hx20_m hx23_m hx25_m hx26_m hmem_m3
      (hsteps1.codeLoaded hcode)
  exact ⟨s', Steps.trans hsteps1 hsteps2, hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s',
    Eq.mp (congrArg (s'.mem ⊨ ·) (by dsimp only [sp] at hmems' ⊢; ac_rfl)) hmems'⟩

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB
