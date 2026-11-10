/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhHChain
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhHEvict
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhHStep12
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhHStep3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhHStep5
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHMain
import ProofLib.SepLogic.WPp

/-!
# Handshake `DecryptPq` DH Commit Sub-Segment Proof

Chains `s3_step1_2`, `s3_step3`, `s3_step4`, and `s3_step5` to establish `S3CommitSpec`
(`+0x8ac → +0x3e4`) for `try_decrypt_with_state::<signal_session_handshake::Coins>` on
`tripleRatchetProgAt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.DecryptPq

open CryptoVerification.LibsignalSession

open BS10

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace BS10

end BS10

private theorem setWidth8_zeroExtend64 (w : BitVec 32) :
    (w.zeroExtend 64).setWidth 8 = w.setWidth 8 := by
  bv_omega

/-- Top-level proof of `S3CommitSpec` (`+0x8ac → +0x3e4` or panic): chains
`s3_step1_2` (`+0x8ac → +0xa84`), `s3_step3` (`+0xa84 → +0xaf4`),
`s3_step4` (`+0xaf4 → +0xb98`), and `s3_step5` (`+0xb98 → +0x3e4`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.s3_commit_spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.S3CommitSpec img C A ctl uuidTryParse S abs := by
  intro hLoads hHooks hPkSer hToPb hGrowOne hDropChain
    x trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
    R s0 s hsc hrc_len hclamp hS3 hL
  let newChain : ReceiverChain :=
    { senderRatchetKey := x.msg.senderRatchetKey
      chainKey := some receiverChainKey
      messageKeys := [] }
  let r1 : RatchetState :=
    { tr.ratchet with
      senderChain := some ⟨newSenderKey, senderChainKey⟩
      rootKey := finalRootKey
      previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
      receiverChains :=
        RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
  let sp := s0.sp - 1504#64
  let draws := min 32 x.rest.length
  rcases hS3 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hx25, hx27, hx28, msgW, hmsgW, hm⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htr, hfrozen, hsym, hvregs⟩
  have hpc_s : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x8ac#64 :=
      by
    rw [hpc, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS3CommitPC_eq_fnAddr hLoads C ctl abs]
  dsimp only [trAt, ratchetAt, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap, signalMessageAt] at hm
  rw [hsc] at hm
  have h_sc_50_eq :
      ∀ (pad : List (BitVec 8)), pad.length = 100 →
        ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes (some sc) pad) =
        (((sp + 0x50#64) ↦₃₂ 1#32) ∗
         ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
         ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
         ((sp + 0x94#64) ↦ₛ keyToBytes32 sc.chainKey.key) ∗
         ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index)) := by
    intro pad _hpad
    rw [show sp + 0x38#64 + 24#64 = sp + 0x50#64 from add_assoc_const _ _ _ _,
        optSenderChainBytes_some_pointsTo (sp + 0x50#64) sc pad,
        show sp + 0x50#64 + 4#64 = sp + 0x54#64 from add_assoc_const _ _ _ _,
        show sp + 0x50#64 + 36#64 = sp + 0x74#64 from add_assoc_const _ _ _ _,
        show sp + 0x50#64 + 68#64 = sp + 0x94#64 from add_assoc_const _ _ _ _,
        chainKeyBytes_pointsTo (sp + 0x94#64) sc.chainKey,
        show sp + 0x94#64 + 32#64 = sp + 0xb4#64 from add_assoc_const _ _ _ _]
  have hm_pures : s.mem ⊨
      ⌜∀ sc', some sc = some sc' →
        Ratchet.clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
      ⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
        trG.ratchet.senderPad.length = 100 ∧
        tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
      ⌜macLength + 1 ≤ x.msg.serialized.length ∧
        x.msg.ciphertext.length < 2 ^ 40 ∧ x.msg.pqRatchet.length < 2 ^ 40 ∧
        x.msg.serialized.length < 2 ^ 40 ∧
        (∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
         (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
       ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes (some sc) trG.ratchet.senderPad) ∗
       ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 0) ∗
       ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
       ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
       memRegion (sp + 0x38#64 + 172#64) 4 ∗
       vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
       ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
       ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x10 ∗
       ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
       memRegion (sp + 0x1d8#64) 0xd8 ∗
       memRegion (sp + 0x2b0#64) 0x10 ∗
       memRegion (sp + 0x2c0#64) 0x110 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
       ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
       memRegion (sp + 0x440#64) 0x80 ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
       memRegion (sp + 0x4e0#64) 0xa0 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       vecU8At A x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
       boxU8At A (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
       boxU8At A (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
       ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
       optBoxU8At A (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
       ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗
       ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
       ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
       memRegion (x.msgA + 0x71#64) 7 ∗
       CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
       logOff img ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm
    dsimp only [sp, draws]
    ac_rfl
  rw [satisfies_pure_sepConj] at hm_pures
  rcases hm_pures with ⟨_hclamp_old, hm_pures⟩
  rw [satisfies_pure_sepConj] at hm_pures
  rcases hm_pures with ⟨⟨hchains_len, hpad_len, hmfj⟩, hm_pures⟩
  rw [satisfies_pure_sepConj] at hm_pures
  rcases hm_pures with ⟨hmsg_pure, hm_body⟩
  rw [h_sc_50_eq trG.ratchet.senderPad hpad_len,
      show sp + 0x38#64 + 128#64 = sp + 0xb8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 160#64 = sp + 0xd8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 168#64 = sp + 0xe0#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 172#64 = sp + 0xe4#64 from add_assoc_const _ _ _ _] at hm_body
  have hsplit_1d8 := memRegion_split (sp + 0x1d8#64) 0x60 0x78 (by decide)
  rw [show (0x60 + 0x78 : Nat) = 0xd8 from rfl,
      show sp + 0x1d8#64 + 96#64 = sp + 0x238#64 from add_assoc_const _ _ _ _] at hsplit_1d8
  have hsplit_2c0 := memRegion_split (sp + 0x2c0#64) 0x14 0xfc (by decide)
  rw [show (0x14 + 0xfc : Nat) = 0x110 from rfl,
      show sp + 0x2c0#64 + 20#64 = sp + 0x2d4#64 from add_assoc_const _ _ _ _] at hsplit_2c0
  have hsplit_440 := memRegion_split (sp + 0x440#64) 0x10 0x70 (by decide)
  rw [show (0x10 + 0x70 : Nat) = 0x80 from rfl,
      show sp + 0x440#64 + 16#64 = sp + 0x450#64 from add_assoc_const _ _ _ _] at hsplit_440
  have hsplit_450 := memRegion_split (sp + 0x450#64) 0x50 0x20 (by decide)
  rw [show (0x50 + 0x20 : Nat) = 0x70 from rfl,
      show sp + 0x450#64 + 80#64 = sp + 0x4a0#64 from add_assoc_const _ _ _ _] at hsplit_450
  have hsplit_4e0 := memRegion_split (sp + 0x4e0#64) 0x20 0x80 (by decide)
  rw [show (0x20 + 0x80 : Nat) = 0xa0 from rfl,
      show sp + 0x4e0#64 + 32#64 = sp + 0x500#64 from add_assoc_const _ _ _ _] at hsplit_4e0
  have hsplit_500 := memRegion_split (sp + 0x500#64) 0x60 0x20 (by decide)
  rw [show (0x60 + 0x20 : Nat) = 0x80 from rfl,
      show sp + 0x500#64 + 96#64 = sp + 0x560#64 from add_assoc_const _ _ _ _] at hsplit_500
  have hstk_pb := stackAt_split_from sp tryDecryptSubStack chainKeyToPbStack (by decide) (by decide)
  rw [hsplit_1d8, hsplit_2c0, hsplit_440, hsplit_450, hsplit_4e0, hsplit_500, hstk_pb] at hm_body
  let BaseFrame : SepProp :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    ((sp + 0x50#64) ↦₃₂ 1#32) ∗
    ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
    ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
    ((sp + 0x94#64) ↦ₛ keyToBytes32 sc.chainKey.key) ∗
    ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
    memRegion (sp + 0xe4#64) 4 ∗
    vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
    ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
    ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
    memRegion x.ret 48 ∗
    ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
    memRegion (sp + 0x14#64) 8 ∗
    ((sp + 0x1c#64) ↦₃₂ msgW) ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x238#64) 0x78 ∗
    memRegion (sp + 0x2b0#64) 0x10 ∗
    memRegion (sp + 0x2c0#64) 0x14 ∗
    memRegion (sp + 0x2d4#64) 0xfc ∗
    memRegion (sp + 0x3f4#64) 12 ∗
    ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
    ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
    memRegion (sp + 0x450#64) 0x50 ∗
    memRegion (sp + 0x4a0#64) 0x20 ∗
    ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
    ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
    memRegion (sp + 0x560#64) 0x20 ∗
    protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗
    vecU8At A x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
    boxU8At A (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
    boxU8At A (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
    optBoxU8At A (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
    ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗
    ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
    ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
    memRegion (x.msgA + 0x71#64) 7 ∗
    CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
    logOff img ∗
    tryDecryptSavedRegs s0.sp s0
  let gcs0 := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hsplit_sp16 := memRegion_split sp 12 4 (by decide)
  rw [show (12 + 4 : Nat) = 0x10 from rfl,
      show sp + 12#64 = sp + 0xc#64 from rfl] at hsplit_sp16
  rw [hsplit_sp16] at hm_body
  let Frame12 : SepProp :=
    vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr gcs0 ∗
    memRegion (sp + 0xc#64) 4 ∗
    memRegion (sp + 0x1d8#64) 0x60 ∗
    memRegion (sp + 0x500#64) 0x60 ∗
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
      (tryDecryptSubStack - chainKeyToPbStack) ∗
    BaseFrame
  have hm_step12 : s.mem ⊨
      (memRegion sp 12 ∗
       ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index) ∗
       ((sp + 0xb8#64) ↦ₛ keyToBytes32 0) ∗
       ((sp + 0xe0#64) ↦₃₂ tr.ratchet.previousCounter) ∗
       ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       memRegion (sp + 0x440#64) 16 ∗
       memRegion (sp + 0x4e0#64) 32 ∗
       ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
       A.pool ∗
       stackAt sp chainKeyToPbStack) ∗
      (Frame12 ∗ R) := by
    dsimp only [Frame12, BaseFrame]
    refine Satisfies.mono (Entails.of_eq ?_) hm_body
    ac_rfl
  have hreach12 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.s3_step1_2 img C A ctl S abs hHooks hPkSer hToPb
    x R Frame12 s0 s sp x.msgA sc.chainKey.index tr.ratchet.previousCounter
    finalRootKey senderChainKey receiverChainKey x.msg.senderRatchetKey
    hpc_s hrun hsp hsp_align htr hx22 hx25 hx27 hx28 hL hm_step12
  refine CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.seq hreach12 ?_
  intro s1 hkf1 hsym1 hs1
  rcases hs1 with ⟨boxPtr, srkPtr, ckPtr, pad, hsrk0, hpad, hpc1, hrun1, hsp1, hsp_align1,
    htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1, hL1, hm1⟩
  have hfrozen1 : img.FrozenLoaded s1 := hfrozen.of_keepsFrozen hkf1
  have hsym1' : s1.symtab = img.symtab := hsym1.trans hsym
  have hstk_grow := stackAt_split_from sp tryDecryptSubStack growOneStack (by decide) (by decide)
  have hsplit_1d8_32 := memRegion_split (sp + 0x1d8#64) 32 0x40 (by decide)
  rw [show (32 + 0x40 : Nat) = 0x60 from rfl,
      show sp + 0x1d8#64 + 32#64 = sp + 0x1f8#64 from add_assoc_const _ _ _ _] at hsplit_1d8_32
  have hjoin_1b0_72 := (memRegion_split (sp + 0x1b0#64) 40 32 (by decide)).symm
  rw [show (40 + 32 : Nat) = 72 from rfl,
      show sp + 0x1b0#64 + 40#64 = sp + 0x1d8#64 from add_assoc_const _ _ _ _] at hjoin_1b0_72
  have hm1_sp8 :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left (cell_to_memRegion_8 sp boxPtr))) hm1
  have hm1_prep : s1.mem ⊨
      (memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
          (tryDecryptSubStack - chainKeyToPbStack) ∗
       stackAt sp chainKeyToPbStack) ∗
      (memRegion (sp + 0x1b0#64) 40 ∗ memRegion (sp + 0x1d8#64) 32) ∗
      vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr gcs0 ∗
      memRegion sp 8 ∗
      ((sp + 8#64) ↦₃₂ sckWord16 senderChainKey) ∗
      memRegion (sp + 0xc#64) 4 ∗
      ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index) ∗
      ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
      ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some receiverChainKey) pad) ∗
      memRegion (sp + 0x1f8#64) 0x40 ∗
      ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
      ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
      ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
      ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
      memRegion (sp + 0x500#64) 0x60 ∗
      ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
      (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
      (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
      optChainKeyHeap A ⟨32#64, ckPtr⟩ (some receiverChainKey) ∗
      A.pool ∗
      BaseFrame ∗ R := by
    dsimp only [Frame12] at hm1_sp8
    rw [hsplit_1d8_32] at hm1_sp8
    refine Satisfies.mono (Entails.of_eq ?_) hm1_sp8
    ac_rfl
  rw [← hstk_pb, hstk_grow, hjoin_1b0_72, vecAt_chains_eq] at hm1_prep
  let Frame3 : SepProp :=
    memRegion sp 8 ∗
    ((sp + 8#64) ↦₃₂ sckWord16 senderChainKey) ∗
    memRegion (sp + 0xc#64) 4 ∗
    ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index) ∗
    ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
    ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
    memRegion (sp + 0x1f8#64) 0x40 ∗
    ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
    ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
    ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
    ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
    ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
    ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
    ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
    memRegion (sp + 0x500#64) 0x60 ∗
    ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
      (tryDecryptSubStack - growOneStack) ∗
    BaseFrame
  have hm_step3 : s1.mem ⊨
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs0.length) ∗
       vecBuf A 104 8 (chainAt A) trG.ratchet.chainsCap trG.ratchet.chainsPtr gcs0 ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some receiverChainKey) pad) ∗
       memRegion (sp + 0x1b0#64) 72 ∗
       (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
       optChainKeyHeap A ⟨32#64, ckPtr⟩ (some receiverChainKey) ∗
       A.pool ∗
       stackAt sp growOneStack) ∗
      (Frame3 ∗ R) := by
    dsimp only [Frame3]
    refine Satisfies.mono (Entails.of_eq ?_) hm1_prep
    ac_rfl
  have hgcs0_len : gcs0.length < 2 ^ 32 := by
    dsimp only [gcs0]
    rw [List.length_zip, hchains_len, Nat.min_self]
    exact hrc_len
  have hreach3 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.s3_step3 img C A ctl S abs hHooks hGrowOne x R Frame3 s0 s1
    sp trG.ratchet.chainsCap trG.ratchet.chainsPtr boxPtr srkPtr ckPtr gcs0
    x.msg.senderRatchetKey receiverChainKey pad hgcs0_len hpad hsrk0
    hpc1 hrun1 hsp1 hsp_align1 htr1 hfrozen1 hsym1'
    hx25_1 hx26_1 hx27_1 hx28_1 hL1 hm_step3
  refine CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.seq hreach3 ?_
  intro s2 _hkf2 _hsym2 hs2
  rcases hs2 with ⟨cap', ptr', hpc2, hrun2, hsp2, hsp_align2, htr2,
    hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx25_2, hx29_2, hvregs_2, hL2, hm2⟩
  let gcs1 := gcs0 ++ [(newChainGhost srkPtr ckPtr x.msg.senderRatchetKey, newChain)]
  have hstk_drop := stackAt_split_from sp tryDecryptSubStack dropChainStack (by decide) (by decide)
  have hjoin_1f8 := (memRegion_split (sp + 0x1f8#64) 0x40 0x78 (by decide)).symm
  rw [show (0x40 + 0x78 : Nat) = 0xb8 from rfl,
      show sp + 0x1f8#64 + 64#64 = sp + 0x238#64 from add_assoc_const _ _ _ _] at hjoin_1f8
  have hck_94 := (chainKeyBytes_pointsTo (sp + 0x94#64) sc.chainKey).symm
  rw [show sp + 0x94#64 + 32#64 = sp + 0xb4#64 from add_assoc_const _ _ _ _] at hck_94
  have hm2_prep : s2.mem ⊨
      (memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
          (tryDecryptSubStack - growOneStack) ∗
       stackAt sp growOneStack) ∗
      (memRegion (sp + 0x1f8#64) 0x40 ∗ memRegion (sp + 0x238#64) 0x78) ∗
      (((sp + 0x94#64) ↦ₛ keyToBytes32 sc.chainKey.key) ∗ ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index)) ∗
      ((sp + 0x38#64) ↦₆₄ cap') ∗
      ((sp + 0x40#64) ↦₆₄ ptr') ∗
      ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs1.length) ∗
      vecBuf A 104 8 (chainAt A) cap' ptr' gcs1 ∗
      memRegion (sp + 0x190#64) 104 ∗
      memRegion (sp + 0x500#64) 96 ∗
      memRegion sp 8 ∗
      A.pool ∗
      ((sp + 8#64) ↦₃₂ sckWord16 senderChainKey) ∗
      memRegion (sp + 0xc#64) 4 ∗
      ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
      ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
      ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
      ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
      ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
      ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      ((sp + 0x50#64) ↦₃₂ 1#32) ∗
      ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
      ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
      ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
      memRegion (sp + 0xe4#64) 4 ∗
      vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
      ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
      ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
      memRegion x.ret 48 ∗
      ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion (sp + 0x14#64) 8 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion (sp + 0x2c#64) 4 ∗
      ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x50 ∗
      memRegion (sp + 0x2b0#64) 0x10 ∗
      memRegion (sp + 0x2c0#64) 0x14 ∗
      memRegion (sp + 0x2d4#64) 0xfc ∗
      memRegion (sp + 0x3f4#64) 12 ∗
      ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      memRegion (sp + 0x450#64) 0x50 ∗
      memRegion (sp + 0x4a0#64) 0x20 ∗
      ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
      memRegion (sp + 0x560#64) 0x20 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      vecU8At A x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
      boxU8At A (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
      boxU8At A (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
      optBoxU8At A (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
      ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗
      ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
      ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
      memRegion (x.msgA + 0x71#64) 7 ∗
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
      logOff img ∗
      tryDecryptSavedRegs s0.sp s0 ∗ R := by
    dsimp only [Frame3, BaseFrame] at hm2
    refine Satisfies.mono (Entails.of_eq ?_) hm2
    ac_rfl
  rw [← hstk_grow, hstk_drop, hjoin_1f8, hck_94] at hm2_prep
  let TailFrame : SepProp :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
    ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
    ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
    memRegion (sp + 0xe4#64) 4 ∗
    vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
    ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
    ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
    memRegion x.ret 48 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗
    vecU8At A x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
    boxU8At A (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
    boxU8At A (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
    ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
    optBoxU8At A (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
    ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗
    ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
    ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
    memRegion (x.msgA + 0x71#64) 7 ∗
    CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
    logOff img ∗
    tryDecryptSavedRegs s0.sp s0
  let Step5Cells : SepProp :=
    memRegion sp 8 ∗
    ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗
    memRegion (sp + 0xc#64) 4 ∗
    ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
    memRegion (sp + 0x14#64) 8 ∗
    ((sp + 0x1c#64) ↦₃₂ msgW) ∗
    ((sp + 0x50#64) ↦₃₂ 1#32) ∗
    ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
    ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
    ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1f8#64) 0xb8 ∗
    memRegion (sp + 0x2b0#64) 0x10 ∗
    memRegion (sp + 0x2c0#64) 0x14 ∗
    memRegion (sp + 0x2d4#64) 0xfc ∗
    ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
    memRegion (sp + 0x3f4#64) 12 ∗
    ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
    ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
    ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
    ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
    memRegion (sp + 0x450#64) 0x50 ∗
    memRegion (sp + 0x4a0#64) 0x20 ∗
    ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
    ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
    ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
    ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
    ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
    ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
    memRegion (sp + 0x560#64) 0x20
  let Frame4 : SepProp :=
    ((sp + 0x38#64) ↦₆₄ cap') ∗
    Step5Cells ∗
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
      (tryDecryptSubStack - dropChainStack) ∗
    TailFrame
  have hm_step4 : s2.mem ⊨ evictActive A sp cap' ptr' gcs1 ∗ (Frame4 ∗ R) := by
    dsimp only [evictActive, Frame4, Step5Cells, TailFrame]
    refine Satisfies.mono (Entails.of_eq ?_) hm2_prep
    ac_rfl
  have hgcs1_len : gcs1.length = tr.ratchet.receiverChains.length + 1 := by
    dsimp only [gcs1, gcs0]
    rw [List.length_append, List.length_zip, hchains_len, Nat.min_self]
    rfl
  have hle4 : gcs1.length ≤ 2 ^ 32 := BS10.le_of_eq_succ_lt hgcs1_len hrc_len
  have hreach4 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.s3_step4 img C A ctl S abs hDropChain x R Frame4 s0 s2
    sp cap' ptr' gcs1 hle4 hpc2 hrun2 hsp2 hsp_align2 htr2
    (hx23_2.trans (hx23_1.trans hx23)) hx25_2 hL2 hm_step4
  refine CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.seq hreach4 ?_
  intro s3 _hkf3 _hsym3 hs3
  rcases hs3 with ⟨hpc3, hrun3, hsp3, hsp_align3, htr3,
    hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx25_3, hx29_3, hvregs_3, hL3, hm3⟩
  let Frame5 : SepProp :=
    vecAt A 104 8 (chainAt A) (sp + 0x38#64) cap' ptr' (evictGcs gcs1) ∗
    A.pool ∗
    stackAt sp tryDecryptSubStack ∗
    TailFrame
  have hm_step5 : s3.mem ⊨
      memRegion sp 8 ∗
      ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗
      memRegion (sp + 0xc#64) 4 ∗
      ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion (sp + 0x14#64) 8 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x50#64) ↦₃₂ 1#32) ∗
      ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
      ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
      ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
      memRegion (sp + 0x140#64) 0x50 ∗
      memRegion (sp + 0x190#64) 104 ∗
      memRegion (sp + 0x1f8#64) 0xb8 ∗
      memRegion (sp + 0x2b0#64) 0x10 ∗
      memRegion (sp + 0x2c0#64) 0x14 ∗
      memRegion (sp + 0x2d4#64) 0xfc ∗
      ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      memRegion (sp + 0x3f4#64) 12 ∗
      ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
      memRegion (sp + 0x450#64) 0x50 ∗
      memRegion (sp + 0x4a0#64) 0x20 ∗
      ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
      ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
      ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
      ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
      memRegion (sp + 0x500#64) 96 ∗
      memRegion (sp + 0x560#64) 0x20 ∗
      (Frame5 ∗ R) := by
    dsimp only [evictActive, Frame4, Step5Cells, Frame5] at hm3 ⊢
    rw [vecAt_chains_eq, hstk_drop]
    refine Satisfies.mono (Entails.of_eq ?_) hm3
    ac_rfl
  have hreach5 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.s3_step5 img C A ctl S abs x trG.ratchet.senderPad sc
    receiverChainKey newSenderKey senderChainKey msgW Frame5 R s0 s3 sp rfl hpad_len
    hpc3 hrun3 hsp3 hsp_align3 hx25_3 hL3 hm_step5
  refine CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.BS10.reachesOrPanic_mono hreach5 ?_
  intro sf hkf_f hsym_f hsf
  rcases hsf with ⟨hpcf, hrunf, hspf, hsp_alignf, htrf,
    hx12f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx29f, _hx30f, hvregsf, _hLf, hmf⟩
  let trG' : TrGhost :=
    { trG with
      ratchet :=
        { trG.ratchet with
          chainsCap := cap'
          chainsPtr := ptr'
          chains := (evictGcs gcs1).map Prod.fst } }
  refine ⟨trG', ?_⟩
  have hpcf_s4 : sf.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS4PC img := by
    rw [hpcf, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS4PC_eq_fnAddr hLoads C ctl abs]
  have hmetaf : tryDecryptMidMeta img s0 sf := by
    refine ⟨hrunf, hspf, hsp0_align, hsp_alignf, ?_, htrf.trans htr3,
      ((hfrozen1.of_keepsFrozen _hkf2).of_keepsFrozen _hkf3).of_keepsFrozen hkf_f,
      hsym_f.trans (_hsym3.trans (_hsym2.trans hsym1')),
      hvregsf.trans (hvregs_3.trans (hvregs_2.trans (hvregs_1.trans hvregs)))⟩
    exact hx29f.trans (hx29_3.trans (hx29_2.trans (hx29_1.trans hx29)))
  have hx19_f : sf.readReg64 .x19 = x.ret :=
    hx19f.trans (hx19_3.trans (hx19_2.trans (hx19_1.trans hx19)))
  have hx20_f : sf.readReg64 .x20 = sp + 0x140#64 :=
    hx20f.trans (hx20_3.trans (hx20_2.trans (hx20_1.trans hx20)))
  have hx21_f : sf.readReg64 .x21 = x.ss :=
    hx21f.trans (hx21_3.trans (hx21_2.trans (hx21_1.trans hx21)))
  have hx22_f : sf.readReg64 .x22 = x.msgA :=
    hx22f.trans (hx22_3.trans (hx22_2.trans hx22_1))
  have hx23_f : sf.readReg64 .x23 = sp + 0x500#64 :=
    hx23f.trans hx23_3
  have hx24_f : (sf.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType := by
    rw [hx24f, setWidth8_zeroExtend64, hmsgW]
  refine ⟨hpcf_s4, hmetaf, hx12f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25f, ?_⟩
  have h_map_snd_gcs1 : gcs1.map Prod.snd = tr.ratchet.receiverChains ++ [newChain] :=
    map_snd_zip_append trG.ratchet.chains tr.ratchet.receiverChains
      (newChainGhost srkPtr ckPtr x.msg.senderRatchetKey) newChain hchains_len
  have h_evict_snd : (evictGcs gcs1).map Prod.snd = r1.receiverChains := by
    rw [map_snd_evictGcs, h_map_snd_gcs1]
  have h_zip_trG' : trG'.ratchet.chains.zip r1.receiverChains = evictGcs gcs1 := by
    dsimp only [trG']
    rw [← h_evict_snd, zip_map_fst_snd]
  have h_len_trG' : trG'.ratchet.chains.length = r1.receiverChains.length := by
    dsimp only [trG']
    rw [← h_evict_snd, List.length_map, List.length_map]
  have h_clamp_r1 : ∀ sc', r1.senderChain = some sc' →
      Ratchet.clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes := by
    intro sc' hsc'
    injection hsc' with hsc'_eq
    subst hsc'_eq
    exact hclamp
  dsimp only [trAt, ratchetAt, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap, signalMessageAt, Frame5, TailFrame] at hmf ⊢
  rw [h_zip_trG',
      show sp + 0x38#64 + 24#64 = sp + 0x50#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 128#64 = sp + 0xb8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 160#64 = sp + 0xd8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 168#64 = sp + 0xe0#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 172#64 = sp + 0xe4#64 from add_assoc_const _ _ _ _]
  have hmf_pures : sf.mem ⊨
      ⌜∀ sc', r1.senderChain = some sc' →
        Ratchet.clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
      ⌜trG'.ratchet.chains.length = r1.receiverChains.length ∧
        trG'.ratchet.senderPad.length = 100 ∧
        r1.maxForwardJumps < 2 ^ 64⌝ ∗
      ⌜macLength + 1 ≤ x.msg.serialized.length ∧
        x.msg.ciphertext.length < 2 ^ 40 ∧ x.msg.pqRatchet.length < 2 ^ 40 ∧
        x.msg.serialized.length < 2 ^ 40 ∧
        (∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
      (((sp + 0x50#64) ↦ₛ optSenderChainBytes (some ⟨newSenderKey,
        senderChainKey⟩) trG.ratchet.senderPad) ∗
       memRegion sp 0x20 ∗
       memRegion (sp + 0x140#64) 0x170 ∗
       ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 20) ∗
       memRegion (sp + 0x2d4#64) 0x2ac ∗
       ((vecAt A 104 8 (chainAt A) (sp + 0x38#64) cap' ptr' (evictGcs gcs1) ∗
         A.pool ∗
         stackAt sp tryDecryptSubStack ∗
         (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
          ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
          ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
          memRegion (sp + 0xe4#64) 4 ∗
          vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
          ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          memRegion x.ret 48 ∗
          ((sp + 0x20#64) ↦₆₄ x.locA) ∗
          ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 0x2c#64) 4 ∗
          ((sp + 0x30#64) ↦₆₄ x.remA) ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          vecU8At A x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
          boxU8At A (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
          boxU8At A (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
          ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
          optBoxU8At A (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
          ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗
          ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
          ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
          memRegion (x.msgA + 0x71#64) 7 ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          logOff img ∗
          tryDecryptSavedRegs s0.sp s0)) ∗ R)) := by
    rw [satisfies_pure_sepConj]
    refine ⟨h_clamp_r1, ?_⟩
    rw [satisfies_pure_sepConj]
    refine ⟨⟨h_len_trG', hpad_len, hmfj⟩, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨hmsg_pure, hmf⟩
  refine Satisfies.mono (Entails.of_eq ?_) hmf_pures
  dsimp only [sp, draws, r1, newChain, trG']
  ac_rfl

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH
