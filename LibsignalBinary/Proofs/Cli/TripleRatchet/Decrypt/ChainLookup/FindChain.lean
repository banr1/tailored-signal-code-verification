/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.Defs
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.FindChainSym
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainStack
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainSym

/-!
# `try_decrypt_with_state` Segment S2 (`FindChain`) Proof

Composes the `RatchetState::find_receiver_chain_key` call with its post-call branches
(`+0x2a4 → +0x3e4 / +0x500 / +0x30c`) to establish `FindChainSpec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_after_call_ok_none {img : Obj.Image} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 0x2a8#64)
    (hmeta : tryDecryptMidMeta img s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx22 : s.readReg64 .x22 = x.msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx24 : (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 0x2c0#64)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
      memRegion x.ret 48 ∗
      memRegion (s0.sp - 1504#64) 0x20 ∗
      (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
      (((s0.sp - 1504#64) + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 0x2c#64) 4 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x140#64) 0x50 ∗
      findReceiverChainKeyResultAt ((s0.sp - 1504#64) + 0x190#64) (.ok none) ∗
      memRegion ((s0.sp - 1504#64) + 0x1b8#64) 0x3c8 ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :
    reaches_pc (tripleRatchetProgAtExt img.base ext) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segDhStepPC img) s
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepState A ctl img x trG tr st1 R s0) := by
  let sp := s0.sp - 1504#64
  change s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    (((sp + 0x190#64) ↦₃₂ 0#32) ∗ memRegion (sp + 0x190#64 + 4#64) 36) ∗
    memRegion (sp + 0x1b8#64) 0x3c8 ∗
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R at hm
  rw [show sp + 0x190#64 + 4#64 = sp + 0x194#64 by bv_omega,
      memRegion_split (sp + 0x1b8#64) 0x1c8 0x200 (by decide),
      show (sp + 0x1b8#64) + BitVec.ofNat 64 0x1c8 = sp + 0x380#64 by bv_omega,
      memRegion_split (sp + 0x380#64) 16 0x1f0 (by decide),
      show (sp + 0x380#64) + 16#64 = sp + 0x390#64 by bv_omega] at hm
  have hm1 : s.mem ⊨ memRegion (sp + 0x194#64) 36 ∗
      (memRegion (sp + 0x380#64) 16 ∗
       ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x20 ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x1b8#64) 0x1c8 ∗
       memRegion (sp + 0x390#64) 0x1f0 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, hm2⟩ := exists_words36_of_memRegion_36 hm1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm2
  have hm3 : s.mem ⊨ memRegion (sp + 0x380#64) 16 ∗
      ((((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2) ∗
        ((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x20 ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x1b8#64) 0x1c8 ∗
       memRegion (sp + 0x390#64) 0x1f0 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨d0, d1, hm4⟩ := exists_words16_of_memRegion_16 hm3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm4
  let F_none :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1b8#64) 0x1c8 ∗
    memRegion (sp + 0x390#64) 0x1f0 ∗
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R
  have hm_pre : s.mem ⊨
      (((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦₃₂ w0) ∗
       ((sp + 0x198#64) ↦₆₄ w1) ∗
       ((sp + 0x1a0#64) ↦₆₄ w2) ∗
       ((sp + 0x1a8#64) ↦₆₄ w3) ∗
       ((sp + 0x1b0#64) ↦₆₄ w4) ∗
       ((sp + 0x380#64) ↦₆₄ d0) ∗
       ((sp + 0x388#64) ↦₆₄ d1)) ∗ F_none := by
    dsimp only [F_none]
    convert hm4 using 1; sep_ac_rfl
  have hwp := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_ok_none_full_wp (ext := ext)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (d0 := d0) (d1 := d1)
    himg hpc (tryDecryptMidMeta.to_wpInv hmeta) hx25 hx28
  refine sepWP_to_reaches_pc_with_midMeta hmeta hwp hm_pre ?_
  intro sf Pf hpcf ⟨hPf, hwpInv_f, hx12_f, hcs⟩ hinv_f hmf
  subst hPf
  refine ⟨hpcf, hwpInv_f.to_midMeta hinv_f, hx12_f,
    (hcs.1).trans hx19,
    (hcs.2.1).trans hx20,
    (hcs.2.2.1).trans hx21,
    (hcs.2.2.2.1).trans hx22,
    (hcs.2.2.2.2.1).trans hx23,
    by change (sf.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hcs.2.2.2.2.2.1]; exact hx24,
    (hcs.2.2.2.2.2.2.1).trans hx25,
    (hcs.2.2.2.2.2.2.2.2.1).trans hx27,
    (hcs.2.2.2.2.2.2.2.2.2.1).trans hx28,
    ?_⟩
  have hmf_re : sf.mem ⊨
      (memRegion (sp + 0x140#64) 0x50 ∗
       ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       (((sp + 0x194#64) ↦₃₂ w0) ∗
        ((sp + 0x198#64) ↦₆₄ w1) ∗
        ((sp + 0x1a0#64) ↦₆₄ w2) ∗
        ((sp + 0x1a8#64) ↦₆₄ w3) ∗
        ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       memRegion (sp + 0x1b8#64) 0x1c8 ∗
       (((sp + 0x380#64) ↦₆₄ w3) ∗
        ((sp + 0x388#64) ↦₆₄ w4)) ∗
       memRegion (sp + 0x390#64) 0x1f0) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x20 ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    dsimp only [F_none, sp] at hmf ⊢
    convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono (sepConj_mono_left (findChain_none_stack_recombine sp w0 w1 w2 w3 w4)) hmf_re
  dsimp only [sp] at hmf2 ⊢
  convert hmf2 using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_after_call_ok_some {img : Obj.Image} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {R : SepProp} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 0x2a8#64)
    (hmeta : tryDecryptMidMeta img s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx22 : s.readReg64 .x22 = x.msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx24 : (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 0x2c0#64)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
      memRegion x.ret 48 ∗
      memRegion (s0.sp - 1504#64) 0x20 ∗
      (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
      (((s0.sp - 1504#64) + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 0x2c#64) 4 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x140#64) 0x50 ∗
      findReceiverChainKeyResultAt ((s0.sp - 1504#64) + 0x190#64) (.ok (some ck)) ∗
      memRegion ((s0.sp - 1504#64) + 0x1b8#64) 0x3c8 ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :
    reaches_pc (tripleRatchetProgAtExt img.base ext) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segConsumeMsgKeyPC img) s
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img x trG tr st1 ck 0 R s0) := by
  let sp := s0.sp - 1504#64
  have htake_len : ((chainKeyBytes ck).take 20).length = 20 := by
    rw [List.length_take_of_le (by rw [chainKeyBytes_length]; decide)]
  have hdrop_len : ((chainKeyBytes ck).drop 20).length = 16 := by
    rw [List.length_drop, chainKeyBytes_length]
  obtain ⟨w0, w1, w2, hw20⟩ := exists_words20_of_length_20 htake_len
  obtain ⟨w3, w4, hw16⟩ := exists_words16_of_length_16 hdrop_len
  have hck_split :
      ((sp + 0x190#64 + 4#64) ↦ₛ chainKeyBytes ck) =
        (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2)) ∗
        (((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) := by
    rw [show sp + 0x190#64 + 4#64 = sp + 0x194#64 by bv_omega,
        ← List.take_append_drop 20 (chainKeyBytes ck),
        pointsToBytes_append, htake_len,
        show (sp + 0x194#64) + BitVec.ofNat 64 20 = sp + 0x1a8#64 by bv_omega,
        hw20 (sp + 0x194#64), hw16 (sp + 0x1a8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  change s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    (((sp + 0x190#64) ↦₃₂ 1#32) ∗ ((sp + 0x190#64 + 4#64) ↦ₛ chainKeyBytes ck)) ∗
    memRegion (sp + 0x1b8#64) 0x3c8 ∗
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R at hm
  rw [hck_split,
      memRegion_split (sp + 0x1b8#64) 0xf8 0x2d0 (by decide),
      show (sp + 0x1b8#64) + BitVec.ofNat 64 0xf8 = sp + 0x2b0#64 by bv_omega,
      memRegion_split (sp + 0x2b0#64) 16 0x2c0 (by decide),
      show (sp + 0x2b0#64) + 16#64 = sp + 0x2c0#64 by bv_omega,
      memRegion_split (sp + 0x2c0#64) 20 0x2ac (by decide),
      show (sp + 0x2c0#64) + 20#64 = sp + 0x2d4#64 by bv_omega,
      memRegion_split (sp + 0x2d4#64) 0xac 0x200 (by decide),
      show (sp + 0x2d4#64) + BitVec.ofNat 64 0xac = sp + 0x380#64 by bv_omega,
      memRegion_split (sp + 0x380#64) 16 0x1f0 (by decide),
      show (sp + 0x380#64) + 16#64 = sp + 0x390#64 by bv_omega] at hm
  have hm1 : s.mem ⊨ memRegion (sp + 0x2b0#64) 16 ∗
      (memRegion (sp + 0x2c0#64) 20 ∗
       memRegion (sp + 0x380#64) 16 ∗
       ((sp + 0x190#64) ↦₃₂ 1#32) ∗
       (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2)) ∗
       (((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x20 ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x1b8#64) 0xf8 ∗
       memRegion (sp + 0x2d4#64) 0xac ∗
       memRegion (sp + 0x390#64) 0x1f0 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨b0, b1, hm2⟩ := exists_words16_of_memRegion_16 hm1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm2
  have hm3 : s.mem ⊨ memRegion (sp + 0x2c0#64) 20 ∗
      ((((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1)) ∗
       memRegion (sp + 0x380#64) 16 ∗
       ((sp + 0x190#64) ↦₃₂ 1#32) ∗
       (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2)) ∗
       (((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x20 ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x1b8#64) 0xf8 ∗
       memRegion (sp + 0x2d4#64) 0xac ∗
       memRegion (sp + 0x390#64) 0x1f0 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨c0, c1, c2, hm4⟩ := exists_words20_of_memRegion_20 hm3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm4
  have hm5 : s.mem ⊨ memRegion (sp + 0x380#64) 16 ∗
      ((((sp + 0x2c0#64) ↦₃₂ c0) ∗ ((sp + 0x2c4#64) ↦₆₄ c1) ∗ ((sp + 0x2cc#64) ↦₆₄ c2)) ∗
       (((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1)) ∗
       ((sp + 0x190#64) ↦₃₂ 1#32) ∗
       (((sp + 0x194#64) ↦₃₂ w0) ∗ ((sp + 0x198#64) ↦₆₄ w1) ∗ ((sp + 0x1a0#64) ↦₆₄ w2)) ∗
       (((sp + 0x1a8#64) ↦₆₄ w3) ∗ ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x20 ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x1b8#64) 0xf8 ∗
       memRegion (sp + 0x2d4#64) 0xac ∗
       memRegion (sp + 0x390#64) 0x1f0 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm4 using 1; sep_ac_rfl
  obtain ⟨d0, d1, hm6⟩ := exists_words16_of_memRegion_16 hm5
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm6
  let F_some :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1b8#64) 0xf8 ∗
    memRegion (sp + 0x2d4#64) 0xac ∗
    memRegion (sp + 0x390#64) 0x1f0 ∗
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R
  have hm_pre : s.mem ⊨
      (((sp + 0x190#64) ↦₃₂ 1#32) ∗
       ((sp + 0x194#64) ↦₃₂ w0) ∗
       ((sp + 0x198#64) ↦₆₄ w1) ∗
       ((sp + 0x1a0#64) ↦₆₄ w2) ∗
       ((sp + 0x1a8#64) ↦₆₄ w3) ∗
       ((sp + 0x1b0#64) ↦₆₄ w4) ∗
       ((sp + 0x2b0#64) ↦₆₄ b0) ∗
       ((sp + 0x2b8#64) ↦₆₄ b1) ∗
       ((sp + 0x2c0#64) ↦₃₂ c0) ∗
       ((sp + 0x2c4#64) ↦₆₄ c1) ∗
       ((sp + 0x2cc#64) ↦₆₄ c2) ∗
       ((sp + 0x380#64) ↦₆₄ d0) ∗
       ((sp + 0x388#64) ↦₆₄ d1)) ∗ F_some := by
    dsimp only [F_some]
    convert hm6 using 1; sep_ac_rfl
  have hwp := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_ok_some_full_wp (ext := ext)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (b0 := b0) (b1 := b1) (c0 := c0) (c1 := c1) (c2 := c2) (d0 := d0) (d1 := d1)
    himg hpc (tryDecryptMidMeta.to_wpInv hmeta) hx25 hx28
  refine sepWP_to_reaches_pc_with_midMeta hmeta hwp hm_pre ?_
  intro sf Pf hpcf ⟨hPf, hwpInv_f, hx12_f, hcs⟩ hinv_f hmf
  subst hPf
  refine ⟨hpcf, hwpInv_f.to_midMeta hinv_f, hx12_f,
    (hcs.1).trans hx19,
    (hcs.2.1).trans hx20,
    (hcs.2.2.1).trans hx21,
    (hcs.2.2.2.1).trans hx22,
    (hcs.2.2.2.2.1).trans hx23,
    by change (sf.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hcs.2.2.2.2.2.1]; exact hx24,
    (hcs.2.2.2.2.2.2.1).trans hx25,
    ?_⟩
  have h2b0 :
      (((sp + 0x2b0#64) ↦₆₄ w3) ∗ ((sp + 0x2b8#64) ↦₆₄ w4)) =
      ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes ck).drop 20) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using (hw16 (sp + 0x2b0#64)).symm
  have h2c0 :
      (((sp + 0x2c0#64) ↦₃₂ w0) ∗ ((sp + 0x2c4#64) ↦₆₄ w1) ∗ ((sp + 0x2cc#64) ↦₆₄ w2)) =
      ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes ck).take 20) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using (hw20 (sp + 0x2c0#64)).symm
  have hmf_re : sf.mem ⊨
      (memRegion (sp + 0x140#64) 0x50 ∗
       ((sp + 0x190#64) ↦₃₂ 1#32) ∗
       (((sp + 0x194#64) ↦₃₂ w0) ∗
        ((sp + 0x198#64) ↦₆₄ w1) ∗
        ((sp + 0x1a0#64) ↦₆₄ w2) ∗
        ((sp + 0x1a8#64) ↦₆₄ w3) ∗
        ((sp + 0x1b0#64) ↦₆₄ w4)) ∗
       memRegion (sp + 0x1b8#64) 0xf8) ∗
      (memRegion (sp + 0x2d4#64) 0xac ∗
       (((sp + 0x380#64) ↦₆₄ w3) ∗
        ((sp + 0x388#64) ↦₆₄ w4)) ∗
       memRegion (sp + 0x390#64) 0x1f0) ∗
      (((sp + 0x2b0#64) ↦₆₄ w3) ∗ ((sp + 0x2b8#64) ↦₆₄ w4)) ∗
      (((sp + 0x2c0#64) ↦₃₂ w0) ∗ ((sp + 0x2c4#64) ↦₆₄ w1) ∗ ((sp + 0x2cc#64) ↦₆₄ w2)) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x20 ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    dsimp only [F_some, sp] at hmf ⊢
    convert hmf using 1; sep_ac_rfl
  rw [h2b0, h2c0] at hmf_re
  have hmf2 := Satisfies.mono
    (sepConj_mono (findChain_some_stack_recombine_left sp w0 w1 w2 w3 w4)
      (sepConj_mono_left (findChain_some_stack_recombine_right sp w3 w4))) hmf_re
  dsimp only [sp] at hmf2 ⊢
  convert hmf2 using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_after_call_error {img : Obj.Image} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {R : SepProp} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 0x2a8#64)
    (hmeta : tryDecryptMidMeta img s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
      memRegion x.ret 48 ∗
      memRegion (s0.sp - 1504#64) 0x20 ∗
      (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
      (((s0.sp - 1504#64) + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 0x2c#64) 4 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x140#64) 0x50 ∗
      findReceiverChainKeyResultAt ((s0.sp - 1504#64) + 0x190#64) (.error e) ∗
      memRegion ((s0.sp - 1504#64) + 0x1b8#64) 0x3c8 ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :
    reaches_pc (tripleRatchetProgAtExt img.base ext) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errTailPC img) s
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e 0 R s0) := by
  let sp := s0.sp - 1504#64
  have hm_findReceiverChainKey : s.mem ⊨ findReceiverChainKeyResultAt (sp + 0x190#64) (.error e) ∗
      ((memRegion sp 0x20 ∗
        ((sp + 0x20#64) ↦₆₄ x.locA) ∗
        ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗
        ((sp + 0x30#64) ↦₆₄ x.remA)) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x1b8#64) 0x3c8 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    dsimp only [sp] at hm ⊢
    convert hm using 1; sep_ac_rfl
  obtain ⟨he, hm_err⟩ := findReceiverChainKeyResultAt_error_eq hm_findReceiverChainKey
  subst he
  have hm_sp38 := Satisfies.mono
    (sepConj_mono_right (sepConj_mono_left (findChain_err_stack_recombine_sp38 sp x.locA x.remA x.msg.counter)))
    hm_err
  unfold strRefAt at hm_sp38
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm_sp38
  have hm_ex : s.mem ⊨
      (∃∗ p : BitVec 64,
        ((sp + 0x198#64) ↦₆₄ p) ∗
        ((sp + 0x1a0#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length) ∗
        (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey)) ∗
      (((sp + 0x190#64) ↦₃₂ 2#32) ∗
       memRegion (sp + 0x194#64) 4 ∗
       memRegion (sp + 0x1a8#64) 16 ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x38 ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x1b8#64) 0x3c8 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm_sp38 using 1; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_ex
  rcases hm_ex with ⟨p, hm_p⟩
  rw [memRegion_split (sp + 0x140#64) 0x28 0x28 (by decide),
      show (sp + 0x140#64) + BitVec.ofNat 64 0x28 = sp + 0x168#64 by bv_omega,
      memRegion_split (sp + 0x168#64) 16 24 (by decide),
      show (sp + 0x168#64) + 16#64 = sp + 0x178#64 by bv_omega,
      memRegion_split (sp + 0x178#64) 16 8 (by decide),
      show (sp + 0x178#64) + 16#64 = sp + 0x188#64 by bv_omega,
      memRegion_split (sp + 0x188#64) 4 4 (by decide),
      show (sp + 0x188#64) + 4#64 = sp + 0x18c#64 by bv_omega,
      memRegion_split (sp + 0x1b8#64) 0xf8 0x2d0 (by decide),
      show (sp + 0x1b8#64) + BitVec.ofNat 64 0xf8 = sp + 0x2b0#64 by bv_omega,
      memRegion_split (sp + 0x2b0#64) 16 0x2c0 (by decide),
      show (sp + 0x2b0#64) + 16#64 = sp + 0x2c0#64 by bv_omega,
      memRegion_split (sp + 0x2c0#64) 8 0x2b8 (by decide),
      show (sp + 0x2c0#64) + 8#64 = sp + 0x2c8#64 by bv_omega,
      memRegion_split (sp + 0x2c8#64) 4 0x2b4 (by decide),
      show (sp + 0x2c8#64) + 4#64 = sp + 0x2cc#64 by bv_omega,
      memRegion_split (sp + 0x2cc#64) 4 0x2b0 (by decide),
      show (sp + 0x2cc#64) + 4#64 = sp + 0x2d0#64 by bv_omega,
      memRegion_split (sp + 0x2d0#64) 4 0x2ac (by decide),
      show (sp + 0x2d0#64) + 4#64 = sp + 0x2d4#64 by bv_omega,
      memRegion_split (sp + 0x2d4#64) 0x5c 0x250 (by decide),
      show (sp + 0x2d4#64) + BitVec.ofNat 64 0x5c = sp + 0x330#64 by bv_omega,
      memRegion_split (sp + 0x330#64) 16 0x240 (by decide),
      show (sp + 0x330#64) + 16#64 = sp + 0x340#64 by bv_omega,
      memRegion_split (sp + 0x340#64) 20 0x22c (by decide),
      show (sp + 0x340#64) + 20#64 = sp + 0x354#64 by bv_omega] at hm_p
  let w1 := BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length
  let F_err_base :=
    (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗
    ((sp + 0x190#64) ↦₃₂ 2#32) ∗
    ((sp + 0x198#64) ↦₆₄ p) ∗
    ((sp + 0x1a0#64) ↦₆₄ w1) ∗
    memRegion (sp + 0x194#64) 4 ∗
    memRegion (sp + 0x1a8#64) 16 ∗
    memRegion (sp + 0x1b8#64) 0xf8 ∗
    memRegion (sp + 0x2d4#64) 0x5c ∗
    memRegion (sp + 0x354#64) 0x22c ∗
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x38 ∗
    memRegion (sp + 0x140#64) 0x28 ∗
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R
  have hm1 : s.mem ⊨ memRegion (sp + 0x168#64) 16 ∗
      (memRegion (sp + 0x178#64) 16 ∗
       memRegion (sp + 0x188#64) 4 ∗
       memRegion (sp + 0x18c#64) 4 ∗
       memRegion (sp + 0x2b0#64) 16 ∗
       memRegion (sp + 0x2c0#64) 8 ∗
       memRegion (sp + 0x2c8#64) 4 ∗
       memRegion (sp + 0x2cc#64) 4 ∗
       memRegion (sp + 0x2d0#64) 4 ∗
       memRegion (sp + 0x330#64) 16 ∗
       memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by
    dsimp only [F_err_base, w1]
    convert hm_p using 1; sep_ac_rfl
  obtain ⟨g0, g1, hm2⟩ := exists_words16_of_memRegion_16 hm1
  have hm3 : s.mem ⊨ memRegion (sp + 0x178#64) 16 ∗
      ((((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x188#64) 4 ∗
       memRegion (sp + 0x18c#64) 4 ∗
       memRegion (sp + 0x2b0#64) 16 ∗
       memRegion (sp + 0x2c0#64) 8 ∗
       memRegion (sp + 0x2c8#64) 4 ∗
       memRegion (sp + 0x2cc#64) 4 ∗
       memRegion (sp + 0x2d0#64) 4 ∗
       memRegion (sp + 0x330#64) 16 ∗
       memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨g2, g3, hm4⟩ := exists_words16_of_memRegion_16 hm3
  have hm5 : s.mem ⊨ memRegion (sp + 0x188#64) 4 ∗
      ((((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x18c#64) 4 ∗
       memRegion (sp + 0x2b0#64) 16 ∗
       memRegion (sp + 0x2c0#64) 8 ∗
       memRegion (sp + 0x2c8#64) 4 ∗
       memRegion (sp + 0x2cc#64) 4 ∗
       memRegion (sp + 0x2d0#64) 4 ∗
       memRegion (sp + 0x330#64) 16 ∗
       memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by
    convert hm4 using 1; sep_ac_rfl
  obtain ⟨g4, hm6⟩ := exists_word32_of_memRegion_4 hm5
  have hm7 : s.mem ⊨ memRegion (sp + 0x18c#64) 4 ∗
      (((sp + 0x188#64) ↦₃₂ g4) ∗
       (((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x2b0#64) 16 ∗
       memRegion (sp + 0x2c0#64) 8 ∗
       memRegion (sp + 0x2c8#64) 4 ∗
       memRegion (sp + 0x2cc#64) 4 ∗
       memRegion (sp + 0x2d0#64) 4 ∗
       memRegion (sp + 0x330#64) 16 ∗
       memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by
    convert hm6 using 1; sep_ac_rfl
  obtain ⟨d8c, hm8⟩ := exists_word32_of_memRegion_4 hm7
  have hm9 : s.mem ⊨ memRegion (sp + 0x2b0#64) 16 ∗
      (((sp + 0x18c#64) ↦₃₂ d8c) ∗
       ((sp + 0x188#64) ↦₃₂ g4) ∗
       (((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x2c0#64) 8 ∗
       memRegion (sp + 0x2c8#64) 4 ∗
       memRegion (sp + 0x2cc#64) 4 ∗
       memRegion (sp + 0x2d0#64) 4 ∗
       memRegion (sp + 0x330#64) 16 ∗
       memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by
    convert hm8 using 1; sep_ac_rfl
  obtain ⟨b0, b1, hm10⟩ := exists_words16_of_memRegion_16 hm9
  have hm11 : s.mem ⊨ memRegion (sp + 0x2c0#64) 8 ∗
      ((((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b0#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 0x18c#64) ↦₃₂ d8c) ∗
       ((sp + 0x188#64) ↦₃₂ g4) ∗
       (((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x2c8#64) 4 ∗
       memRegion (sp + 0x2cc#64) 4 ∗
       memRegion (sp + 0x2d0#64) 4 ∗
       memRegion (sp + 0x330#64) 16 ∗
       memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by
    convert hm10 using 1; sep_ac_rfl
  obtain ⟨d0, hm12⟩ := exists_word64_of_memRegion_8 hm11
  have hm13 : s.mem ⊨ memRegion (sp + 0x2c8#64) 4 ∗
      (((sp + 0x2c0#64) ↦₆₄ d0) ∗
       (((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b0#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 0x18c#64) ↦₃₂ d8c) ∗
       ((sp + 0x188#64) ↦₃₂ g4) ∗
       (((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x2cc#64) 4 ∗
       memRegion (sp + 0x2d0#64) 4 ∗
       memRegion (sp + 0x330#64) 16 ∗
       memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by
    convert hm12 using 1; sep_ac_rfl
  obtain ⟨d1_lo, hm14⟩ := exists_word32_of_memRegion_4 hm13
  have hm15 : s.mem ⊨ memRegion (sp + 0x2cc#64) 4 ∗
      (((sp + 0x2c8#64) ↦₃₂ d1_lo) ∗
       ((sp + 0x2c0#64) ↦₆₄ d0) ∗
       (((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b0#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 0x18c#64) ↦₃₂ d8c) ∗
       ((sp + 0x188#64) ↦₃₂ g4) ∗
       (((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x2d0#64) 4 ∗
       memRegion (sp + 0x330#64) 16 ∗
       memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by
    convert hm14 using 1; sep_ac_rfl
  obtain ⟨d1_hi, hm16⟩ := exists_word32_of_memRegion_4 hm15
  have hm17 : s.mem ⊨ memRegion (sp + 0x2d0#64) 4 ∗
      (((sp + 0x2cc#64) ↦₃₂ d1_hi) ∗
       ((sp + 0x2c8#64) ↦₃₂ d1_lo) ∗
       ((sp + 0x2c0#64) ↦₆₄ d0) ∗
       (((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b0#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 0x18c#64) ↦₃₂ d8c) ∗
       ((sp + 0x188#64) ↦₃₂ g4) ∗
       (((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x330#64) 16 ∗
       memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by
    convert hm16 using 1; sep_ac_rfl
  obtain ⟨d2d0, hm18⟩ := exists_word32_of_memRegion_4 hm17
  have hm19 : s.mem ⊨ memRegion (sp + 0x330#64) 16 ∗
      (((sp + 0x2d0#64) ↦₃₂ d2d0) ∗
       ((sp + 0x2cc#64) ↦₃₂ d1_hi) ∗
       ((sp + 0x2c8#64) ↦₃₂ d1_lo) ∗
       ((sp + 0x2c0#64) ↦₆₄ d0) ∗
       (((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b0#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 0x18c#64) ↦₃₂ d8c) ∗
       ((sp + 0x188#64) ↦₃₂ g4) ∗
       (((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 0x340#64) 20 ∗ F_err_base) := by
    convert hm18 using 1; sep_ac_rfl
  obtain ⟨c0, c1, hm20⟩ := exists_words16_of_memRegion_16 hm19
  have hm21 : s.mem ⊨ memRegion (sp + 0x340#64) 20 ∗
      ((((sp + 0x330#64) ↦₆₄ c0) ∗ ((sp + 0x330#64 + 8#64) ↦₆₄ c1)) ∗
       ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗
       ((sp + 0x2cc#64) ↦₃₂ d1_hi) ∗
       ((sp + 0x2c8#64) ↦₃₂ d1_lo) ∗
       ((sp + 0x2c0#64) ↦₆₄ d0) ∗
       (((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b0#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 0x18c#64) ↦₃₂ d8c) ∗
       ((sp + 0x188#64) ↦₃₂ g4) ∗
       (((sp + 0x178#64) ↦₆₄ g2) ∗ ((sp + 0x178#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 0x168#64) ↦₆₄ g0) ∗ ((sp + 0x168#64 + 8#64) ↦₆₄ g1)) ∗ F_err_base) := by
    convert hm20 using 1; sep_ac_rfl
  obtain ⟨s0_w, s1, s2, hm22⟩ := exists_words20_of_memRegion_20 hm21
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm22
  let F_err :=
    (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗
    memRegion (sp + 0x194#64) 4 ∗
    memRegion (sp + 0x1a8#64) 16 ∗
    memRegion (sp + 0x1b8#64) 0xf8 ∗
    memRegion (sp + 0x2d4#64) 0x5c ∗
    memRegion (sp + 0x354#64) 0x22c ∗
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x38 ∗
    memRegion (sp + 0x140#64) 0x28 ∗
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R
  have hm_pre : s.mem ⊨
      (((sp + 0x168#64) ↦₆₄ g0) ∗
       ((sp + 0x170#64) ↦₆₄ g1) ∗
       ((sp + 0x178#64) ↦₆₄ g2) ∗
       ((sp + 0x180#64) ↦₆₄ g3) ∗
       ((sp + 0x188#64) ↦₃₂ g4) ∗
       ((sp + 0x18c#64) ↦₃₂ d8c) ∗
       ((sp + 0x190#64) ↦₃₂ 2#32) ∗
       ((sp + 0x198#64) ↦₆₄ p) ∗
       ((sp + 0x1a0#64) ↦₆₄ w1) ∗
       ((sp + 0x2b0#64) ↦₆₄ b0) ∗
       ((sp + 0x2b8#64) ↦₆₄ b1) ∗
       ((sp + 0x2c0#64) ↦₆₄ d0) ∗
       ((sp + 0x2c8#64) ↦₃₂ d1_lo) ∗
       ((sp + 0x2cc#64) ↦₃₂ d1_hi) ∗
       ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗
       ((sp + 0x330#64) ↦₆₄ c0) ∗
       ((sp + 0x338#64) ↦₆₄ c1) ∗
       ((sp + 0x340#64) ↦₃₂ s0_w) ∗
       ((sp + 0x344#64) ↦₆₄ s1) ∗
       ((sp + 0x34c#64) ↦₆₄ s2)) ∗ F_err := by
    dsimp only [F_err, F_err_base, w1] at hm22 ⊢
    convert hm22 using 1; sep_ac_rfl
  have hwp := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_err_wp (ext := ext)
    (w0 := p) (w1 := w1) (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3)
    (b0 := b0) (b1 := b1) (d0 := d0) (c0 := c0) (c1 := c1) (s1 := s1) (s2 := s2)
    (g4 := g4) (d8c := d8c) (d1_lo := d1_lo) (d1_hi := d1_hi) (d2d0 := d2d0) (s0_w := s0_w)
    himg hpc (tryDecryptMidMeta.to_wpInv hmeta) hx20 hx25
  refine sepWP_to_reaches_pc_with_midMeta hmeta hwp hm_pre ?_
  intro sf Pf hpcf ⟨hPf, hwpInv_f, hx19_f, hx20_f, hx26_f⟩ hinv_f hmf
  subst hPf
  refine ⟨hpcf, hwpInv_f.to_midMeta hinv_f, hx19_f.trans hx19, hx20_f.trans hx20, hx26_f, ?_⟩
  let u0 := b0.extractLsb' 0 32 ++ d2d0
  let u1 := b1.extractLsb' 0 32 ++ b0.extractLsb' 32 32
  let u2 := b1.extractLsb' 32 32
  have hmf_re : sf.mem ⊨
      (((sp + 0x168#64) ↦₆₄ p) ∗
       ((sp + 0x170#64) ↦₆₄ w1) ∗
       (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗
       ((sp + 0x178#64) ↦₆₄ u0) ∗
       ((sp + 0x180#64) ↦₆₄ u1) ∗
       ((sp + 0x188#64) ↦₃₂ u2) ∗
       ((sp + 0x18c#64) ↦₃₂ 24#32)) ∗
      (((sp + 0x190#64) ↦₃₂ 2#32) ∗
       memRegion (sp + 0x194#64) 4 ∗
       (((sp + 0x198#64) ↦₆₄ p) ∗ ((sp + 0x1a0#64) ↦₆₄ w1)) ∗
       memRegion (sp + 0x1a8#64) 16 ∗
       memRegion (sp + 0x1b8#64) 0xf8 ∗
       (((sp + 0x2b0#64) ↦₆₄ b0) ∗ ((sp + 0x2b8#64) ↦₆₄ b1)) ∗
       (((sp + 0x2c0#64) ↦₆₄ p) ∗ ((sp + 0x2c8#64) ↦₆₄ w1)) ∗
       ((sp + 0x2d0#64) ↦₃₂ d2d0) ∗
       memRegion (sp + 0x2d4#64) 0x5c ∗
       (((sp + 0x330#64) ↦₆₄ p) ∗ ((sp + 0x338#64) ↦₆₄ w1)) ∗
       (((sp + 0x340#64) ↦₆₄ u0) ∗ ((sp + 0x348#64) ↦₆₄ u1)) ∗
       ((sp + 0x350#64) ↦₃₂ u2) ∗
       memRegion (sp + 0x354#64) 0x22c) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x38 ∗
       memRegion (sp + 0x140#64) 0x28 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    dsimp only [F_err, u0, u1, u2, sp] at hmf ⊢
    convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono
    (sepConj_mono (findChain_err_speBody_entails A sp p u0 u1 u2)
      (sepConj_mono_left (findChain_err_stack_recombine_0x190 sp p w1 b0 b1 u0 u1 d2d0 u2))) hmf_re
  dsimp only [sp] at hmf2 ⊢
  convert hmf2 using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_ok_ext {img : Obj.Image} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S2SpecExt img A ctl ext := by
  intro himg hfrck x trG tr st1 R s0 s hs2 _hcode
  have hcall := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_call_findReceiverChainKey_reaches himg hfrck x trG tr st1 R s0 s hs2
  cases hres : tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
  | ok optCk =>
    cases optCk with
    | some ck =>
      rw [hres] at hcall
      refine reaches_pc_seq hcall (fun s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, _, hx28_ret, hm_ret⟩ => ?_)
      exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_after_call_ok_some himg hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hx28_ret hm_ret
    | none =>
      rw [hres] at hcall
      refine reaches_pc_seq hcall (fun s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, hx27_ret, hx28_ret, hm_ret⟩ => ?_)
      exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_after_call_ok_none himg hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hx27_ret hx28_ret hm_ret
  | error e =>
    rw [hres] at hcall
    refine reaches_pc_seq hcall (fun s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, _, _, _, _, hx25_ret, _, _, hm_ret⟩ => ?_)
    exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_after_call_error himg hpc_ret hmeta_ret hx19_ret hx20_ret hx25_ret hm_ret

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_ok_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainSpec_trap img C A ctl abs :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_ok_ext

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainSpec img C A ctl abs :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_ok_ext

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
