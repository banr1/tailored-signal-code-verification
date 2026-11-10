/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymA
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import LibsignalBinary.Proofs.E2E.Record.Serialization.MsgKeyLen
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WPp

/-!
# `<session_structure::Chain as prost::Message>::encoded_len` (`0x26aa0`)

Proves `chainLen_ok` and its relocatable `[LibsignalPlacement]` counterparts (block `88`), showing
that `Chain::encoded_len` returns `(encChainMem gc).length` by summing tags 1
(`sender_ratchet_key`), 2 (`sender_ratchet_key_private`), 3 (`chain_key`), and 4 (`message_keys` via
`MessageKey::encoded_len`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  Prost.truncate32_ofNat64
  hwVarintLen_eq_encodeVarint_length' hwVarintLen_bvShift_eq_encodeVarint_length'
  hwVarintLen_mix1_eq_encodeVarint_length hwVarintLen_mix2_eq_encodeVarint_length

private theorem chainLen_senderRatchetKey (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (g : ChainGhost) (c : ReceiverChain) (a : BitVec 64)
    (hsrk_lt : g.srk.bytes.length < 2 ^ 63)
    (v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64)
    (s0 : State) (Frame : SepProp)
    (hpc : s0.pc = (tripleRatchetProgAt b C ctl abs).fnAddr chainLenName)
    (hrun : s0.status = .Running)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = a) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr chainLenName + 56#64)
      s0
      (chainFieldsAt A g c a ∗
        chainLenSavedAt s0.sp v0 v1 v2 v3 v4 v5 v6 v7 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ chainFieldsAt A g c a ∗
          chainLenSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x23) v3 (s0.readReg64 .x22) (s0.readReg64 .x21)
            (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
          Frame) ∧
        Saved64Preserved s0 sm (s0.sp - 64#64) ∧
        sm.readReg64 .x0 = a ∧
        sm.readReg64 .x8 = BitVec.ofNat 64 (bytesField 1 g.srk.bytes).length) := by
  chainLen_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") 158548 0 56
  dsimp only [tripleRatchetProgAt, chainLenName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
    "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" = entry
  examples_hide_fetches
  have halign' : s0.sp &&& 15#64 = 0#64 := by
    simpa [beq_iff_eq] using halign
  dsimp only [chainFieldsAt, chainLenSavedAt]
  by_cases hsrk : g.srk.bytes = []
  · simp only [hsrk, bytesField, ↓reduceIte, List.length_nil, BitVec.ofNat_eq_ofNat]
    wp_steps
    wp_done
  · have hne0 := ofNat_len_beq_zero_of_ne_nil hsrk hsrk_lt
    have hbf := bv_bytesField_length_of_ne_nil (tag := 1) hsrk rfl
    wp_steps
    wp_done

private theorem chainLen_senderRatchetKeyPrivate (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (g : ChainGhost) (c : ReceiverChain) (a : BitVec 64) (s1 : Nat)
    (hpriv_lt : g.priv.bytes.length < 2 ^ 63)
    (hfit12 : s1 + (bytesField 2 g.priv.bytes).length < 2 ^ 64)
    (s0 s : State) (fsp : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr chainLenName + 56#64)
    (hrun : s.status = .Running)
    (hpres : Saved64Preserved s0 s fsp)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr chainLenName + 100#64)
      s
      (chainFieldsAt A g c a ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ chainFieldsAt A g c a ∗ Frame) ∧
        Saved64Preserved s0 sm fsp ∧
        sm.readReg64 .x0 = a ∧
        sm.readReg64 .x8 = BitVec.ofNat 64 (s1 + (bytesField 2 g.priv.bytes).length)) := by
  chainLen_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") 158548 56 100
  dsimp only [tripleRatchetProgAt, chainLenName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
    "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" = entry
  examples_hide_fetches
  rcases hpres with ⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  dsimp only [chainFieldsAt]
  by_cases hpriv : g.priv.bytes = []
  · simp only [hpriv, bytesField, ↓reduceIte, List.length_nil, Nat.add_zero, BitVec.ofNat_eq_ofNat]
    have hovf0 := ult_zero_64 (BitVec.ofNat 64 s1)
    wp_steps
    wp_done
  · have hne0 := ofNat_len_beq_zero_of_ne_nil hpriv hpriv_lt
    have hbf := bv_bytesField_length_of_ne_nil (tag := 2) hpriv rfl
    have hovf := ult_ofNat_add_of_lt hfit12
    have hadd := bv_add_ofNat_comm s1 (bytesField 2 g.priv.bytes).length
    wp_steps
    wp_done

private theorem chainLen_chainKey (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (g : ChainGhost) (c : ReceiverChain) (a : BitVec 64) (s12 : Nat)
    (hck : ∀ ck, c.chainKey = some ck → g.ck.cap.toNat < 2 ^ 63)
    (hfit123 : s12 + (msgField 3 (c.chainKey.map encChainKey)).length < 2 ^ 64)
    (s0 s : State) (fsp : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr chainLenName + 100#64)
    (hrun : s.status = .Running)
    (hpres : Saved64Preserved s0 s fsp)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr chainLenName + 236#64)
      s
      (chainFieldsAt A g c a ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ chainFieldsAt A g c a ∗ Frame) ∧
        Saved64Preserved s0 sm fsp ∧
        sm.readReg64 .x0 = a ∧
        sm.readReg64 .x20 = BitVec.ofNat 64 (s12 + (msgField 3 (c.chainKey.map encChainKey)).length)) := by
  chainLen_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") 158548 100 224
  chainLen_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") 158548 228 236
  chainLen_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") 158548 368 376
  dsimp only [tripleRatchetProgAt, chainLenName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
    "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" = entry
  examples_hide_fetches
  rcases hpres with ⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  dsimp only [chainFieldsAt]
  cases hck_eq : c.chainKey with
  | none =>
    rw [optChainKeyAt_none_offset72_eq]
    simp only [Option.map_none, msgField, List.length_nil, Nat.add_zero]
    have hovf0 := ult_zero_64 (BitVec.ofNat 64 s12)
    wp_steps
    wp_done
  | some ck =>
    have hcap_lt : g.ck.cap.toNat < 2 ^ 63 := hck ck hck_eq
    have hcap_ne := cap_add_one_beq_zero_false hcap_lt
    rw [hck_eq] at hfit123
    rw [optChainKeyAt_some_offset72_eq]
    rcases ck with ⟨key, idx⟩
    by_cases hidx : idx = 0#32
    · subst hidx
      have hmsg36 := msgField3_encChainKey_zero_length key
      simp only [Option.map_some, hmsg36] at hfit123 ⊢
      have hcc36 := ule_ofNat_add_of_lt hfit123
      have hadd36 := bv_add_ofNat_comm s12 36
      wp_steps
      wp_done
    · simp only [Option.map_some] at hfit123 ⊢
      have hidx_beq : (idx == 0#32) = false := beq_eq_false_iff_ne.mpr hidx
      have hu32 := bv_uint32Field1_length_of_ne_zero hidx
      have heck := bv_encChainKey_length ⟨key, idx⟩
      have hmsg := bv_msgField3_encChainKey_length ⟨key, idx⟩
      have hcc := ule_ofNat_add_of_lt hfit123
      have hadd := bv_add_ofNat_comm s12 (msgField 3 (some (encChainKey ⟨key, idx⟩))).length
      wp_steps
      wp_done

private theorem chainLen_mk_body {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hmk_at : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr chainLenName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len"))
      (msgKeyLenSpec A))
    (s0 : State) (fsp v20 v21 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (acc : Nat) (pin : MessageKeyGhost) (mk : MessageKeyGenerator)
      (s : State) (Frame : SepProp),
      acc + mkBodyLen mk < 2 ^ 64 →
      s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr chainLenName + 256#64 →
      s.status = .Running →
      Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = cur →
      s.readReg64 .x20 = v20 →
      s.readReg64 .x21 = v21 →
      s.readReg64 .x22 = BitVec.ofNat 64 acc →
      s.readReg64 .x23 = cnt →
      SepWP (tripleRatchetProgAt b C ctl abs)
        ((tripleRatchetProgAt b C ctl abs).fnAddr chainLenName + 300#64)
        s
        (messageKeyAt A (pin, mk) cur ∗ stackAt fsp msgKeyLenStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ messageKeyAt A (pin, mk) cur ∗ stackAt fsp msgKeyLenStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = cur ∧
          sm.readReg64 .x20 = v20 ∧
          sm.readReg64 .x21 = v21 ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (acc + mkBodyLen mk) ∧
          sm.readReg64 .x23 = cnt) := by
  simp only [msgKeyLenSpec] at hmk_at
  chainLen_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") 158548 256 300
  dsimp only [tripleRatchetProgAt, chainLenName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
    "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" = entry
  examples_hide_fetches
  intro cur cnt acc pin mk s Frame hfit hpc hrun hpres hx19 hx20 hx21 hx22 hx23
  rcases hpres with ⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  have hmk_fit : mkBodyLen mk < 2 ^ 64 := by omega
  have hovf1 := mkBodyLen_ult hmk_fit
  have hbody := bv_mkBodyLen_eq mk
  have hovf2 := ult_ofNat_add_of_lt hfit
  have hadd := bv_add_ofNat_comm acc (mkBodyLen mk)
  wp_steps
  wp_call hmk_at (⟨cur, (pin, mk)⟩ : MsgKeyLenGhost)
  wp_steps
  refine SepWP.align_pre (by rw [hsp]) ?_
  wp_done

private theorem chainLen_mk_loop {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hmk_at : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr chainLenName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len"))
      (msgKeyLenSpec A))
    (s0 : State) (fsp v20 v21 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (MessageKeyGhost × MessageKeyGenerator)) (cur : BitVec 64) (acc : Nat)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      acc + mksBodyLen (rest.map Prod.snd) < 2 ^ 64 →
      s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr chainLenName + 256#64 →
      s.status = .Running →
      Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = cur →
      s.readReg64 .x20 = v20 →
      s.readReg64 .x21 = v21 →
      s.readReg64 .x22 = BitVec.ofNat 64 acc →
      s.readReg64 .x23 = BitVec.ofNat 64 rest.length →
      SepWP (tripleRatchetProgAt b C ctl abs)
        ((tripleRatchetProgAt b C ctl abs).fnAddr chainLenName + 312#64)
        s
        (arrayAt (messageKeyAt A) 104 cur rest ∗ stackAt fsp msgKeyLenStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ arrayAt (messageKeyAt A) 104 cur rest ∗ stackAt fsp msgKeyLenStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧
          sm.readReg64 .x20 = v20 ∧
          sm.readReg64 .x21 = v21 ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (acc + mksBodyLen (rest.map Prod.snd))) := by
  have hbody := chainLen_mk_body (b := b) (C := C) (ctl := ctl)
    hmk_at s0 fsp v20 v21 hfsp_align
  chainLen_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") 158548 300 312
  dsimp only [tripleRatchetProgAt, chainLenName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
    "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨pin, mk⟩
    intro cur acc s Frame _ hlen hfit hpc hrun hpres hx19 hx20 hx21 hx22 hx23
    have hfit_mk : acc + mkBodyLen mk < 2 ^ 64 := by
      simp only [List.map_cons, mksBodyLen] at hfit; omega
    have hfit_tl : (acc + mkBodyLen mk) + mksBodyLen (tl.map Prod.snd) < 2 ^ 64 := by
      simp only [List.map_cons, mksBodyLen] at hfit; omega
    rw [show arrayAt (messageKeyAt A) 104 cur ((pin, mk) :: tl) =
          messageKeyAt A (pin, mk) cur ∗ arrayAt (messageKeyAt A) 104 (cur + 104#64) tl from rfl,
        sep_pull_mk]
    refine SepWP.seq_clean (mid := entry + bv% (300))
      (hbody cur (BitVec.ofNat 64 ((pin, mk) :: tl).length) acc pin mk s
        (arrayAt (messageKeyAt A) 104 (cur + 104#64) tl ∗ Frame)
        hfit_mk hpc hrun hpres hx19 hx20 hx21 hx22 hx23) ?_
    intro s1 hpc1 hrun1 ⟨⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, List.map_cons, List.map_nil,
        mksBodyLen, Nat.add_zero, arrayAt, emp_sepConj, BitVec.ofNat_eq_ofNat] at hx23_1 ⊢
      wp_steps
      wp_done
    | cons hd2 tl2 =>
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len : (hd2 :: tl2).length * 104 < 2 ^ 63 := Getters.DropGlueFacts.tail_len_mul_lt hlen
      rw [show ((pin, mk) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          Getters.DropGlueFacts.ofNat_succ_eq_add_one] at hx23_1
      have hne1 : (BitVec.ofNat 64 (hd2 :: tl2).length + 1#64 != 1#64) = true := by
        have h := Getters.DropGlueFacts.ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
        simpa [bne] using h
      wp_steps
      rw [sep_push_mk]
      have hacc_assoc :
          acc + mksBodyLen (List.map Prod.snd ((pin, mk) :: hd2 :: tl2)) =
            (acc + mkBodyLen mk) + mksBodyLen (List.map Prod.snd (hd2 :: tl2)) := by
        simp only [List.map_cons, mksBodyLen, Nat.add_assoc]
      rw [hacc_assoc]
      refine SepWP.mono
        (ih (cur + 104#64) (acc + mkBodyLen mk) _ (messageKeyAt A (pin, mk) cur ∗ Frame)
          htl_ne htl_len hfit_tl rfl (by assumption)
          ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
          rfl hx20_1 hx21_1 hx22_1 rfl) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      rw [sep_rejoin_mk]
      exact Entails.refl _

/-- `Chain::encoded_len` (`0x26aa0`) satisfies `chainLenSpec` given `MessageKey::encoded_len`. -/
theorem chainLen_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hmk : OkAt b C ctl abs msgKeyLenName (msgKeyLenSpec A)) :
    OkAt b C ctl abs chainLenName (chainLenSpec A) := by
  have hmk_at : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr chainLenName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len"))
      (msgKeyLenSpec A) := by
    rw [← msgKeyLen_fnAddr_eq]
    exact hmk
  simp only [OkAt, chainLenSpec]
  have hphases : PLift (_ ∧ _ ∧ _ ∧ _) :=
    ⟨⟨chainLen_senderRatchetKey b C A ctl abs,
      chainLen_senderRatchetKeyPrivate b C A ctl abs,
      chainLen_chainKey b C A ctl abs,
      chainLen_mk_loop (b := b) (C := C) (ctl := ctl) hmk_at⟩⟩
  chainLen_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") 158548 236 256
  chainLen_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") 158548 312 356
  have hname_eq : chainLenName =
      "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" := rfl
  have hsp2_eq : tripleRatchetProgAt b C ctl abs =
      libsignalSessionCode.rebase b (Rust.withPanics (tripleRatchetExterns C ctl abs)) := rfl
  rw [hname_eq, hsp2_eq] at hphases ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
    "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" = entry
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨a, g, c⟩
  dsimp only at hpre ⊢
  rcases hphases with ⟨⟨hp1a, hp1b, hp2, hloop⟩⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hfit_all : (encChainMem (g, c)).length < 2 ^ 32 := by assumption
  have halign : (s0.sp &&& 15#64 == 0#64) = true := by assumption
  have halign' : s0.sp &&& 15#64 = 0#64 := by simpa [beq_iff_eq] using halign
  have hfsp_align : ((s0.sp - 64#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 64#64 halign (by decide)
  have hfsp_align' : (s0.sp - 64#64) &&& 15#64 = 0#64 := by
    simpa [beq_iff_eq] using hfsp_align
  rw [encChainMem_length] at hfit_all
  nth_rw 1 [stackAt_chainLen_split s0.sp]
  rw [cells8_sub64_eq s0.sp]
  wp_pull_exists
  rename_i v0 v1 v2 v3 v4 v5 v6 v7
  refine SepWP.weaken_pre (sepConj_mono_left (chainAt_expose A g c a)) ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hsrk_des, hmax, hklen, hsrk_lt, hpriv_lt, hck_lt, hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  set s1 := (bytesField 1 g.srk.bytes).length
  set s2 := (bytesField 2 g.priv.bytes).length
  set s3 := (msgField 3 (c.chainKey.map encChainKey)).length
  set s4 := ((c.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length
  have hfit12 : s1 + s2 < 2 ^ 64 := by omega
  have hfit123 : (s1 + s2) + s3 < 2 ^ 64 := by omega
  have hfit1234 : ((s1 + s2) + s3) + s4 < 2 ^ 64 := by omega
  have hpre_eq :
      chainFieldsAt A g c a ∗
        arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
        stackAt (s0.sp - 64#64) msgKeyLenStack ∗
        chainLenSavedAt s0.sp v0 v1 v2 v3 v4 v5 v6 v7 =
      chainFieldsAt A g c a ∗
        chainLenSavedAt s0.sp v0 v1 v2 v3 v4 v5 v6 v7 ∗
        (arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
          stackAt (s0.sp - 64#64) msgKeyLenStack) := by
    ac_rfl
  rw [hpre_eq]
  refine SepWP.seq_clean
    (hp1a g c a hsrk_lt v0 v1 v2 v3 v4 v5 v6 v7 s0
      (arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
        stackAt (s0.sp - 64#64) msgKeyLenStack)
      (by assumption) (by assumption) halign hx0) ?_
  intro s1_st hpc1 hrun1 ⟨hpres1, hx0_1, hx8_1⟩
  let SavedSlot : SepProp :=
    chainLenSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x23) v3 (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)
  let RestFrame : SepProp :=
    SavedSlot ∗
      (arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
        stackAt (s0.sp - 64#64) msgKeyLenStack)
  refine SepWP.seq_clean
    (hp1b g c a s1 hpriv_lt hfit12 s0 s1_st (s0.sp - 64#64) RestFrame
      hpc1 hrun1 hpres1 hx0_1 hx8_1) ?_
  intro s2_st hpc2 hrun2 ⟨hpres2, hx0_2, hx8_2⟩
  refine SepWP.seq_clean
    (hp2 g c a (s1 + s2) hck_lt hfit123 s0 s2_st (s0.sp - 64#64) RestFrame
      hpc2 hrun2 hpres2 hx0_2 hx8_2) ?_
  intro s3_st hpc3 hrun3 ⟨hpres3, hx0_3, hx20_3⟩


  have hrestore_all :
      chainFieldsAt A g c a ∗
        arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
        stackAt (s0.sp - 64#64) msgKeyLenStack ∗
        SavedSlot ⊢
      protoChainAt A (g, c) a ∗ stackAt s0.sp chainLenStack := by
    have hpull :
        (chainFieldsAt A g c a ∗
          arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
          stackAt (s0.sp - 64#64) msgKeyLenStack ∗
          SavedSlot) =
        ((chainFieldsAt A g c a ∗
          arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys)) ∗
         (stackAt (s0.sp - 64#64) msgKeyLenStack ∗ SavedSlot)) := by
      ac_rfl
    rw [hpull]
    exact sepConj_mono
      (chainAt_restore A g c a hsrk_des hmax hklen hlen_le hcap_lt hptr_ne)
      (stack_restore_chainLen s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x23) v3 (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19))
  cases hmks : g.keys.zip c.messageKeys with
  | nil =>
    have hcmk_nil : c.messageKeys = [] := by
      have h := zip_map_snd_eq hklen
      rw [hmks, List.map_nil] at h
      exact h.symm
    have hs4_0 : s4 = 0 := by simp [s4, hcmk_nil]
    have henc_eq : (encChainMem (g, c)).length = (s1 + s2) + s3 := by
      rw [encChainMem_length]
      change s1 + s2 + s3 + s4 = (s1 + s2) + s3
      omega
    rcases hpres3 with ⟨hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩
    dsimp only [RestFrame, SavedSlot, chainFieldsAt, chainLenSavedAt]
    simp only [hmks, List.length_nil, BitVec.ofNat_eq_ofNat, henc_eq]
    have hcc0 := ule_zero_64 0#64
    have hovf0 := ult_zero_64 (BitVec.ofNat 64 ((s1 + s2) + s3))
    wp_steps
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq ?_) hrestore_all) ?_
    · dsimp only [SavedSlot, chainFieldsAt, chainLenSavedAt]; simp only [hmks]; ac_rfl
    · wp_done
  | cons hd tl =>
    have hmks_ne : hd :: tl ≠ [] := List.cons_ne_nil _ _
    have hmks_len_lt : (hd :: tl).length * 104 < 2 ^ 63 := by
      simpa [hmks] using hlen_lt
    have hne0 := Getters.DropGlueFacts.ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hmks_len_lt
    have hmap_snd : (hd :: tl).map Prod.snd = c.messageKeys := by
      rw [← hmks]
      exact zip_map_snd_eq hklen
    have hlen_mks : (hd :: tl).length = c.messageKeys.length := by
      rw [← hmks]
      exact zip_length_eq hklen
    have hs4_eq : s4 = mksBodyLen c.messageKeys + c.messageKeys.length :=
      flatten_lenField4_length c.messageKeys
    have hfit_loop : 0 + mksBodyLen ((hd :: tl).map Prod.snd) < 2 ^ 64 := by
      rw [Nat.zero_add, hmap_snd]; omega
    refine SepWP.seq_clean (mid := entry + bv% (256))
      (P_mid := arrayAt (messageKeyAt A) 104 g.mkPtr (hd :: tl) ∗
        stackAt (s0.sp - 64#64) msgKeyLenStack ∗
        (chainFieldsAt A g c a ∗ SavedSlot))
      (Q := fun sm =>
        Saved64Preserved s0 sm (s0.sp - 64#64) ∧
        sm.readReg64 .x19 = g.mkPtr ∧
        sm.readReg64 .x20 = BitVec.ofNat 64 ((s1 + s2) + s3) ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (hd :: tl).length ∧
        sm.readReg64 .x22 = 0#64 ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 (hd :: tl).length)
      ?_ ?_
    · rcases hpres3 with ⟨hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩
      dsimp only [RestFrame, chainFieldsAt]
      simp only [hmks]
      change s3_st.readReg64 .x20 = BitVec.ofNat 64 ((s1 + s2) + s3) at hx20_3
      wp_steps
      refine SepWP.align_pre (by ac_rfl) ?_
      wp_done
    · intro s4_st hpc4 hrun4 ⟨hpres4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4⟩
      refine SepWP.seq_clean (mid := entry + bv% (312))
        (hloop s0 (s0.sp - 64#64) (BitVec.ofNat 64 ((s1 + s2) + s3)) (BitVec.ofNat 64 (hd :: tl).length)
          hfsp_align (hd :: tl) g.mkPtr 0 s4_st (chainFieldsAt A g c a ∗ SavedSlot)
          hmks_ne hmks_len_lt hfit_loop hpc4 hrun4 hpres4
          hx19_4 hx20_4 hx21_4 hx22_4 hx23_4) ?_
      intro s5_st hpc5 hrun5 ⟨⟨hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx20_5, hx21_5, hx22_5⟩
      rw [Nat.zero_add, hmap_snd] at hx22_5
      rw [hlen_mks] at hx21_5
      have hfit_s4 : mksBodyLen c.messageKeys + c.messageKeys.length < 2 ^ 64 := by omega
      have hadd_s4 :
          BitVec.ofNat 64 (mksBodyLen c.messageKeys) + BitVec.ofNat 64 c.messageKeys.length =
            BitVec.ofNat 64 (mksBodyLen c.messageKeys + c.messageKeys.length) :=
        (BitVec.ofNat_add (mksBodyLen c.messageKeys) c.messageKeys.length).symm
      have hovf_s4' := ult_ofNat_add_left_of_lt hfit_s4
      have hovf_s4 :
          BitVec.ult
            (BitVec.ofNat 64 (mksBodyLen c.messageKeys) + BitVec.ofNat 64 c.messageKeys.length)
            (BitVec.ofNat 64 (mksBodyLen c.messageKeys)) = false := by
        rw [hadd_s4]
        exact hovf_s4'
      have hfit_tot : ((s1 + s2) + s3) + (mksBodyLen c.messageKeys + c.messageKeys.length) < 2 ^ 64 := by omega
      have hovf_total := ult_ofNat_add_of_lt hfit_tot
      have hadd_total := bv_add_ofNat_comm ((s1 + s2) + s3) (mksBodyLen c.messageKeys + c.messageKeys.length)
      have henc_eq : (encChainMem (g, c)).length =
          ((s1 + s2) + s3) + (mksBodyLen c.messageKeys + c.messageKeys.length) := by
        rw [encChainMem_length, ← hs4_eq]
      dsimp only [SavedSlot, chainLenSavedAt]
      simp only [henc_eq]
      wp_steps
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq ?_) hrestore_all) ?_
      · dsimp only [SavedSlot, chainFieldsAt, chainLenSavedAt]; simp only [hmks]; ac_rfl
      · wp_done

/-! ## Relocatable `[LibsignalPlacement]` proofs -/

section Placed

open CryptoVerification.E2E.Record.Placed

private theorem chainLen_senderRatchetKey_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (g : ChainGhost) (c : ReceiverChain) (a : BitVec 64)
    (hsrk_lt : g.srk.bytes.length < 2 ^ 63)
    (v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64)
    (s0 : State) (Frame : SepProp)
    (hpc : s0.pc = (blkPl_88).base)
    (hrun : s0.status = .Running)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = a) :
    SepWP (lsProg_88 H)
      ((blkPl_88).base + 56#64)
      s0
      (chainFieldsAt A g c a ∗
        chainLenSavedAt s0.sp v0 v1 v2 v3 v4 v5 v6 v7 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ chainFieldsAt A g c a ∗
          chainLenSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x23) v3 (s0.readReg64 .x22) (s0.readReg64 .x21)
            (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
          Frame) ∧
        Saved64Preserved s0 sm (s0.sp - 64#64) ∧
        sm.readReg64 .x0 = a ∧
        sm.readReg64 .x8 = BitVec.ofNat 64 (bytesField 1 g.srk.bytes).length) := by
  have halign' : s0.sp &&& 15#64 = 0#64 := by
    simpa [beq_iff_eq] using halign
  dsimp only [chainFieldsAt, chainLenSavedAt]
  by_cases hsrk : g.srk.bytes = []
  · simp only [hsrk, bytesField, ↓reduceIte, List.length_nil, BitVec.ofNat_eq_ofNat]
    wp_steps
    wp_done
  · have hne0 := ofNat_len_beq_zero_of_ne_nil hsrk hsrk_lt
    have hbf := bv_bytesField_length_of_ne_nil (tag := 1) hsrk rfl
    wp_steps
    wp_done

private theorem chainLen_senderRatchetKeyPrivate_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (g : ChainGhost) (c : ReceiverChain) (a : BitVec 64) (s1 : Nat)
    (hpriv_lt : g.priv.bytes.length < 2 ^ 63)
    (hfit12 : s1 + (bytesField 2 g.priv.bytes).length < 2 ^ 64)
    (s0 s : State) (fsp : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_88).base + 56#64)
    (hrun : s.status = .Running)
    (hpres : Saved64Preserved s0 s fsp)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1) :
    SepWP (lsProg_88 H)
      ((blkPl_88).base + 100#64)
      s
      (chainFieldsAt A g c a ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ chainFieldsAt A g c a ∗ Frame) ∧
        Saved64Preserved s0 sm fsp ∧
        sm.readReg64 .x0 = a ∧
        sm.readReg64 .x8 = BitVec.ofNat 64 (s1 + (bytesField 2 g.priv.bytes).length)) := by
  rcases hpres with ⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  dsimp only [chainFieldsAt]
  by_cases hpriv : g.priv.bytes = []
  · simp only [hpriv, bytesField, ↓reduceIte, List.length_nil, Nat.add_zero, BitVec.ofNat_eq_ofNat]
    have hovf0 := ult_zero_64 (BitVec.ofNat 64 s1)
    wp_steps
    wp_done
  · have hne0 := ofNat_len_beq_zero_of_ne_nil hpriv hpriv_lt
    have hbf := bv_bytesField_length_of_ne_nil (tag := 2) hpriv rfl
    have hovf := ult_ofNat_add_of_lt hfit12
    have hadd := bv_add_ofNat_comm s1 (bytesField 2 g.priv.bytes).length
    wp_steps
    wp_done

private theorem chainLen_chainKey_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (g : ChainGhost) (c : ReceiverChain) (a : BitVec 64) (s12 : Nat)
    (hck : ∀ ck, c.chainKey = some ck → g.ck.cap.toNat < 2 ^ 63)
    (hfit123 : s12 + (msgField 3 (c.chainKey.map encChainKey)).length < 2 ^ 64)
    (s0 s : State) (fsp : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_88).base + 100#64)
    (hrun : s.status = .Running)
    (hpres : Saved64Preserved s0 s fsp)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12) :
    SepWP (lsProg_88 H)
      ((blkPl_88).base + 236#64)
      s
      (chainFieldsAt A g c a ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ chainFieldsAt A g c a ∗ Frame) ∧
        Saved64Preserved s0 sm fsp ∧
        sm.readReg64 .x0 = a ∧
        sm.readReg64 .x20 = BitVec.ofNat 64 (s12 + (msgField 3 (c.chainKey.map encChainKey)).length)) := by
  rcases hpres with ⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  dsimp only [chainFieldsAt]
  cases hck_eq : c.chainKey with
  | none =>
    rw [optChainKeyAt_none_offset72_eq]
    simp only [Option.map_none, msgField, List.length_nil, Nat.add_zero]
    have hovf0 := ult_zero_64 (BitVec.ofNat 64 s12)
    wp_steps
    wp_done
  | some ck =>
    have hcap_lt : g.ck.cap.toNat < 2 ^ 63 := hck ck hck_eq
    have hcap_ne := cap_add_one_beq_zero_false hcap_lt
    rw [hck_eq] at hfit123
    rw [optChainKeyAt_some_offset72_eq]
    rcases ck with ⟨key, idx⟩
    by_cases hidx : idx = 0#32
    · subst hidx
      have hmsg36 := msgField3_encChainKey_zero_length key
      simp only [Option.map_some, hmsg36] at hfit123 ⊢
      have hcc36 := ule_ofNat_add_of_lt hfit123
      have hadd36 := bv_add_ofNat_comm s12 36
      wp_steps
      wp_done
    · simp only [Option.map_some] at hfit123 ⊢
      have hidx_beq : (idx == 0#32) = false := beq_eq_false_iff_ne.mpr hidx
      have hu32 := bv_uint32Field1_length_of_ne_zero hidx
      have heck := bv_encChainKey_length ⟨key, idx⟩
      have hmsg := bv_msgField3_encChainKey_length ⟨key, idx⟩
      have hcc := ule_ofNat_add_of_lt hfit123
      have hadd := bv_add_ofNat_comm s12 (msgField 3 (some (encChainKey ⟨key, idx⟩))).length
      wp_steps
      wp_done

private theorem chainLen_mk_body_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base (msgKeyLenSpec A))
    (s0 : State) (fsp v20 v21 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (acc : Nat) (pin : MessageKeyGhost) (mk : MessageKeyGenerator)
      (s : State) (Frame : SepProp),
      LibsignalCodeLoaded lsmpl s.mem →
      acc + mkBodyLen mk < 2 ^ 64 →
      s.pc = (blkPl_88).base + 256#64 →
      s.status = .Running →
      Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = cur →
      s.readReg64 .x20 = v20 →
      s.readReg64 .x21 = v21 →
      s.readReg64 .x22 = BitVec.ofNat 64 acc →
      s.readReg64 .x23 = cnt →
      SepWP (lsProg_88 H)
        ((blkPl_88).base + 300#64)
        s
        (messageKeyAt A (pin, mk) cur ∗ stackAt fsp msgKeyLenStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ messageKeyAt A (pin, mk) cur ∗ stackAt fsp msgKeyLenStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = cur ∧
          sm.readReg64 .x20 = v20 ∧
          sm.readReg64 .x21 = v21 ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (acc + mkBodyLen mk) ∧
          sm.readReg64 .x23 = cnt) := by
  intro cur cnt acc pin mk s Frame hcl hfit hpc hrun hpres hx19 hx20 hx21 hx22 hx23
  have hmk_call := lscall_blk (callerProg := lsProg_88 H) hmk hcl
  simp only [withMemEq, msgKeyLenSpec] at hmk_call
  rcases hpres with ⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  have hmk_fit : mkBodyLen mk < 2 ^ 64 := by omega
  have hovf1 := mkBodyLen_ult hmk_fit
  have hbody := bv_mkBodyLen_eq mk
  have hovf2 := ult_ofNat_add_of_lt hfit
  have hadd := bv_add_ofNat_comm acc (mkBodyLen mk)
  wp_steps
  wp_call hmk_call (⟨cur, (pin, mk)⟩ : MsgKeyLenGhost)
  wp_steps
  refine SepWP.align_pre (by rw [hsp]) ?_
  wp_done

private theorem chainLen_mk_loop_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base (msgKeyLenSpec A))
    (s0 : State) (fsp v20 v21 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (MessageKeyGhost × MessageKeyGenerator)) (cur : BitVec 64) (acc : Nat)
      (s : State) (Frame : SepProp),
      LibsignalCodeLoaded lsmpl s.mem →
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      acc + mksBodyLen (rest.map Prod.snd) < 2 ^ 64 →
      s.pc = (blkPl_88).base + 256#64 →
      s.status = .Running →
      Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = cur →
      s.readReg64 .x20 = v20 →
      s.readReg64 .x21 = v21 →
      s.readReg64 .x22 = BitVec.ofNat 64 acc →
      s.readReg64 .x23 = BitVec.ofNat 64 rest.length →
      SepWP (lsProg_88 H)
        ((blkPl_88).base + 312#64)
        s
        (arrayAt (messageKeyAt A) 104 cur rest ∗ stackAt fsp msgKeyLenStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ arrayAt (messageKeyAt A) 104 cur rest ∗ stackAt fsp msgKeyLenStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧
          sm.readReg64 .x20 = v20 ∧
          sm.readReg64 .x21 = v21 ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (acc + mksBodyLen (rest.map Prod.snd))) := by
  have hbody := chainLen_mk_body_placed hmk s0 fsp v20 v21 hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨pin, mk⟩
    intro cur acc s Frame hcl _ hlen hfit hpc hrun hpres hx19 hx20 hx21 hx22 hx23
    have hfit_mk : acc + mkBodyLen mk < 2 ^ 64 := by
      simp only [List.map_cons, mksBodyLen] at hfit; omega
    have hfit_tl : (acc + mkBodyLen mk) + mksBodyLen (tl.map Prod.snd) < 2 ^ 64 := by
      simp only [List.map_cons, mksBodyLen] at hfit; omega
    rw [show arrayAt (messageKeyAt A) 104 cur ((pin, mk) :: tl) =
          messageKeyAt A (pin, mk) cur ∗ arrayAt (messageKeyAt A) 104 (cur + 104#64) tl from rfl,
        sep_pull_mk]
    refine sepWP_seq_clean_lscl hcl (mid := (blkPl_88).base + bv% (300))
      (hbody cur (BitVec.ofNat 64 ((pin, mk) :: tl).length) acc pin mk s
        (arrayAt (messageKeyAt A) 104 (cur + 104#64) tl ∗ Frame)
        hcl hfit_mk hpc hrun hpres hx19 hx20 hx21 hx22 hx23) ?_
    intro s1 hpc1 hrun1 hcl1 ⟨⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, List.map_cons, List.map_nil,
        mksBodyLen, Nat.add_zero, arrayAt, emp_sepConj, BitVec.ofNat_eq_ofNat] at hx23_1 ⊢
      wp_steps
      wp_done
    | cons hd2 tl2 =>
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len : (hd2 :: tl2).length * 104 < 2 ^ 63 := Getters.DropGlueFacts.tail_len_mul_lt hlen
      rw [show ((pin, mk) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          Getters.DropGlueFacts.ofNat_succ_eq_add_one] at hx23_1
      have hne1 : (BitVec.ofNat 64 (hd2 :: tl2).length + 1#64 != 1#64) = true := by
        have h := Getters.DropGlueFacts.ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
        simpa [bne] using h
      refine sepWP_seq_clean_lscl hcl1 (mid := (blkPl_88).base + bv% (256))
        (P_mid := messageKeyAt A (pin, mk) cur ∗ stackAt fsp msgKeyLenStack ∗
          (arrayAt (messageKeyAt A) 104 (cur + 104#64) (hd2 :: tl2) ∗ Frame))
        (Q := fun sm =>
          Saved64Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = cur + 104#64 ∧
          sm.readReg64 .x20 = v20 ∧
          sm.readReg64 .x21 = v21 ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (acc + mkBodyLen mk) ∧
          sm.readReg64 .x23 = BitVec.ofNat 64 (hd2 :: tl2).length)
        (by
          rcases hpres with _
          wp_steps
          wp_done) ?_
      intro s2 hpc2 hrun2 hcl2 ⟨hpres2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2⟩
      rw [sep_push_mk]
      have hacc_assoc :
          acc + mksBodyLen (List.map Prod.snd ((pin, mk) :: hd2 :: tl2)) =
            (acc + mkBodyLen mk) + mksBodyLen (List.map Prod.snd (hd2 :: tl2)) := by
        simp only [List.map_cons, mksBodyLen, Nat.add_assoc]
      rw [hacc_assoc]
      refine SepWP.mono
        (ih (cur + 104#64) (acc + mkBodyLen mk) s2 (messageKeyAt A (pin, mk) cur ∗ Frame)
          hcl2 htl_ne htl_len hfit_tl hpc2 hrun2 hpres2
          hx19_2 hx20_2 hx21_2 hx22_2 hx23_2) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      rw [sep_rejoin_mk]
      exact Entails.refl _

/-- Relocatable `Chain::encoded_len` (block `88`) contract given `MessageKey::encoded_len` (block `118`). -/
theorem chainLen_placed_ok_of_msgKeyLen [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base (msgKeyLenSpec A)) :
    subroutine_ok (lsProg_88 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)) := by
  have hphases : PLift (_ ∧ _ ∧ _ ∧ _) :=
    ⟨⟨chainLen_senderRatchetKey_placed A H,
      chainLen_senderRatchetKeyPrivate_placed A H,
      chainLen_chainKey_placed A H,
      chainLen_mk_loop_placed hmk⟩⟩
  simp only [withLsCodeLoaded, chainLenSpec]
  wp_init x s0
  rcases x with ⟨a, g, c⟩
  dsimp only at hpre ⊢
  rcases hphases with ⟨⟨hp1a, hp1b, hp2, hloop⟩⟩
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hfit_all : (encChainMem (g, c)).length < 2 ^ 32 := by assumption
  have halign : (s0.sp &&& 15#64 == 0#64) = true := by assumption
  have halign' : s0.sp &&& 15#64 = 0#64 := by simpa [beq_iff_eq] using halign
  have hfsp_align : ((s0.sp - 64#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 64#64 halign (by decide)
  have hfsp_align' : (s0.sp - 64#64) &&& 15#64 = 0#64 := by
    simpa [beq_iff_eq] using hfsp_align
  rw [encChainMem_length] at hfit_all
  nth_rw 1 [stackAt_chainLen_split s0.sp]
  rw [cells8_sub64_eq s0.sp]
  wp_pull_exists
  rename_i v0 v1 v2 v3 v4 v5 v6 v7
  refine SepWP.weaken_pre (sepConj_mono_left (chainAt_expose A g c a)) ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hsrk_des, hmax, hklen, hsrk_lt, hpriv_lt, hck_lt, hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  set s1 := (bytesField 1 g.srk.bytes).length
  set s2 := (bytesField 2 g.priv.bytes).length
  set s3 := (msgField 3 (c.chainKey.map encChainKey)).length
  set s4 := ((c.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length
  have hfit12 : s1 + s2 < 2 ^ 64 := by omega
  have hfit123 : (s1 + s2) + s3 < 2 ^ 64 := by omega
  have hfit1234 : ((s1 + s2) + s3) + s4 < 2 ^ 64 := by omega
  have hpre_eq :
      chainFieldsAt A g c a ∗
        arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
        stackAt (s0.sp - 64#64) msgKeyLenStack ∗
        chainLenSavedAt s0.sp v0 v1 v2 v3 v4 v5 v6 v7 =
      chainFieldsAt A g c a ∗
        chainLenSavedAt s0.sp v0 v1 v2 v3 v4 v5 v6 v7 ∗
        (arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
          stackAt (s0.sp - 64#64) msgKeyLenStack) := by
    ac_rfl
  rw [hpre_eq]
  refine sepWP_seq_clean_lscl hcl0
    (hp1a g c a hsrk_lt v0 v1 v2 v3 v4 v5 v6 v7 s0
      (arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
        stackAt (s0.sp - 64#64) msgKeyLenStack)
      (by assumption) (by assumption) halign hx0) ?_
  intro s1_st hpc1 hrun1 hcl1 ⟨hpres1, hx0_1, hx8_1⟩
  let SavedSlot : SepProp :=
    chainLenSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x23) v3 (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)
  let RestFrame : SepProp :=
    SavedSlot ∗
      (arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
        stackAt (s0.sp - 64#64) msgKeyLenStack)
  refine sepWP_seq_clean_lscl hcl1
    (hp1b g c a s1 hpriv_lt hfit12 s0 s1_st (s0.sp - 64#64) RestFrame
      hpc1 hrun1 hpres1 hx0_1 hx8_1) ?_
  intro s2_st hpc2 hrun2 hcl2 ⟨hpres2, hx0_2, hx8_2⟩
  refine sepWP_seq_clean_lscl hcl2
    (hp2 g c a (s1 + s2) hck_lt hfit123 s0 s2_st (s0.sp - 64#64) RestFrame
      hpc2 hrun2 hpres2 hx0_2 hx8_2) ?_
  intro s3_st hpc3 hrun3 hcl3 ⟨hpres3, hx0_3, hx20_3⟩
  have hrestore_all :
      chainFieldsAt A g c a ∗
        arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
        stackAt (s0.sp - 64#64) msgKeyLenStack ∗
        SavedSlot ⊢
      protoChainAt A (g, c) a ∗ stackAt s0.sp chainLenStack := by
    have hpull :
        (chainFieldsAt A g c a ∗
          arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
          stackAt (s0.sp - 64#64) msgKeyLenStack ∗
          SavedSlot) =
        ((chainFieldsAt A g c a ∗
          arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys)) ∗
         (stackAt (s0.sp - 64#64) msgKeyLenStack ∗ SavedSlot)) := by
      ac_rfl
    rw [hpull]
    exact sepConj_mono
      (chainAt_restore A g c a hsrk_des hmax hklen hlen_le hcap_lt hptr_ne)
      (stack_restore_chainLen s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x23) v3 (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19))
  cases hmks : g.keys.zip c.messageKeys with
  | nil =>
    have hcmk_nil : c.messageKeys = [] := by
      have h := zip_map_snd_eq hklen
      rw [hmks, List.map_nil] at h
      exact h.symm
    have hs4_0 : s4 = 0 := by simp [s4, hcmk_nil]
    have henc_eq : (encChainMem (g, c)).length = (s1 + s2) + s3 := by
      rw [encChainMem_length]
      change s1 + s2 + s3 + s4 = (s1 + s2) + s3
      omega
    rcases hpres3 with ⟨hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩
    dsimp only [RestFrame, SavedSlot, chainFieldsAt, chainLenSavedAt]
    simp only [hmks, List.length_nil, BitVec.ofNat_eq_ofNat, henc_eq]
    have hcc0 := ule_zero_64 0#64
    have hovf0 := ult_zero_64 (BitVec.ofNat 64 ((s1 + s2) + s3))
    wp_steps
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq ?_) hrestore_all) ?_
    · dsimp only [SavedSlot, chainFieldsAt, chainLenSavedAt]; simp only [hmks]; ac_rfl
    · wp_done
  | cons hd tl =>
    have hmks_ne : hd :: tl ≠ [] := List.cons_ne_nil _ _
    have hmks_len_lt : (hd :: tl).length * 104 < 2 ^ 63 := by
      simpa [hmks] using hlen_lt
    have hne0 := Getters.DropGlueFacts.ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hmks_len_lt
    have hmap_snd : (hd :: tl).map Prod.snd = c.messageKeys := by
      rw [← hmks]
      exact zip_map_snd_eq hklen
    have hlen_mks : (hd :: tl).length = c.messageKeys.length := by
      rw [← hmks]
      exact zip_length_eq hklen
    have hs4_eq : s4 = mksBodyLen c.messageKeys + c.messageKeys.length :=
      flatten_lenField4_length c.messageKeys
    have hfit_loop : 0 + mksBodyLen ((hd :: tl).map Prod.snd) < 2 ^ 64 := by
      rw [Nat.zero_add, hmap_snd]; omega
    refine sepWP_seq_clean_lscl hcl3 (mid := (blkPl_88).base + bv% (256))
      (P_mid := arrayAt (messageKeyAt A) 104 g.mkPtr (hd :: tl) ∗
        stackAt (s0.sp - 64#64) msgKeyLenStack ∗
        (chainFieldsAt A g c a ∗ SavedSlot))
      (Q := fun sm =>
        Saved64Preserved s0 sm (s0.sp - 64#64) ∧
        sm.readReg64 .x19 = g.mkPtr ∧
        sm.readReg64 .x20 = BitVec.ofNat 64 ((s1 + s2) + s3) ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (hd :: tl).length ∧
        sm.readReg64 .x22 = 0#64 ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 (hd :: tl).length)
      ?_ ?_
    · rcases hpres3 with ⟨hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩
      dsimp only [RestFrame, chainFieldsAt]
      simp only [hmks]
      change s3_st.readReg64 .x20 = BitVec.ofNat 64 ((s1 + s2) + s3) at hx20_3
      wp_steps
      refine SepWP.align_pre (by ac_rfl) ?_
      wp_done
    · intro s4_st hpc4 hrun4 hcl4 ⟨hpres4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4⟩
      refine sepWP_seq_clean_lscl hcl4 (mid := (blkPl_88).base + bv% (312))
        (hloop s0 (s0.sp - 64#64) (BitVec.ofNat 64 ((s1 + s2) + s3)) (BitVec.ofNat 64 (hd :: tl).length)
          hfsp_align (hd :: tl) g.mkPtr 0 s4_st (chainFieldsAt A g c a ∗ SavedSlot)
          hcl4 hmks_ne hmks_len_lt hfit_loop hpc4 hrun4 hpres4
          hx19_4 hx20_4 hx21_4 hx22_4 hx23_4) ?_
      intro s5_st hpc5 hrun5 _hcl5 ⟨⟨hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx20_5, hx21_5, hx22_5⟩
      rw [Nat.zero_add, hmap_snd] at hx22_5
      rw [hlen_mks] at hx21_5
      have hfit_s4 : mksBodyLen c.messageKeys + c.messageKeys.length < 2 ^ 64 := by omega
      have hadd_s4 :
          BitVec.ofNat 64 (mksBodyLen c.messageKeys) + BitVec.ofNat 64 c.messageKeys.length =
            BitVec.ofNat 64 (mksBodyLen c.messageKeys + c.messageKeys.length) :=
        (BitVec.ofNat_add (mksBodyLen c.messageKeys) c.messageKeys.length).symm
      have hovf_s4' := ult_ofNat_add_left_of_lt hfit_s4
      have hovf_s4 :
          BitVec.ult
            (BitVec.ofNat 64 (mksBodyLen c.messageKeys) + BitVec.ofNat 64 c.messageKeys.length)
            (BitVec.ofNat 64 (mksBodyLen c.messageKeys)) = false := by
        rw [hadd_s4]
        exact hovf_s4'
      have hfit_tot : ((s1 + s2) + s3) + (mksBodyLen c.messageKeys + c.messageKeys.length) < 2 ^ 64 := by omega
      have hovf_total := ult_ofNat_add_of_lt hfit_tot
      have hadd_total := bv_add_ofNat_comm ((s1 + s2) + s3) (mksBodyLen c.messageKeys + c.messageKeys.length)
      have henc_eq : (encChainMem (g, c)).length =
          ((s1 + s2) + s3) + (mksBodyLen c.messageKeys + c.messageKeys.length) := by
        rw [encChainMem_length, ← hs4_eq]
      dsimp only [SavedSlot, chainLenSavedAt]
      simp only [henc_eq]
      wp_steps
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq ?_) hrestore_all) ?_
      · dsimp only [SavedSlot, chainFieldsAt, chainLenSavedAt]; simp only [hmks]; ac_rfl
      · wp_done

/-- Relocatable `Chain::encoded_len` (block `88`) contract under `[LibsignalPlacement]`. -/
theorem chainLen_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_88 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)) :=
  chainLen_placed_ok_of_msgKeyLen A H (msgKeyLen_placed_ok A H)

end Placed

end CryptoVerification.E2E.Record.Serialization
