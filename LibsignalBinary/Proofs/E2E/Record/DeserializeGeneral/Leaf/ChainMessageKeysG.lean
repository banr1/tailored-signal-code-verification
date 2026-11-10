/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances
public import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.ChainKeyEpilogue
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Steps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

/-!
# Tag-4 Field Leaf (`chainMessageKeysG_ok`) for General `message::merge<Chain>`

Proves `chainMessageKeysG_ok` (`+0x120 → +0x120`, `k → k + 1`) for nested `MessageKey` entries
(tag `4`, decoding optional `counter` tag `1` and 32-byte `seed` tag `5` and pushing into
`Vec<MessageKey>` at `a + 0x30`, growing capacity via `RawVec<Chain>::grow_one` when `len = cap`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter BytesMergeOk Int32MergeOk)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? sessionImg0
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainMergeStateSimp.sp_setPC_pre_seedChain ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setPC_pre_seedChain ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setPC_pre_seedChain ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setPC_pre_seedChain ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
attribute [local simp, local arm64_norm] ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## Pure `ChainG`, `ChainField`, and `encMessageKey` Helpers -/

theorem chainField_eq_key_of_tag4 {fl : ChainField} (h : fl.tag = 4) :
    ∃ mk : MessageKeyGenerator, fl = .key mk := by
  cases fl <;> simp [ChainField.tag] at h; exact ⟨_, rfl⟩

theorem mem_keys_of_key_mem_fields {c : ChainG} {mk : MessageKeyGenerator}
    (h : ChainField.key mk ∈ c.fields) : mk ∈ c.keys := by
  unfold ChainG.fields at h
  simp only [List.mem_append, List.mem_map, ChainField.key.injEq, exists_eq_right] at h
  rcases h with ((h1 | h2) | h3) | h4
  · split at h1 <;> simp at h1
  · split at h2 <;> simp at h2
  · split at h3 <;> simp at h3
  · exact h4

def chainFieldKeys : ChainField → List MessageKeyGenerator
  | .key m => [m]
  | _ => []

theorem chainG_apply_keys (c : ChainG) (fl : ChainField) :
    (c.apply fl).keys = c.keys ++ chainFieldKeys fl := by
  cases fl <;> simp [ChainG.apply, chainFieldKeys]

theorem foldl_chainG_apply_keys (fs : List ChainField) (c : ChainG) :
    (fs.foldl ChainG.apply c).keys = c.keys ++ fs.flatMap chainFieldKeys := by
  induction fs generalizing c with
  | nil => simp
  | cons fl fs ih => simp only [List.foldl_cons, List.flatMap_cons, ih, chainG_apply_keys, List.append_assoc]

theorem chainG_fields_flatMap_keys (c : ChainG) :
    c.fields.flatMap chainFieldKeys = c.keys := by
  unfold ChainG.fields
  have h1 : (if c.srk = [] then [] else [ChainField.srk c.srk]).flatMap chainFieldKeys = [] := by split <;> rfl
  have h2 : (if c.priv = [] then [] else [ChainField.priv c.priv]).flatMap chainFieldKeys = [] := by split <;> rfl
  have h4 : ∀ ks : List MessageKeyGenerator, (ks.map ChainField.key).flatMap chainFieldKeys = ks := by
    intro ks; induction ks with | nil => rfl | cons m ks ih => simp [chainFieldKeys, ih]
  rw [List.flatMap_append, List.flatMap_append, List.flatMap_append, h1, h2, h4]
  rcases c.ck with _ | ⟨i, k⟩ <;> rfl

theorem chainGAfter_keys_length_le (c : ChainG) (k : Nat) :
    (chainGAfter c k).keys.length ≤ c.keys.length := by
  unfold chainGAfter; rw [foldl_chainG_apply_keys]; dsimp only [ChainG.empty]
  rw [List.nil_append, ← chainG_fields_flatMap_keys c]
  conv => rhs; rw [← List.take_append_drop k c.fields]
  rw [List.flatMap_append, List.length_append]; omega

theorem chainGAfter_succ_of_key {c : ChainG} {k : Nat} (hk : k < c.fields.length)
    {mk : MessageKeyGenerator} (hfl : c.fields[k]'hk = .key mk) :
    chainGAfter c (k + 1) = { chainGAfter c k with keys := (chainGAfter c k).keys ++ [mk] } := by
  unfold chainGAfter
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil, hfl]; rfl

theorem drop_fields_flatMap_enc_of_key {c : ChainG} {k : Nat} (hk : k < c.fields.length)
    {mk : MessageKeyGenerator} (hfl : c.fields[k]'hk = .key mk) (tail : List (BitVec 8)) :
    (c.fields.drop k).flatMap ChainField.enc ++ tail =
      lenField 4 (encMessageKey mk) ++ ((c.fields.drop (k + 1)).flatMap ChainField.enc ++ tail) := by
  rw [List.drop_eq_getElem_cons hk, hfl, List.flatMap_cons, ChainField.enc, List.append_assoc]

theorem uint32Field_1_eq_pbVarint (i : BitVec 32) : uint32Field 1 i = pbVarint 1 i.toNat := by
  unfold uint32Field pbVarint pbKey
  by_cases hi : i = 0
  · subst hi; rfl
  · have hne : i.toNat ≠ 0 := by intro h; apply hi; exact BitVec.eq_of_toNat_eq (by simpa using h)
    simp only [hi, hne, ↓reduceIte]
    have hkey : encodeKey 1 .varint = [0x08#8] := rfl
    rw [hkey, pbVarintBody_u32_eq_encodeVarint_seedChain]

theorem bytesField_5_eq_pbBytes {b : List (BitVec 8)} (hb : b.length = 32) :
    bytesField 5 b = pbBytes 5 b := by
  have hne : b ≠ [] := by rintro rfl; simp at hb
  have hlt : b.length < 128 := by omega
  unfold bytesField lenField pbBytes pbKey; simp only [hne, ↓reduceIte]
  have hkey : encodeKey 5 .lengthDelimited = [0x2a#8] := rfl
  rw [hkey, encodeVarint_lt128_seedChain b.length hlt]

theorem encMessageKey_eq_pb {mk : MessageKeyGenerator} (hseed : mk.seed.length = 32) :
    encMessageKey mk = pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed := by
  unfold encMessageKey; rw [uint32Field_1_eq_pbVarint, bytesField_5_eq_pbBytes hseed]

theorem encMessageKey_length_lt128 {mk : MessageKeyGenerator} (hseed : mk.seed.length = 32) :
    (encMessageKey mk).length < 128 := by
  rw [encMessageKey_eq_pb hseed, List.length_append, pbBytes_length_seedChain, hseed]
  have := pbVarint1_length_bounds_seedChain mk.counter.toNat; omega

theorem lenField_4_encMessageKey_eq {mk : MessageKeyGenerator} (hseed : mk.seed.length = 32) :
    lenField 4 (encMessageKey mk) =
      0x22#8 :: BitVec.ofNat 8 (encMessageKey mk).length ::
        (pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed) := by
  have hlt := encMessageKey_length_lt128 hseed; unfold lenField
  have hkey : encodeKey 4 .lengthDelimited = [0x22#8] := rfl
  rw [hkey, encodeVarint_lt128_seedChain _ hlt, encMessageKey_eq_pb hseed]; rfl

/-! ## Stack Frame, `prostMsgKeyAt` Move, and `prostChainGAt` Helpers -/

def chainMergeSavedRegs12 (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

def chainMergePad4 (sp0 : BitVec 64) : SepProp :=
  memRegion (sp0 - 256#64) 8 ∗ memRegion (sp0 - 144#64) 48

theorem chainMergeSavedRegs_eq_split (sp0 : BitVec 64) (s0 : State) :
    chainMergeSavedRegs sp0 s0 =
      memRegion (sp0 - 248#64) 104 ∗ chainMergePad4 sp0 ∗ chainMergeSavedRegs12 sp0 s0 := by
  unfold chainMergeSavedRegs chainMergePad4 chainMergeSavedRegs12
  have s1 := memRegion_split (sp0 - 256#64) 8 152 (by decide)
  have e1 : (sp0 - 256#64) + BitVec.ofNat 64 8 = sp0 - 248#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (8 : Nat) + 152 = 160 by decide, e1] at s1
  have s2 := memRegion_split (sp0 - 248#64) 104 48 (by decide)
  have e2 : (sp0 - 248#64) + BitVec.ofNat 64 104 = sp0 - 144#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (104 : Nat) + 48 = 152 by decide, e2] at s2; rw [s1, s2]; ac_rfl

theorem memRegion104_sp248_split (sp0 : BitVec 64) :
    memRegion (sp0 - 248#64) 104 =
      memRegion (sp0 - 248#64) 80 ∗ (∃∗ c10 : BitVec 64, (sp0 - 168#64) ↦₆₄ c10) ∗
      (∃∗ c11 : BitVec 64, (sp0 - 160#64) ↦₆₄ c11) ∗ (∃∗ wc : BitVec 32, (sp0 - 152#64) ↦₃₂ wc) ∗
      memRegion (sp0 - 148#64) 4 := by
  have s80 := memRegion_split (sp0 - 248#64) 80 24 (by decide)
  have e80 : (sp0 - 248#64) + BitVec.ofNat 64 80 = sp0 - 168#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (80 : Nat) + 24 = 104 by decide, e80] at s80
  have h24 := memRegion24_split_ck_seedChain (sp0 - 248#64)
  have eb0 : (sp0 - 248#64) + 0x50#64 = sp0 - 168#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have eb1 : (sp0 - 248#64) + 0x58#64 = sp0 - 160#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have eb2 : (sp0 - 248#64) + 0x60#64 = sp0 - 152#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have eb3 : (sp0 - 248#64) + 0x64#64 = sp0 - 148#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [eb0, eb1, eb2, eb3] at h24; rw [s80, h24]

theorem memRegion80_sp248_eq_cells10 (sp0 : BitVec 64) :
    memRegion (sp0 - 248#64) 80 =
      ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
      ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64,
        ((sp0 - 248#64) ↦₆₄ c0) ∗ ((sp0 - 240#64) ↦₆₄ c1) ∗ ((sp0 - 232#64) ↦₆₄ c2) ∗
        ((sp0 - 224#64) ↦₆₄ c3) ∗ ((sp0 - 216#64) ↦₆₄ c4) ∗ ((sp0 - 208#64) ↦₆₄ c5) ∗
        ((sp0 - 200#64) ↦₆₄ c6) ∗ ((sp0 - 192#64) ↦₆₄ c7) ∗ ((sp0 - 184#64) ↦₆₄ c8) ∗
        ((sp0 - 176#64) ↦₆₄ c9) := by
  have h80 := memRegion80_chainInit_eq_cells10_receiverChains (sp0 - 16#64)
  have ea0 : sp0 - 16#64 - 232#64 = sp0 - 248#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea1 : sp0 - 16#64 - 224#64 = sp0 - 240#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea2 : sp0 - 16#64 - 216#64 = sp0 - 232#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea3 : sp0 - 16#64 - 208#64 = sp0 - 224#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea4 : sp0 - 16#64 - 200#64 = sp0 - 216#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea5 : sp0 - 16#64 - 192#64 = sp0 - 208#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea6 : sp0 - 16#64 - 184#64 = sp0 - 200#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea7 : sp0 - 16#64 - 176#64 = sp0 - 192#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea8 : sp0 - 16#64 - 168#64 = sp0 - 184#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea9 : sp0 - 16#64 - 160#64 = sp0 - 176#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [ea0, ea1, ea2, ea3, ea4, ea5, ea6, ea7, ea8, ea9] at h80; exact h80

theorem prostMsgKeyAt_fold (sp0 : BitVec 64) (mk : MessageKeyGenerator) :
    vecU8 A0 (sp0 - 248#64) [] ∗ vecU8 A0 (sp0 - 224#64) [] ∗ vecU8 A0 (sp0 - 200#64) [] ∗
      vecU8 A0 (sp0 - 176#64) mk.seed ∗ ((sp0 - 152#64) ↦₃₂ mk.counter) ∗
      memRegion (sp0 - 148#64) 4 = prostMsgKeyAt A0 mk (sp0 - 248#64) := by
  unfold prostMsgKeyAt
  have e1 : (sp0 - 248#64) + 24#64 = sp0 - 224#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2 : (sp0 - 248#64) + 48#64 = sp0 - 200#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3 : (sp0 - 248#64) + 72#64 = sp0 - 176#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e4 : (sp0 - 248#64) + 96#64 = sp0 - 152#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e5 : (sp0 - 248#64) + 100#64 = sp0 - 148#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [e1, e2, e3, e4, e5]

theorem prostMsgKeyAt_move_bytes (A : RustAlloc) (mk : MessageKeyGenerator) (a : BitVec 64) :
    prostMsgKeyAt A mk a ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 104 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ prostMsgKeyAt A mk b⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  have h12 := move_bytes_pair_receiverChains (P1 := fun b => vecU8 A b []) (P2 := fun b => vecU8 A b [])
    (n1 := 24) (n2 := 24) (off := 24#64) rfl (fun b => vecU8_move_bytes_receiverChains A b [])
    (fun b => vecU8_move_bytes_receiverChains A b [])
  have h123 := move_bytes_pair_receiverChains (P1 := fun b => vecU8 A b [] ∗ vecU8 A (b + 24#64) [])
    (P2 := fun b => vecU8 A b []) (n1 := 48) (n2 := 24) (off := 48#64) rfl h12
    (fun b => vecU8_move_bytes_receiverChains A b [])
  have h1234 := move_bytes_pair_receiverChains
    (P1 := fun b => (vecU8 A b [] ∗ vecU8 A (b + 24#64) []) ∗ vecU8 A (b + 48#64) [])
    (P2 := fun b => vecU8 A b mk.seed) (n1 := 72) (n2 := 24) (off := 72#64) rfl h123
    (fun b => vecU8_move_bytes_receiverChains A b mk.seed)
  have h12345 := move_bytes_pair_receiverChains
    (P1 := fun b => ((vecU8 A b [] ∗ vecU8 A (b + 24#64) []) ∗ vecU8 A (b + 48#64) []) ∗ vecU8 A (b + 72#64) mk.seed)
    (P2 := fun b => (b ↦₃₂ mk.counter) ∗ memRegion (b + 4#64) 4) (n1 := 96) (n2 := 8) (off := 96#64) rfl
    h1234 (prostCkTailSome_move_bytes_receiverChains mk.counter) a
  have heq : ∀ b : BitVec 64, prostMsgKeyAt A mk b =
      (((vecU8 A b [] ∗ vecU8 A (b + 24#64) []) ∗ vecU8 A (b + 48#64) []) ∗ vecU8 A (b + 72#64) mk.seed) ∗
      (((b + 96#64) ↦₃₂ mk.counter) ∗ memRegion ((b + 96#64) + 4#64) 4) := fun b => by
    unfold prostMsgKeyAt
    have e100 : (b + 96#64) + 4#64 = b + 100#64 := by rw [BitVec.add_assoc]; rfl
    rw [e100]; ac_rfl
  simp only [show (96 : Nat) + 8 = 104 from rfl, ← heq] at h12345; exact h12345

theorem prostMsgKeyAt_move_chunks104 (A : RustAlloc) (a : BitVec 64) (mk : MessageKeyGenerator) :
    prostMsgKeyAt A mk a ⊢
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128, ∃∗ q3 : BitVec 128,
      ∃∗ q4 : BitVec 128, ∃∗ q5 : BitVec 128, ∃∗ w6 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ b : BitVec 64, (RawByteMove.chunks104_6QWAt b q0 q1 q2 q3 q4 q5 w6 ∗ H) ⊢ prostMsgKeyAt A mk b⌝ ∗
        RawByteMove.chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 ∗ H := by
  refine Entails.trans (prostMsgKeyAt_move_bytes A mk a) ?_
  apply Entails.sepExists_elim; intro bs; apply Entails.sepExists_elim; intro H
  apply Entails.pure_left; rintro ⟨hlen, hmov⟩
  obtain ⟨q0, q1, q2, q3, q4, q5, w6, _, hchunks⟩ := RawByteMove.exists_bytes104Of6QW hlen
  rw [hchunks a]
  refine Entails.sepExists_right q0 (Entails.sepExists_right q1
    (Entails.sepExists_right q2 (Entails.sepExists_right q3
      (Entails.sepExists_right q4 (Entails.sepExists_right q5
        (Entails.sepExists_right w6 (Entails.sepExists_right H ?_)))))))
  refine Entails.pure_right (fun b => ?_) (Entails.refl _); rw [← hchunks b]; exact hmov b

theorem chunks104_6QWAt_sp248_eq (sp0 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    RawByteMove.chunks104_6QWAt (sp0 - 248#64) q0 q1 q2 q3 q4 q5 w6 =
      ((sp0 - 248#64) ↦₆₄ q0.extractLsb' 0 64) ∗ ((sp0 - 240#64) ↦₆₄ q0.extractLsb' 64 64) ∗
      ((sp0 - 232#64) ↦₆₄ q1.extractLsb' 0 64) ∗ ((sp0 - 224#64) ↦₆₄ q1.extractLsb' 64 64) ∗
      ((sp0 - 216#64) ↦₆₄ q2.extractLsb' 0 64) ∗ ((sp0 - 208#64) ↦₆₄ q2.extractLsb' 64 64) ∗
      ((sp0 - 200#64) ↦₆₄ q3.extractLsb' 0 64) ∗ ((sp0 - 192#64) ↦₆₄ q3.extractLsb' 64 64) ∗
      ((sp0 - 184#64) ↦₆₄ q4.extractLsb' 0 64) ∗ ((sp0 - 176#64) ↦₆₄ q4.extractLsb' 64 64) ∗
      ((sp0 - 168#64) ↦₆₄ q5.extractLsb' 0 64) ∗ ((sp0 - 160#64) ↦₆₄ q5.extractLsb' 64 64) ∗
      ((sp0 - 152#64) ↦₆₄ w6) := by
  unfold RawByteMove.chunks104_6QWAt pointsTo128
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, sepConj_assoc]; rfl

theorem arrayAt_prostMsgKeyAt_move_bytes (A : RustAlloc) (keys : List MessageKeyGenerator) :
    ∀ a : BitVec 64,
      arrayAt (fun mk b => prostMsgKeyAt A mk b) 104 a keys ⊢
        ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
          ⌜bs.length = keys.length * 104 ∧
            ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ arrayAt (fun mk d => prostMsgKeyAt A mk d) 104 b keys⌝ ∗
          (a ↦ₛ bs) ∗ H := by
  induction keys with
  | nil =>
    intro a; rw [arrayAt_nil]
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_)
    rw [pointsToBytes_nil, sepConj_emp]
    refine Entails.pure_right ⟨rfl, fun b => ?_⟩ (Entails.refl _)
    rw [pointsToBytes_nil, sepConj_emp, arrayAt_nil]; exact Entails.refl _
  | cons mk ks ih =>
    intro a; rw [arrayAt_cons]
    have hm := move_bytes_pair_receiverChains (P1 := fun b => prostMsgKeyAt A mk b)
      (P2 := fun b => arrayAt (fun m d => prostMsgKeyAt A m d) 104 b ks)
      (n1 := 104) (n2 := ks.length * 104) (off := BitVec.ofNat 64 104) rfl
      (prostMsgKeyAt_move_bytes A mk) ih a
    have hlen : 104 + ks.length * 104 = (mk :: ks).length * 104 := by simp only [List.length_cons]; omega
    rw [hlen] at hm; exact hm

def prostChainGRest (A : RustAlloc) (a : BitVec 64) (c : ChainG) : SepProp :=
  vecU8 A a c.srk ∗ vecU8 A (a + 0x18#64) c.priv ∗
    match c.ck with
    | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
    | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗ memRegion (a + 0x64#64) 4

theorem prostChainGAt_eq_keys_sep_rest (A : RustAlloc) (a : BitVec 64) (c : ChainG) :
    prostChainGAt A a c =
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c.keys ∗ prostChainGRest A a c := by
  unfold prostChainGAt prostChainGRest; ac_rfl

theorem prostChainGRest_update_keys (A : RustAlloc) (a : BitVec 64) (c : ChainG)
    (ks : List MessageKeyGenerator) :
    prostChainGRest A a { c with keys := ks } = prostChainGRest A a c := rfl

theorem vecOf_keys_open (a : BitVec 64) (keys : List MessageKeyGenerator) :
    vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (a + 0x30#64) keys ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜keys.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        arrayAt (fun mk b => prostMsgKeyAt A0 mk b) 104 ptr keys ∗
        (if cap = 0#64 then emp
         else memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) := by
  unfold vecOf vecAt vecHeader
  apply Entails.sepExists_elim; intro cap; apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have e40 : a + 0x30#64 + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
  rw [e38, e40]
  refine Entails.trans (sepConj_mono_right (vecBuf_expose_arrayAt A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) cap ptr keys)) ?_
  have hlive : A0.live ptr (cap.toNat * 104) 8 = emp := rfl
  have hif : (if cap = 0 then emp else A0.live ptr (cap.toNat * 104) 8 ∗
      memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) =
      (if cap = 0#64 then emp else memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) := by
    rw [hlive]
    change (if cap = 0#64 then emp else emp ∗ memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) = _
    by_cases h0 : cap = 0#64 <;> simp [h0]
  rw [hif]
  have hpull : (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length)) ∗
      (⌜keys.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ keys.length * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        arrayAt (fun mk b => prostMsgKeyAt A0 mk b) 104 ptr keys ∗
        (if cap = 0#64 then emp else memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104))) =
      ⌜keys.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ keys.length * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        arrayAt (fun mk b => prostMsgKeyAt A0 mk b) 104 ptr keys ∗
        (if cap = 0#64 then emp else memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104))) := by ac_rfl
  rw [hpull]; apply Entails.pure_left; rintro ⟨hlen, hcap_lt, _, hptr⟩
  exact Entails.pure_right ⟨hlen, hcap_lt, hptr⟩ (Entails.refl _)

theorem vecOf_keys_push_fold (a cap ptr : BitVec 64)
    (keys : List MessageKeyGenerator) (mk : MessageKeyGenerator)
    (hcap_le : keys.length + 1 ≤ cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1)) ∗
      arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr keys ∗
      prostMsgKeyAt A0 mk (ptr + BitVec.ofNat 64 (keys.length * 104)) ∗
      memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap.toNat - (keys.length + 1)) * 104) ⊢
    vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 0x30#64) (keys ++ [mk]) := by
  have hne0 : cap ≠ 0#64 := by intro h0; subst h0; simp at hcap_le
  have hlen : (keys ++ [mk]).length = keys.length + 1 := by simp
  have hlive : A0.live ptr (cap.toNat * 104) 8 = emp := rfl
  unfold vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have e40 : a + 0x30#64 + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
  have hif : (if cap = 0 then emp else A0.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr (keys ++ [mk]) ∗
        memRegion (ptr + BitVec.ofNat 64 ((keys ++ [mk]).length * 104)) ((cap.toNat - (keys ++ [mk]).length) * 104)) =
      (arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr keys ∗
        prostMsgKeyAt A0 mk (ptr + BitVec.ofNat 64 (keys.length * 104))) ∗
      memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap.toNat - (keys.length + 1)) * 104) := by
    rw [hlive, hlen, arrayAt_concat]; change (if cap = 0#64 then emp else _) = _; simp [hne0]
  rw [e38, e40, hif, hlen]
  have hgrp : (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1))) ∗
      (⌜keys.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr keys ∗
            prostMsgKeyAt A0 mk (ptr + BitVec.ofNat 64 (keys.length * 104))) ∗
          memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap.toNat - (keys.length + 1)) * 104))) =
      ⌜keys.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1)) ∗
        arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr keys ∗
        prostMsgKeyAt A0 mk (ptr + BitVec.ofNat 64 (keys.length * 104)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap.toNat - (keys.length + 1)) * 104)) := by ac_rfl
  rw [hgrp]; exact Entails.pure_right ⟨hcap_le, hcap_lt, hptr⟩ (Entails.refl _)

theorem growOneChain_ok_sub_seedChain {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ConsumeMessageKeyTransfer.growOneChainName)
      ((CryptoVerification.LibsignalSession.growOneSpec A0).inImage sessionImg0)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr chainMergeName + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))
      ((CryptoVerification.LibsignalSession.growOneSpec A0).inImage sessionImg0) := by
  have heq : (tripleRatchetProgAt b C ctl abs).fnAddr chainMergeName + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") =
      (tripleRatchetProgAt b C ctl abs).fnAddr ConsumeMessageKeyTransfer.growOneChainName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"), (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")]
    bv_omega
  rw [heq]; exact h

theorem stackAt_sub_to_growOne_seedChain (sp : BitVec 64) :
    stackAt sp chainMergeSubStack =
      memRegion (sp - BitVec.ofNat 64 chainMergeSubStack) (chainMergeSubStack - 4608) ∗ stackAt sp 4608 :=
  stackAt_sub_split_seedChain sp 4608 chainMergeSubStack

theorem memRegion_spare_eq_emp_of_full (cap ptr : BitVec 64) (n : Nat) (hfull : n = cap.toNat) :
    (if cap = 0#64 then emp else memRegion (ptr + BitVec.ofNat 64 (n * 104)) ((cap.toNat - n) * 104)) = emp := by
  rw [hfull, Nat.sub_self, Nat.zero_mul, ProofLib.memRegion_zero]
  by_cases h0 : cap = 0#64 <;> simp [h0]

theorem memRegion_spare_split_of_lt (cap ptr : BitVec 64) (n : Nat)
    (hlt : n + 1 ≤ cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) :
    (if cap = 0#64 then emp else memRegion (ptr + BitVec.ofNat 64 (n * 104)) ((cap.toNat - n) * 104)) =
      memRegion (ptr + BitVec.ofNat 64 (n * 104)) 104 ∗
      memRegion (ptr + BitVec.ofNat 64 ((n + 1) * 104)) ((cap.toNat - (n + 1)) * 104) := by
  have hne0 : cap ≠ 0#64 := by intro h0; subst h0; simp at hlt
  simp only [hne0, ↓reduceIte]
  have hmul : (cap.toNat - n) * 104 = 104 + (cap.toNat - (n + 1)) * 104 := by omega
  have hsplit := memRegion_split (ptr + BitVec.ofNat 64 (n * 104)) 104 ((cap.toNat - (n + 1)) * 104) (by omega)
  have haddr : ptr + BitVec.ofNat 64 (n * 104) + BitVec.ofNat 64 104 = ptr + BitVec.ofNat 64 ((n + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  rw [← hmul, haddr] at hsplit; exact hsplit

theorem growOne_inImage_pre_eq (a cap ptr sp : BitVec 64) (bs : List (BitVec 8)) (s : State)
    (hsp : s.sp = sp) (hbs : bs.length = cap.toNat * 104) :
    ((CryptoVerification.LibsignalSession.growOneSpec A0).inImage sessionImg0).pre (a + 0x30#64, cap, ptr, bs) s =
    ⌜(bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = a + 0x30#64 ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63) ∧ sessionImg0.FrozenLoaded s ∧ s.symtab = sessionImg0.symtab⌝ ∗
    (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ (ptr ↦ₛ bs) ∗ stackAt sp 4608) := by
  unfold Spec.inImage CryptoVerification.LibsignalSession.growOneSpec; dsimp only
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have hpool : A0.pool = emp := rfl
  have hlive : A0.live ptr bs.length 8 = emp := rfl
  have hif : (if cap = 0 then emp else A0.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) = (ptr ↦ₛ bs) := by
    rw [hlive]; change (if cap = 0#64 then emp else emp ∗ (ptr ↦ₛ bs)) = (ptr ↦ₛ bs)
    by_cases h0 : cap = 0#64
    · subst h0; simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul] at hbs
      rw [List.eq_nil_of_length_eq_zero hbs, pointsToBytes_nil]; simp
    · simp [h0]
  rw [e38, hpool, hif, hsp]; simp only [emp_sepConj, ← sepConj_assoc, pure_sepConj_pure]; ac_rfl

theorem growOne_post_elim_sp (a cap ptr sp : BitVec 64) (bs : List (BitVec 8))
    (n : Nat) (s_pre sf : State) (hsp : s_pre.sp = sp) (hfull : n = cap.toNat)
    (hbs : bs.length = n * 104) (hbound : n ≤ maxMessageKeys) :
    ((CryptoVerification.LibsignalSession.growOneSpec A0).inImage sessionImg0).post (a + 0x30#64, cap, ptr, bs) s_pre sf ⊢
      ⌜sf.trace = s_pre.trace⌝ ∗ ∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜n + 1 ≤ cap'.toNat ∧ cap'.toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        ((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ p') ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 (n * 104)) 104 ∗
        memRegion (p' + BitVec.ofNat 64 ((n + 1) * 104)) ((cap'.toNat - (n + 1)) * 104) ∗ stackAt sp 4608 := by
  unfold Spec.inImage CryptoVerification.LibsignalSession.growOneSpec; dsimp only; rw [hsp]
  apply Entails.pure_left; intro htr; refine Entails.pure_right htr ?_
  apply Entails.sepExists_elim; intro p'
  let cap' : BitVec 64 := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  refine Entails.sepExists_right cap' (Entails.sepExists_right p' ?_)
  have hmax_lt : max (2 * cap.toNat) 4 < 2 ^ 64 := by unfold maxMessageKeys at hbound; omega
  have hcap'_toNat : cap'.toNat = max (2 * cap.toNat) 4 := by
    change (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = _; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax_lt]
  have hcap'_le : n + 1 ≤ cap'.toNat := by omega
  have hcap'_lt : cap'.toNat * 104 < 2 ^ 63 := by unfold maxMessageKeys at hbound; omega
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have hlive : A0.live p' (max (2 * cap.toNat) 4 * 104) 8 = emp := rfl
  have hpool : A0.pool = emp := rfl
  have hmul : (max (2 * cap.toNat) 4 - cap.toNat) * 104 = 104 + (cap'.toNat - (n + 1)) * 104 := by omega
  have hsplit := memRegion_split (p' + BitVec.ofNat 64 (n * 104)) 104 ((cap'.toNat - (n + 1)) * 104) (by omega)
  have haddr : p' + BitVec.ofNat 64 (n * 104) + BitVec.ofNat 64 104 = p' + BitVec.ofNat 64 ((n + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  rw [haddr] at hsplit; rw [e38, hlive, hpool, hbs, hmul, hsplit]; simp only [emp_sepConj]
  apply Entails.pure_left; intro hp'; refine Entails.pure_right ⟨hcap'_le, hcap'_lt, hp'⟩ (Entails.of_eq (by dsimp only [cap']; ac_rfl))

/-! ## Sub-Segments 4a–4e and `chainMessageKeysG_ok` -/

theorem mk_hdr_pointsTo_combine_seedChain (ptr : BitVec 64) (n : Nat) :
    (ptr ↦₈ 0x22#8) ∗ ((ptr + 1#64) ↦₈ BitVec.ofNat 8 n) = (ptr ↦ₛ [0x22#8, BitVec.ofNat 8 n]) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem msgKey_default_of_cells (sp0 : BitVec 64) :
    ((sp0 - 248#64) ↦₆₄ 0#64) ∗ ((sp0 - 240#64) ↦₆₄ 1#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64) ∗
      ((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 1#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64) ∗
      ((sp0 - 200#64) ↦₆₄ 0#64) ∗ ((sp0 - 192#64) ↦₆₄ 1#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64) ∗
      ((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 1#64) ∗ ((sp0 - 160#64) ↦₆₄ 0#64) ⊢
    vecU8 A0 (sp0 - 248#64) [] ∗ vecU8 A0 (sp0 - 224#64) [] ∗ vecU8 A0 (sp0 - 200#64) [] ∗ vecU8 A0 (sp0 - 176#64) [] := by
  have v0 := emptyVec_entails_vecU8_seedChain (sp0 - 248#64); have v1 := emptyVec_entails_vecU8_seedChain (sp0 - 224#64)
  have v2 := emptyVec_entails_vecU8_seedChain (sp0 - 200#64); have v3 := emptyVec_entails_vecU8_seedChain (sp0 - 176#64)
  have e0a : (sp0 - 248#64) + 8#64 = sp0 - 240#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e0b : (sp0 - 248#64) + 16#64 = sp0 - 232#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e1a : (sp0 - 224#64) + 8#64 = sp0 - 216#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e1b : (sp0 - 224#64) + 16#64 = sp0 - 208#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2a : (sp0 - 200#64) + 8#64 = sp0 - 192#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2b : (sp0 - 200#64) + 16#64 = sp0 - 184#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3a : (sp0 - 176#64) + 8#64 = sp0 - 168#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3b : (sp0 - 176#64) + 16#64 = sp0 - 160#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [e0a, e0b] at v0; rw [e1a, e1b] at v1; rw [e2a, e2b] at v2; rw [e3a, e3b] at v3
  have hgrp :
      ((sp0 - 248#64) ↦₆₄ 0#64) ∗ ((sp0 - 240#64) ↦₆₄ 1#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64) ∗
        ((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 1#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64) ∗
        ((sp0 - 200#64) ↦₆₄ 0#64) ∗ ((sp0 - 192#64) ↦₆₄ 1#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64) ∗
        ((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 1#64) ∗ ((sp0 - 160#64) ↦₆₄ 0#64) =
      (((sp0 - 248#64) ↦₆₄ 0#64) ∗ ((sp0 - 240#64) ↦₆₄ 1#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64)) ∗
      ((((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 1#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64)) ∗
      ((((sp0 - 200#64) ↦₆₄ 0#64) ∗ ((sp0 - 192#64) ↦₆₄ 1#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64)) ∗
       (((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 1#64) ∗ ((sp0 - 160#64) ↦₆₄ 0#64)))) := by ac_rfl
  rw [hgrp]; exact sepConj_mono v0 (sepConj_mono v1 (sepConj_mono v2 v3))

theorem spAligned_of_sp_eq {s1 s2 : State} (h : s1.sp = s2.sp) (ha : s2.spAligned = true) :
    s1.spAligned = true := by unfold State.spAligned at ha ⊢; rwa [h]

theorem ult_ofNat_add_right_false_seedChain {m k : Nat} (h : m + k < 2 ^ 64) :
    (BitVec.ofNat 64 (m + k)).ult (BitVec.ofNat 64 m) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 64), decide_eq_false_iff_not]; omega

theorem step_tag4a (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64) (mk_body rest tail : List (BitVec 8))
    (hmk_lt : mk_body.length < 128) (htail_le : tail.length ≤ rest.length)
    (hlen_lt : (2 + (mk_body.length + rest.length)) < 2 ^ 32)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (hsp_align : s0.spAligned = true)
    (hF : sessionImg0.FrozenLoaded s0) (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hx25 : s0.readReg64 .x25 = sp0 - 248#64) (hx26 : s0.readReg64 .x26 = 1#64)
    (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x300#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.spAligned = true →
      sessionImg0.FrozenLoaded sm → sm.symtab = sessionImg0.symtab → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a → sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 → sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      sm.readReg64 .x28 = BitVec.ofNat 64 rest.length → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A0 (sp0 - 248#64) [] ∗ vecU8 A0 (sp0 - 224#64) [] ∗
          vecU8 A0 (sp0 - 200#64) [] ∗ vecU8 A0 (sp0 - 176#64) [] ∗
          ((sp0 - 152#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 148#64) 4 ∗
          (ptr ↦ₛ [0x22#8, BitVec.ofNat 8 mk_body.length]) ∗
          Prost.sliceCursorAt slot (ptr + 2#64) (mk_body ++ rest) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗ memRegion (sp0 - 248#64) 104 ∗
        Prost.sliceCursorAt slot ptr (0x22#8 :: BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F) Q Qp := by
  have hsp_align_bv : s0.sp &&& 15#64 = 0#64 := eq_of_beq hsp_align
  have hlen_gt : tail.length < (0x22#8 :: BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)).length := by
    simp only [List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x22#8 :: BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)).length < 2 ^ 32 := by
    simp only [List.length_cons, List.length_append]; omega
  have hule_ls := ule_ofNat_of_gt_false_seedChain hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x22#8 (BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest))
  have hrem1_lt : (BitVec.ofNat 8 mk_body.length :: (mk_body ++ rest)).length < 2 ^ 32 := by
    simp only [List.length_cons, List.length_append]; omega
  have hcbz2 := cbz_len_cons_false_seedChain (b0 := BitVec.ofNat 8 mk_body.length) (bs1 := mk_body ++ rest) hrem1_lt
  have hse0 := signExtend64_ofNat8_lt128_seedChain hmk_lt
  have hlsr56 := ofNat64_lsr56_eq_zero_seedChain hmk_lt
  have hsub2 := len_cons_sub_one_seedChain (BitVec.ofNat 8 mk_body.length) (mk_body ++ rest)
  have hlen_mk_append : (mk_body ++ rest).length = mk_body.length + rest.length := List.length_append
  have hult_mk_sub := ult_ofNat_add_right_false_seedChain (m := mk_body.length) (k := rest.length) (by omega)
  have hsub_mk_rest := bv_ofNat_add_sub_left_seedChain mk_body.length rest.length
  chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x120 0x144
  chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x188 0x1ac
  chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x1d8 0x230
  chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x2ec 0x2fc
  dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19; have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21; have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
  have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25; have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (768)) hF hsym ?_
  rw [memRegion104_sp248_split sp0, memRegion80_sp248_eq_cells10 sp0]
  unfold Prost.sliceCursorAt; rw [pointsToBytes_cons, pointsToBytes_cons]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro c0; apply SepWP.exists_elim; intro c1
  apply SepWP.exists_elim; intro c2; apply SepWP.exists_elim; intro c3
  apply SepWP.exists_elim; intro c4; apply SepWP.exists_elim; intro c5
  apply SepWP.exists_elim; intro c6; apply SepWP.exists_elim; intro c7
  apply SepWP.exists_elim; intro c8; apply SepWP.exists_elim; intro c9
  apply SepWP.exists_elim; intro c10; apply SepWP.exists_elim; intro c11
  apply SepWP.exists_elim; intro wc
  iterate 48 wp_step
  apply SepWP.fold (msgKey_default_of_cells sp0) (by sep_focus)
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hF1 hsym1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [hsp, arm64_norm]) (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align)
    hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm]) (by simp only [h19, arm64_norm])
    (by simp only [h20, arm64_norm]) (by simp only [h21, arm64_norm]) (by simp only [h22, arm64_norm])
    (by simp only [h24, arm64_norm]) (by simp only [h25, arm64_norm]) (by simp only [h26, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [h29, arm64_norm]))
  unfold Prost.sliceCursorAt
  rw [← hlen_mk_append, ← mk_hdr_pointsTo_combine_seedChain ptr mk_body.length]
  exact sep_ac_seedChain (by ac_rfl)

theorem sp0_aligned_of_sp_sub_256 {s : State} {sp0 : BitVec 64}
    (hsp : s.sp = sp0 - 256#64) (hal : s.spAligned = true) :
    sp0 &&& 15#64 = 0#64 := by
  have h : (sp0 - 256#64) &&& 15#64 = 0#64 := by rw [← hsp]; exact eq_of_beq hal
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq; rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp0.isLt; omega

def dummyChainMergeGhost : ChainMergeGhost :=
  ⟨0#64, ⟨[], [], none⟩, 0#64, 0#64, 0#64, [], []⟩

theorem step_tag4b (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hIM : Prost.Int32MergeOk sessionImg0.base C A0 ctl abs)
    (a bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32) (rest_mk rest tail : List (BitVec 8))
    (hlen_lt : (pbVarint 1 i.toNat ++ rest_mk ++ rest).length < 2 ^ 32)
    {x : ChainMergeGenGhost} {R : SepProp} {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x300#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (halign : sp0 &&& 15#64 = 0#64)
    (hF : sessionImg0.FrozenLoaded s0) (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hx25 : s0.readReg64 .x25 = sp0 - 248#64) (hx26 : s0.readReg64 .x26 = 1#64)
    (hx28 : s0.readReg64 .x28 = BitVec.ofNat 64 rest.length) (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x300#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sessionImg0.FrozenLoaded sm →
      sm.symtab = sessionImg0.symtab → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a → sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 → sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      sm.readReg64 .x28 = BitVec.ofNat 64 rest.length → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗ ((sp0 - 152#64) ↦₃₂ i) ∗ (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest_mk ++ rest) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenSpec.onPanic x s_init sf ∗ R))) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗ ((sp0 - 152#64) ↦₃₂ 0#32) ∗
        Prost.sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest_mk ++ rest)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenSpec.onPanic x s_init sf ∗ R)) := by
  by_cases hi0 : i = 0#32
  · subst hi0; have hpb0 : pbVarint 1 (0#32).toNat = [] := rfl
    rw [hpb0] at hnext ⊢
    simp only [List.nil_append, List.length_nil, BitVec.add_zero, pointsToBytes_nil] at hnext ⊢
    refine SepWPp.mono_pre_seedChain (sep_ac_seedChain (by ac_rfl))
      (hnext s0 hpc hrun hsp hF hsym htr hvregs hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx28 hx29)
  · have hi_pos : i.toNat ≠ 0 := by intro h; apply hi0; apply BitVec.eq_of_toNat_eq; simpa using h
    have hpb : pbVarint 1 i.toNat = 0x08#8 :: pbVarintBody 5 i.toNat := by unfold pbVarint; simp [hi_pos]; rfl
    let rem1 : List (BitVec 8) := pbVarintBody 5 i.toNat ++ (rest_mk ++ rest)
    have hcons_eq : pbVarint 1 i.toNat ++ (rest_mk ++ rest) = 0x08#8 :: rem1 := by rw [hpb]; simp [rem1, List.cons_append]
    have hlen_gt : rest.length < (0x08#8 :: rem1).length := by simp only [rem1, List.length_cons, List.length_append]; omega
    have hlen_cons_lt : (0x08#8 :: rem1).length < 2 ^ 32 := by rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
    have hule_ls := ule_ofNat_of_gt_false_seedChain hlen_gt hlen_cons_lt
    have hult_ls := ult_ofNat_of_gt_true_seedChain hlen_gt hlen_cons_lt
    have hsub1 := len_cons_sub_one_seedChain 0x08#8 rem1
    refine (?_ :
      (∀ (s1 : State),
        s1.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) →
        s1.status = .Running → s1.sp = sp0 - 256#64 → sessionImg0.FrozenLoaded s1 →
        s1.symtab = sessionImg0.symtab → s1.trace = s_init.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s_init →
        s1.readReg64 .lr = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x424#64 →
        (s1.readReg64 .x0).setWidth 8 = 0#8 → s1.readReg64 .x1 = sp0 - 152#64 →
        s1.readReg64 .x2 = bufRef → s1.readReg64 .x19 = bufRef → s1.readReg64 .x20 = a →
        s1.readReg64 .x21 = 98#64 → s1.readReg64 .x22 = 97#64 →
        s1.readReg64 .x24 = BitVec.ofNat 64 tail.length → s1.readReg64 .x25 = sp0 - 248#64 →
        s1.readReg64 .x26 = 1#64 → s1.readReg64 .x28 = BitVec.ofNat 64 rest.length →
        s1.readReg64 .x29 = sp0 - 0x60#64 →
        SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s1
          ((((sp0 - 152#64) ↦₃₂ 0#32) ∗ (bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot (ptr + 1#64) rem1 ∗
            stackAt (sp0 - 256#64) chainMergeSubStack) ∗ ((ptr ↦₈ 0x08#8) ∗ F))
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenSpec.onPanic x s_init sf ∗ R))) → _) ?_
    · intro hnext1
      chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x300 0x324
      chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x368 0x38c
      chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x3c0 0x3c4
      chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x418 0x420
      dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext1 ⊢
      generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
      examples_hide_fetches
      have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19; have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
      have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21; have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
      have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
      have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25; have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
      have h28 : s0.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hx28
      have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
      refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))) hF hsym ?_
      rw [hcons_eq]; unfold Prost.sliceCursorAt; rw [pointsToBytes_cons]; simp only [sepConj_assoc]
      iterate 25 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hF1 hsym1
      refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        (by simp only [hsp, arm64_norm]) hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [h19, arm64_norm]) (by simp only [h20, arm64_norm])
        (by simp only [h21, arm64_norm]) (by simp only [h22, arm64_norm]) (by simp only [h24, arm64_norm])
        (by simp only [h25, arm64_norm]) (by simp only [h26, arm64_norm]) (by simp only [h28, arm64_norm])
        (by simp only [h29, arm64_norm]))
      unfold Prost.sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)
    · intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1
      have hrem1_lt : (pbVarintBody 5 i.toNat ++ (rest_mk ++ rest)).length < 2 ^ 32 := by
        simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
      refine step_chainMerge_int32Merge_seedChain C ctl hIM (sp0 - 152#64) bufRef slot (ptr + 1#64) sp0
        ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x424#64)
        0#32 i (rest_mk ++ rest) hrem1_lt (x := dummyChainMergeGhost) (R := R)
        hpc1 hrun1 hsp1 halign hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
      intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2
      chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x424 0x42c
      dsimp only [tripleRatchetProgAt, chainMergeName] at hpc2 hnext ⊢
      generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
      examples_hide_fetches
      have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (768)) hF2 hsym2 ?_
      iterate 3 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_; intro hF3 hsym3
      have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hcs2.1.trans hx19_1
      have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hcs2.2.1.trans hx20_1
      have h21_2 : s2.readReg64 (Reg.gpr 21#5) = 98#64 := hcs2.2.2.1.trans hx21_1
      have h22_2 : s2.readReg64 (Reg.gpr 22#5) = 97#64 := hcs2.2.2.2.1.trans hx22_1
      have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.2.1.trans hx24_1
      have h25_2 : s2.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hcs2.2.2.2.2.2.2.1.trans hx25_1
      have h26_2 : s2.readReg64 (Reg.gpr 26#5) = 1#64 := hcs2.2.2.2.2.2.2.2.1.trans hx26_1
      have h28_2 : s2.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28_1
      have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
      have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
      refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        (by simp only [hsp2, arm64_norm]) hF3 hsym3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs_2, arm64_norm])
        (by simp only [h19_2, arm64_norm]) (by simp only [h20_2, arm64_norm])
        (by simp only [h21_2, arm64_norm]) (by simp only [h22_2, arm64_norm])
        (by simp only [h24_2, arm64_norm]) (by simp only [h25_2, arm64_norm])
        (by simp only [h26_2, arm64_norm]) (by simp only [h28_2, arm64_norm])
        (by simp only [h29_2, arm64_norm]))
      rw [pbVarint1_ptr_advance_seedChain ptr i.toNat hi_pos, ← pbVarint1_pointsTo_combine_seedChain ptr i.toNat hi_pos]
      exact sep_ac_seedChain (by ac_rfl)

theorem step_tag4c (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hBM : Prost.BytesMergeOk sessionImg0 C A0 ctl abs)
    (a bufRef slot ptr sp0 : BitVec 64) (k rest tail : List (BitVec 8))
    (hk_lt : k.length < 128) (hlen_lt : (pbBytes 5 k ++ rest).length < 2 ^ 32)
    {x : ChainMergeGenGhost} {R : SepProp} {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x300#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (halign : sp0 &&& 15#64 = 0#64)
    (hF : sessionImg0.FrozenLoaded s0) (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hx25 : s0.readReg64 .x25 = sp0 - 248#64) (hx26 : s0.readReg64 .x26 = 1#64)
    (hx28 : s0.readReg64 .x28 = BitVec.ofNat 64 rest.length) (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x300#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sessionImg0.FrozenLoaded sm →
      sm.symtab = sessionImg0.symtab → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a → sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 → sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      sm.readReg64 .x28 = BitVec.ofNat 64 rest.length → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A0 (sp0 - 176#64) k ∗ (ptr ↦ₛ pbBytes 5 k) ∗
          Prost.sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 5 k).length) rest ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenSpec.onPanic x s_init sf ∗ R))) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗ vecU8 A0 (sp0 - 176#64) [] ∗
        Prost.sliceCursorAt slot ptr (pbBytes 5 k ++ rest) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenSpec.onPanic x s_init sf ∗ R)) := by
  have hpb : pbBytes 5 k = 0x2a#8 :: BitVec.ofNat 8 k.length :: k := pbBytes_lt128_eq_seedChain 5 (by decide) k hk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 k.length] ++ k ++ rest
  have hcons_eq : pbBytes 5 k ++ rest = 0x2a#8 :: rem1 := by rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : rest.length < (0x2a#8 :: rem1).length := by simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x2a#8 :: rem1).length < 2 ^ 32 := by rw [← hcons_eq]; exact hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x2a#8 rem1
  refine (?_ :
    (∀ (s1 : State),
      s1.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) →
      s1.status = .Running → s1.sp = sp0 - 256#64 → sessionImg0.FrozenLoaded s1 →
      s1.symtab = sessionImg0.symtab → s1.trace = s_init.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      s1.readReg64 .lr = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x3b4#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 → s1.readReg64 .x1 = sp0 - 176#64 →
      s1.readReg64 .x2 = bufRef → s1.readReg64 .x19 = bufRef → s1.readReg64 .x20 = a →
      s1.readReg64 .x21 = 98#64 → s1.readReg64 .x22 = 97#64 →
      s1.readReg64 .x24 = BitVec.ofNat 64 tail.length → s1.readReg64 .x25 = sp0 - 248#64 →
      s1.readReg64 .x26 = 1#64 → s1.readReg64 .x28 = BitVec.ofNat 64 rest.length →
      s1.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s1
        ((vecU8 A0 (sp0 - 176#64) [] ∗ (bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot (ptr + 1#64) rem1 ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ ((ptr ↦₈ 0x2a#8) ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenSpec.onPanic x s_init sf ∗ R))) → _) ?_
  · intro hnext1
    chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x300 0x324
    chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x368 0x3b0
    dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext1 ⊢
    generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
    examples_hide_fetches
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19; have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
    have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21; have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
    have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
    have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25; have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
    have h28 : s0.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hx28
    have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))) hF hsym ?_
    rw [hcons_eq]; unfold Prost.sliceCursorAt; rw [pointsToBytes_cons]; simp only [sepConj_assoc]
    iterate 29 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hF1 hsym1
    refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [h19, arm64_norm]) (by simp only [h20, arm64_norm])
      (by simp only [h21, arm64_norm]) (by simp only [h22, arm64_norm]) (by simp only [h24, arm64_norm])
      (by simp only [h25, arm64_norm]) (by simp only [h26, arm64_norm]) (by simp only [h28, arm64_norm])
      (by simp only [h29, arm64_norm]))
    unfold Prost.sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1
    have hrem1_lt : ([BitVec.ofNat 8 k.length] ++ k ++ rest).length < 2 ^ 32 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMerge_seedChain C ctl hBM (sp0 - 176#64) bufRef slot (ptr + 1#64) sp0
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x3b4#64)
      [] k rest hk_lt hrem1_lt (x := dummyChainMergeGhost) (R := R)
      hpc1 hrun1 hsp1 halign hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2
    chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x3b4 0x3bc
    dsimp only [tripleRatchetProgAt, chainMergeName] at hpc2 hnext ⊢
    generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
    examples_hide_fetches
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (768)) hF2 hsym2 ?_
    iterate 3 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_; intro hF3 hsym3
    have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hcs2.1.trans hx19_1
    have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hcs2.2.1.trans hx20_1
    have h21_2 : s2.readReg64 (Reg.gpr 21#5) = 98#64 := hcs2.2.2.1.trans hx21_1
    have h22_2 : s2.readReg64 (Reg.gpr 22#5) = 97#64 := hcs2.2.2.2.1.trans hx22_1
    have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.2.1.trans hx24_1
    have h25_2 : s2.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hcs2.2.2.2.2.2.2.1.trans hx25_1
    have h26_2 : s2.readReg64 (Reg.gpr 26#5) = 1#64 := hcs2.2.2.2.2.2.2.2.1.trans hx26_1
    have h28_2 : s2.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28_1
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
    have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      (by simp only [hsp2, arm64_norm]) hF3 hsym3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs_2, arm64_norm])
      (by simp only [h19_2, arm64_norm]) (by simp only [h20_2, arm64_norm])
      (by simp only [h21_2, arm64_norm]) (by simp only [h22_2, arm64_norm])
      (by simp only [h24_2, arm64_norm]) (by simp only [h25_2, arm64_norm])
      (by simp only [h26_2, arm64_norm]) (by simp only [h28_2, arm64_norm])
      (by simp only [h29_2, arm64_norm]))
    rw [pbBytes_ptr_advance_seedChain 5 (by decide) ptr k hk_lt, ← pbBytes_pointsTo_combine_seedChain 5 (by decide) ptr k hk_lt]
    exact sep_ac_seedChain (by ac_rfl)

theorem beq_ofNat_cap_false {n : Nat} {cap : BitVec 64}
    (hle : n ≤ cap.toNat) (hne : n ≠ cap.toNat) : (BitVec.ofNat 64 n == cap) = false := by
  cases hb : (BitVec.ofNat 64 n == cap)
  · rfl
  · have heq := congrArg BitVec.toNat (eq_of_beq hb)
    have hlt : n < 2 ^ 64 := lt_of_le_of_lt hle cap.isLt
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at heq; exact False.elim (hne heq)

theorem step_tag4d (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hG : subroutine_ok (tripleRatchetProgAt sessionImg0.base C ctl abs)
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr ConsumeMessageKeyTransfer.growOneChainName)
      ((CryptoVerification.LibsignalSession.growOneSpec A0).inImage sessionImg0))
    (a bufRef slot ptr_rest sp0 : BitVec 64) (keys : List MessageKeyGenerator) (rest : List (BitVec 8))
    (hbound : keys.length ≤ maxMessageKeys)
    {x : ChainMergeGenGhost} {R : SepProp} {ret val24 : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x300#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (hsp_align : s0.spAligned = true)
    (hF : sessionImg0.FrozenLoaded s0) (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init) (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx24 : s0.readReg64 .x24 = val24)
    (hx25 : s0.readReg64 .x25 = sp0 - 248#64) (hx26 : s0.readReg64 .x26 = 1#64)
    (hx28 : s0.readReg64 .x28 = BitVec.ofNat 64 rest.length) (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      keys.length + 1 ≤ cap'.toNat → cap'.toNat * 104 < 2 ^ 63 → ptr' ≠ 0#64 →
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x5c8#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.spAligned = true →
      sessionImg0.FrozenLoaded sm → sm.symtab = sessionImg0.symtab → sm.trace = s_init.trace → calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a → sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 → sm.readReg64 .x23 = BitVec.ofNat 64 keys.length →
      sm.readReg64 .x24 = val24 → sm.readReg64 .x25 = sp0 - 248#64 →
      sm.readReg64 .x26 = 1#64 → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
          ((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
          ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
          arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr' keys ∗
          memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
          memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap'.toNat - (keys.length + 1)) * 104) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenSpec.onPanic x s_init sf ∗ R))) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗ Prost.sliceCursorAt slot ptr_rest rest ∗
        vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 0x30#64) keys ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenSpec.onPanic x s_init sf ∗ R)) := by
  have hG' := growOneChain_ok_sub_seedChain hG; clear hG
  have hule_r : BitVec.ule (BitVec.ofNat 64 rest.length) (BitVec.ofNat 64 rest.length) = true := by simp [BitVec.ule]
  have hbne_r : (BitVec.ofNat 64 rest.length != BitVec.ofNat 64 rest.length) = false := bne_self_eq_false _
  chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x300 0x30c
  chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x5b4 0x5c4
  chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x61c 0x624
  dsimp only [tripleRatchetProgAt, chainMergeName] at hG' hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19; have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21; have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h24 : s0.readReg64 (Reg.gpr 24#5) = val24 := hx24
  have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25; have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  have h28 : s0.readReg64 (Reg.gpr 28#5) = BitVec.ofNat 64 rest.length := hx28
  have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
  apply SepWPp.fold (vecOf_keys_open a keys) (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap; apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_left; rintro ⟨hcap_le, hcap_lt, hptr⟩
  by_cases hfull : keys.length = cap.toNat
  · have hbeq_cap : (BitVec.ofNat 64 keys.length == cap) = true := by rw [hfull]; simp
    rw [memRegion_spare_eq_emp_of_full cap ptr keys.length hfull, stackAt_sub_to_growOne_seedChain (sp0 - 256#64)]
    simp only [emp_sepConj]
    apply SepWPp.fold (arrayAt_prostMsgKeyAt_move_bytes A0 keys ptr) (by sep_focus)
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro bs; apply SepWPp.exists_elim; intro H
    apply SepWPp.pure_left; rintro ⟨hbs_len, hmov⟩
    have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs_len, hfull]
    have hmax_le : 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 := by unfold maxMessageKeys at hbound; omega
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) hF hsym ?_
    unfold Prost.sliceCursorAt; iterate 11 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hF1 hsym1
    refine call_frame_inImage_receiverChains (x := (a + 0x30#64, cap, ptr, bs))
      (ret_pc := entry + bv% (1572)) hF1 hsym1 hG'
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align) (by simp only [arm64_norm])
      (growOne_inImage_pre_eq a cap ptr (sp0 - 256#64) bs _ (by simp only [hsp, arm64_norm]) hbs_cap)
      ⟨⟨hbs_cap, by simp only [arm64_norm], hptr, hmax_le⟩, hF1, hsym1⟩ (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans_receiverChains (by simp only [htr, arm64_norm])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hFm hsymm
    have ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, _, h28_2, h29_2, hvregs_2⟩ := hcsm
    simp only [h19, h20, h21, h22, h24, h25, h26, h28, h29, hsp, hvregs, arm64_norm] at h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h28_2 h29_2 hvregs_2 hspm
    have hsp_align_m : sm.spAligned = true := spAligned_of_sp_eq (hspm.trans hsp.symm) hsp_align
    refine SepWPp.fold (growOne_post_elim_sp a cap ptr (sp0 - 256#64) bs keys.length _ sm
      (by simp only [hsp, arm64_norm]) hfull hbs_len hbound) rfl ?_
    simp only [sepConj_assoc]; apply SepWPp.pure_left; intro htr_m
    have htr_m' : sm.trace = s_init.trace := by simpa only [htr, arm64_norm] using htr_m
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro cap'; apply SepWPp.exists_elim; intro ptr'
    apply SepWPp.pure_left; rintro ⟨hcap'_le, hcap'_lt, hptr'⟩
    apply SepWPp.fold (hmov ptr') (by sep_focus)
    apply SepWPp.fold (Entails.of_eq (stackAt_sub_to_growOne_seedChain (sp0 - 256#64)).symm) (by sep_focus)
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (1480)) hFm hsymm ?_
    wp_step; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrunm, arm64_norm]) ?_; intro hF2 hsym2
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ cap' ptr' hcap'_le hcap'_lt hptr'
      (by simp only [arm64_norm]) (by simp only [hrunm, arm64_norm])
      (by simp only [hspm, arm64_norm]) (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align_m)
      hF2 hsym2 (by simp only [htr_m', arm64_norm]) (by simp only [hvregs_2, arm64_norm]) (by simp only [h19_2, arm64_norm])
      (by simp only [h20_2, arm64_norm]) (by simp only [h21_2, arm64_norm])
      (by simp only [h22_2, arm64_norm]) (by simp only [h23_2, hfull, BitVec.ofNat_toNat, arm64_norm])
      (by simp only [h24_2, arm64_norm]) (by simp only [h25_2, arm64_norm])
      (by simp only [h26_2, arm64_norm]) (by simp only [h29_2, arm64_norm]))
    unfold Prost.sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)
  · have hcap_le' : keys.length + 1 ≤ cap.toNat := by omega
    have hbeq_cap : (BitVec.ofNat 64 keys.length == cap) = false := beq_ofNat_cap_false hcap_le hfull
    rw [memRegion_spare_split_of_lt cap ptr keys.length hcap_le' hcap_lt]
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (1480)) hF hsym ?_
    unfold Prost.sliceCursorAt; iterate 9 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hF1 hsym1
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ cap ptr hcap_le' hcap_lt hptr
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align)
      hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm]) (by simp only [h19, arm64_norm])
      (by simp only [h20, arm64_norm]) (by simp only [h21, arm64_norm])
      (by simp only [h22, arm64_norm]) (by simp only [arm64_norm])
      (by simp only [h24, arm64_norm]) (by simp only [h25, arm64_norm])
      (by simp only [h26, arm64_norm]) (by simp only [h29, arm64_norm]))
    unfold Prost.sliceCursorAt; exact sep_ac_seedChain (by ac_rfl)

theorem ptr_madd_104_eq (ptr : BitVec 64) (n : Nat) :
    ptr + BitVec.ofNat 64 n * 104#64 = ptr + BitVec.ofNat 64 (n * 104) := by rw [← BitVec.ofNat_mul]

theorem ofNat_add_one_eq (n : Nat) :
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by rw [← BitVec.ofNat_add]

theorem step_tag4e (C : Crypto) (ctl : BitVec 64) {abs : String → Option (State → State)}
    (a cap' ptr' sp0 : BitVec 64) (keys : List MessageKeyGenerator) (mk : MessageKeyGenerator)
    (hcap_le : keys.length + 1 ≤ cap'.toNat) (hcap_lt : cap'.toNat * 104 < 2 ^ 63) (hptr : ptr' ≠ 0#64)
    {ret val19 val24 : BitVec 64} {s_init s0 : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x5c8#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp0 - 256#64) (hsp_align : s0.spAligned = true)
    (hF : sessionImg0.FrozenLoaded s0) (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init) (hx19 : s0.readReg64 .x19 = val19)
    (hx20 : s0.readReg64 .x20 = a) (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64) (hx23 : s0.readReg64 .x23 = BitVec.ofNat 64 keys.length)
    (hx24 : s0.readReg64 .x24 = val24) (hx25 : s0.readReg64 .x25 = sp0 - 248#64)
    (hx26 : s0.readReg64 .x26 = 1#64) (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.spAligned = true →
      sessionImg0.FrozenLoaded sm → sm.symtab = sessionImg0.symtab → sm.trace = s_init.trace → calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = val19 → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 98#64 → sm.readReg64 .x22 = 97#64 →
      sm.readReg64 .x24 = val24 → sm.readReg64 .x25 = sp0 - 248#64 →
      sm.readReg64 .x26 = 1#64 → sm.readReg64 .x29 = sp0 - 0x60#64 →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        ((vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 0x30#64) (keys ++ [mk]) ∗
          memRegion (sp0 - 248#64) 104) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      ((((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr' keys ∗
        memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
        memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap'.toNat - (keys.length + 1)) * 104) ∗
        prostMsgKeyAt A0 mk (sp0 - 248#64)) ∗ F) Q Qp := by
  have hsp_align_bv : s0.sp &&& 15#64 = 0#64 := eq_of_beq hsp_align
  have hmadd := ptr_madd_104_eq ptr' keys.length; have hadd1 := ofNat_add_one_eq keys.length
  chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x5c8 0x618
  chainMerge_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x260 0x260
  dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h19 : s0.readReg64 (Reg.gpr 19#5) = val19 := hx19
  have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20; have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 keys.length := hx23
  have h24 : s0.readReg64 (Reg.gpr 24#5) = val24 := hx24
  have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 248#64 := hx25; have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (288)) hF hsym ?_
  apply SepWP.fold (prostMsgKeyAt_move_chunks104 A0 (sp0 - 248#64) mk) (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro q0; apply SepWP.exists_elim; intro q1
  apply SepWP.exists_elim; intro q2; apply SepWP.exists_elim; intro q3
  apply SepWP.exists_elim; intro q4; apply SepWP.exists_elim; intro q5
  apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro H
  apply SepWP.pure_elim; intro hmov
  apply SepWP.fold (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_receiverChains (ptr' + BitVec.ofNat 64 (keys.length * 104)))) (by sep_focus)
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro dw6
  conv => arg 4; rw [chunks104_6QWAt_sp248_eq sp0 q0 q1 q2 q3 q4 q5 w6,
    chunks104_6QWAt_dst_eq_receiverChains (ptr' + BitVec.ofNat 64 (keys.length * 104)) d0 d1 d2 d3 d4 d5 dw6]
  iterate 22 wp_step
  conv => arg 4; rw [← chunks104_6QWAt_dst_eq_receiverChains (ptr' + BitVec.ofNat 64 (keys.length * 104)) q0 q1 q2 q3 q4 q5 w6,
    ← chunks104_6QWAt_sp248_eq sp0 q0 q1 q2 q3 q4 q5 w6]
  apply SepWP.fold (hmov (ptr' + BitVec.ofNat 64 (keys.length * 104))) (by sep_focus)
  apply SepWP.fold (chunks104_6QWAt_entails_memRegion104_receiverChains (sp0 - 248#64) q0 q1 q2 q3 q4 q5 w6) (by sep_focus)
  apply SepWP.fold (vecOf_keys_push_fold a cap' ptr' keys mk hcap_le hcap_lt hptr) (by sep_focus)
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_; intro hF1 hsym1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [hsp, arm64_norm]) (spAligned_of_sp_eq (by simp only [arm64_norm]) hsp_align)
    hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm]) (by simp only [h19, arm64_norm])
    (by simp only [h20, arm64_norm]) (by simp only [h21, arm64_norm]) (by simp only [h22, arm64_norm])
    (by simp only [h24, arm64_norm]) (by simp only [h25, arm64_norm]) (by simp only [h26, arm64_norm])
    (by simp only [h29, arm64_norm]))
  exact sep_ac_seedChain (by ac_rfl)

theorem SepWPp.focus_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s (P' ∗ F) Q Qp) (hf : P = P' ∗ F := by sep_focus) :
    SepWPp prog ret s P Q Qp :=
  hf ▸ h

theorem segStepG_of_sepWPp {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R P : SepProp} {s0 s : State} {ret : BitVec 64} {Q : State → Prop} (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp prog ret s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Q sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    SegStepG prog spec x R s0 s Q := by
  intro hL; obtain ⟨sf, hsteps, ⟨-, -, Pf, hmf, hq⟩ | ⟨hpan, Pf, hmf, hp⟩ | ⟨_, hoom⟩⟩ := hwp R hm hL
  · exact ⟨sf, hsteps, Or.inl (hq hmf)⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hpan, hp hmf⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem chainG_enc_eq_fields_local (c : ChainG) : c.enc = c.fields.flatMap ChainField.enc := by
  have h1 : (if c.srk = [] then [] else [ChainField.srk c.srk]).flatMap ChainField.enc = bytesField 1 c.srk := by
    by_cases h : c.srk = [] <;> simp [h, bytesField, ChainField.enc]
  have h2 : (if c.priv = [] then [] else [ChainField.priv c.priv]).flatMap ChainField.enc = bytesField 2 c.priv := by
    by_cases h : c.priv = [] <;> simp [h, bytesField, ChainField.enc]
  have h4 : ∀ ks : List MessageKeyGenerator,
      (ks.map ChainField.key).flatMap ChainField.enc = (ks.map fun m => lenField 4 (encMessageKey m)).flatten := by
    intro ks; induction ks with | nil => rfl | cons m ks ih => simp [ChainField.enc, ih]
  rcases hck : c.ck with _ | ⟨i, k⟩ <;>
    simp [ChainG.enc, ChainG.fields, h1, h2, h4, hck, ChainField.enc, msgField]

theorem chainG_payload_split (c : ChainG) (k : Nat) (tail : List (BitVec 8)) :
    c.payload ++ tail =
      (encodeVarint (BitVec.ofNat 64 c.enc.length) ++ (c.fields.take k).flatMap ChainField.enc) ++
        ((c.fields.drop k).flatMap ChainField.enc ++ tail) := by
  unfold ChainG.payload
  conv => lhs; arg 1; arg 2; rw [chainG_enc_eq_fields_local c, ← List.take_append_drop k c.fields, List.flatMap_append]
  simp only [List.append_assoc]

theorem sliceCursorAfter_tag4_combine (slot ptr : BitVec 64)
    (full pfx v1 v2 rest : List (BitVec 8))
    (hfull : full = pfx ++ (0x22#8 :: BitVec.ofNat 8 (v1 ++ v2).length :: ((v1 ++ v2) ++ rest))) :
    (ptr ↦ₛ pfx) ∗ ((ptr + BitVec.ofNat 64 pfx.length) ↦ₛ [0x22#8, BitVec.ofNat 8 (v1 ++ v2).length]) ∗
      ((ptr + BitVec.ofNat 64 pfx.length + 2#64) ↦ₛ v1) ∗
      ((ptr + BitVec.ofNat 64 pfx.length + 2#64 + BitVec.ofNat 64 v1.length) ↦ₛ v2) ∗
      Prost.sliceCursorAt slot
        (ptr + BitVec.ofNat 64 pfx.length + 2#64 + BitVec.ofNat 64 v1.length + BitVec.ofNat 64 v2.length)
        rest = Prost.sliceCursorAfter slot ptr full rest := by
  let fld : List (BitVec 8) := [0x22#8, BitVec.ofNat 8 (v1 ++ v2).length] ++ v1 ++ v2
  have hfull' : full = (pfx ++ fld) ++ rest := by rw [hfull]; simp [fld, List.append_assoc]
  rw [hfull', sliceCursorAfter_append_eq_seedChain]
  have hpfx : (ptr ↦ₛ (pfx ++ fld)) = (ptr ↦ₛ pfx) ∗ ((ptr + BitVec.ofNat 64 pfx.length) ↦ₛ fld) :=
    pointsToBytes_append ptr pfx fld
  have hfld1 : ((ptr + BitVec.ofNat 64 pfx.length) ↦ₛ fld) =
      ((ptr + BitVec.ofNat 64 pfx.length) ↦ₛ [0x22#8, BitVec.ofNat 8 (v1 ++ v2).length]) ∗
      ((ptr + BitVec.ofNat 64 pfx.length + 2#64) ↦ₛ v1) ∗
      ((ptr + BitVec.ofNat 64 pfx.length + 2#64 + BitVec.ofNat 64 v1.length) ↦ₛ v2) := by
    dsimp only [fld]; rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append]
    have h2 : BitVec.ofNat 64 [0x22#8, BitVec.ofNat 8 (v1 ++ v2).length].length = 2#64 := rfl
    rw [h2]
  have hptr_eq : ptr + BitVec.ofNat 64 (pfx ++ fld).length =
      ptr + BitVec.ofNat 64 pfx.length + 2#64 + BitVec.ofNat 64 v1.length + BitVec.ofNat 64 v2.length := by
    simp only [fld, List.length_append, List.length_cons, List.length_nil]
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add]; congr 2; omega
  rw [hpfx, hfld1, hptr_eq]; ac_rfl

theorem chainMessageKeysG_ok (C : Crypto) (ctl : BitVec 64) {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat)
    (s : State) (hk : k < x.c.fields.length) (htag : (x.c.fields[k]'hk).tag = 4)
    (hs : ChainLoopG C ctl x R s0 k s) :
    ChainStepG C ctl x R s0 s (ChainLoopG C ctl x R s0 (k + 1)) abs := by
  rcases hs with ⟨hpc, hrun, htr, hvregs, hsym, hF, hsp, hsp_align, hx29, hx19, hx20, hx24,
    hx21, hx22, hx25, hx26, hOk, hlen_pay, hmem⟩
  obtain ⟨mk, hfl⟩ := chainField_eq_key_of_tag4 htag
  have hmk_mem : mk ∈ x.c.keys := mem_keys_of_key_mem_fields (hfl ▸ List.getElem_mem hk)
  have hseed : mk.seed.length = 32 := hOk.2.2.2.1 mk hmk_mem
  have hbound : (chainGAfter x.c k).keys.length ≤ maxMessageKeys :=
    le_trans (chainGAfter_keys_length_le x.c k) hOk.2.2.2.2
  have halign : s0.sp &&& 15#64 = 0#64 := sp0_aligned_of_sp_sub_256 hsp hsp_align
  let pfx : List (BitVec 8) :=
    encodeVarint (BitVec.ofNat 64 x.c.enc.length) ++ (x.c.fields.take k).flatMap ChainField.enc
  let rest : List (BitVec 8) := (x.c.fields.drop (k + 1)).flatMap ChainField.enc ++ x.tail
  let v1 : List (BitVec 8) := pbVarint 1 mk.counter.toNat
  let v2 : List (BitVec 8) := pbBytes 5 mk.seed
  have hpay_eq : x.c.payload ++ x.tail =
      pfx ++ (0x22#8 :: BitVec.ofNat 8 (v1 ++ v2).length :: ((v1 ++ v2) ++ rest)) := by
    rw [chainG_payload_split x.c k x.tail, drop_fields_flatMap_enc_of_key hk hfl x.tail,
      lenField_4_encMessageKey_eq hseed, encMessageKey_eq_pb hseed]; rfl
  have hcur_open : Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
      ((x.c.fields.drop k).flatMap ChainField.enc ++ x.tail) =
      (x.ptr ↦ₛ pfx) ∗ Prost.sliceCursorAt x.slot (x.ptr + BitVec.ofNat 64 pfx.length)
          (0x22#8 :: BitVec.ofNat 8 (v1 ++ v2).length :: ((v1 ++ v2) ++ rest)) := by
    have hrem : (x.c.fields.drop k).flatMap ChainField.enc ++ x.tail =
        0x22#8 :: BitVec.ofNat 8 (v1 ++ v2).length :: ((v1 ++ v2) ++ rest) := by
      rw [drop_fields_flatMap_enc_of_key hk hfl x.tail, lenField_4_encMessageKey_eq hseed,
        encMessageKey_eq_pb hseed]; rfl
    rw [hrem, hpay_eq, sliceCursorAfter_append_eq_seedChain]
  have hmk_lt : (v1 ++ v2).length < 128 := by
    rw [← encMessageKey_eq_pb hseed]; exact encMessageKey_length_lt128 hseed
  have htail_le : x.tail.length ≤ rest.length := by simp [rest]
  have hlen_a : 2 + ((v1 ++ v2).length + rest.length) < 2 ^ 32 := by
    have h := hlen_pay; rw [hpay_eq] at h; simp only [List.length_append, List.length_cons] at h ⊢; omega
  have hlen_b : (v1 ++ v2 ++ rest).length < 2 ^ 32 := by simp only [List.length_append] at hlen_a ⊢; omega
  have hlen_c : (v2 ++ rest).length < 2 ^ 32 := by simp only [List.length_append] at hlen_a ⊢; omega
  have hk_lt : mk.seed.length < 128 := by omega
  have hmem' : s.mem ⊨
      (prostChainGAt A0 x.a (chainGAfter x.c k) ∗ (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
          (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
        stackAt (s0.sp - 0x100#64) chainMergeSubStack ∗ chainMergeSavedRegs s0.sp s0) ∗ R :=
    Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  refine segStepG_of_sepWPp (ret := chainPC C ctl 0x120#64) hmem' ?_
  rw [prostChainGAt_eq_keys_sep_rest A0 x.a (chainGAfter x.c k),
    chainMergeSavedRegs_eq_split s0.sp s0, hcur_open]
  have hpc' : s.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64 := hpc
  refine SepWPp.focus_pre
    (step_tag4a C ctl x.a x.bufRef x.slot (x.ptr + BitVec.ofNat 64 pfx.length) s0.sp
      (v1 ++ v2) rest x.tail hmk_lt htail_le hlen_a hpc' hrun hsp hsp_align hF hsym htr hvregs
      hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx29 ?_)
  intro s1 hpc1 hrun1 hsp1 hsp_align1 hF1 hsym1 htr1 hvregs1 hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1
  rw [List.append_assoc v1 v2 rest]
  refine SepWPp.focus_pre
    (step_tag4b C ctl hC.2.1 x.a x.bufRef x.slot (x.ptr + BitVec.ofNat 64 pfx.length + 2#64)
      s0.sp mk.counter v2 rest x.tail hlen_b hpc1 hrun1 hsp1 halign hF1 hsym1 htr1 hvregs1
      hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 ?_)
  intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hvregs2 hx19_2 hx20_2 hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2
  refine SepWPp.focus_pre
    (step_tag4c C ctl hC.2.2.1 x.a x.bufRef x.slot
      (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 + BitVec.ofNat 64 v1.length) s0.sp
      mk.seed rest x.tail hk_lt hlen_c hpc2 hrun2 hsp2 halign hF2 hsym2 htr2 hvregs2
      hx19_2 hx20_2 hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 ?_)
  intro s3 hpc3 hrun3 hsp3 hF3 hsym3 htr3 hvregs3 hx19_3 hx20_3 hx21_3 hx22_3 hx24_3 hx25_3 hx26_3 hx28_3 hx29_3
  have hsp_align3 : s3.spAligned = true := spAligned_of_sp_eq (hsp3.trans hsp.symm) hsp_align
  apply SepWPp.fold (Entails.of_eq (prostMsgKeyAt_fold s0.sp mk)) (by sep_focus)
  refine SepWPp.focus_pre
    (step_tag4d C ctl hC.2.2.2 x.a x.bufRef x.slot
      (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 + BitVec.ofNat 64 v1.length + BitVec.ofNat 64 v2.length)
      s0.sp (chainGAfter x.c k).keys rest hbound
      hpc3 hrun3 hsp3 hsp_align3 hF3 hsym3 htr3 hvregs3 hx19_3 hx20_3 hx21_3 hx22_3
      hx24_3 hx25_3 hx26_3 hx28_3 hx29_3 ?_)
  intro s4 cap' ptr' hcap'_le hcap'_lt hptr' hpc4 hrun4 hsp4 hsp_align4 hF4 hsym4 htr4 hvregs4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4
  refine SepWPp.focus_pre
    (step_tag4e C ctl x.a cap' ptr' s0.sp (chainGAfter x.c k).keys mk
      hcap'_le hcap'_lt hptr' hpc4 hrun4 hsp4 hsp_align4 hF4 hsym4 htr4 hvregs4
      hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4 ?_)
  intro s5 hpc5 hrun5 hsp5 hsp_align5 hF5 hsym5 htr5 hvregs5 hx19_5 hx20_5 hx21_5 hx22_5 hx24_5 hx25_5 hx26_5 hx29_5
  refine SepWPp.of_sepWP_ret (SepWP.done hpc5 hrun5 ?_)
  intro hmf5
  refine ⟨hpc5, hrun5, htr5, hvregs5, hsym5, hF5, hsp5, hsp_align5, hx29_5,
    hx19_5, hx20_5, hx24_5, hx21_5, hx22_5, hx25_5, hx26_5,
    hOk, hlen_pay, ?_⟩
  rw [chainGAfter_succ_of_key hk hfl,
    prostChainGAt_eq_keys_sep_rest A0 x.a { chainGAfter x.c k with keys := (chainGAfter x.c k).keys ++ [mk] },
    prostChainGRest_update_keys,
    chainMergeSavedRegs_eq_split s0.sp s0,
    ← sliceCursorAfter_tag4_combine x.slot x.ptr (x.c.payload ++ x.tail) pfx v1 v2 rest hpay_eq]
  exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmf5

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
