/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Base
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChains
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Steps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

/-!
# Tag-7 Leaf (`mergeFieldGenReceiverChains_ok`) for `SessionStructure::merge_field`

Proves `mergeFieldGenReceiverChains_ok` for `receiver_chains` (tag `7`), decoding a `Chain` message
on the stack via `message::merge<Chain>` and pushing it into `Vec<Chain>` at `ss + 0x48` (calling
`RawVec<Chain>::grow_one` when `len = cap`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr sessionImg0
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

/-! ## Field and `prostChainGAt` Helpers -/

theorem eq_recv_of_tag_eq_7 {fld : GenField} (h : fld.tag = 7) :
    ∃ c : ChainG, fld = .recv c := by
  cases fld <;> simp [GenField.tag] at h
  exact ⟨_, rfl⟩

theorem vecOf104_msgKey_nil_0_8 (A : RustAlloc) (v : BitVec 64) :
    ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) ⊢
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) v [] := by
  unfold vecOf vecAt vecBuf
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_emp]
  rw [sepConj_comm (vecHeader v 0#64 8#64 0#64)]
  exact Entails.pure_right ⟨by decide, by decide, by decide⟩ (Entails.refl _)

theorem prostChainGAt_default_of_cells (A : RustAlloc) (sp0 : BitVec 64) :
    (((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗
      ((sp0 - 216#64) ↦₆₄ 0#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64) ∗
      ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64) ∗
      ((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 8#64) ∗
      ((sp0 - 168#64) ↦₆₄ 0#64) ∗ ((sp0 - 160#64) ↦₆₄ noneCap)) ∗
      memRegion (sp0 - 152#64) 24 ⊢
    prostChainGAt A (sp0 - 232#64) ChainG.empty := by
  unfold prostChainGAt ChainG.empty
  dsimp only
  have e1 : (sp0 - 232#64) + 8#64 = sp0 - 224#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2 : (sp0 - 232#64) + 16#64 = sp0 - 216#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3 : (sp0 - 232#64) + 0x18#64 = sp0 - 208#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e4 : (sp0 - 208#64) + 8#64 = sp0 - 200#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e5 : (sp0 - 208#64) + 16#64 = sp0 - 192#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e6 : (sp0 - 232#64) + 0x30#64 = sp0 - 184#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e7 : (sp0 - 184#64) + 8#64 = sp0 - 176#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e8 : (sp0 - 184#64) + 16#64 = sp0 - 168#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e9 : (sp0 - 232#64) + 0x48#64 = sp0 - 160#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e10 : (sp0 - 232#64) + 0x50#64 = sp0 - 152#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [e3, e6, e9, e10]
  have h1 := vecU8_nil_0_1_receiverChains A (sp0 - 232#64)
  rw [e1, e2] at h1
  have h2 := vecU8_nil_0_1_receiverChains A (sp0 - 208#64)
  rw [e4, e5] at h2
  have h3 := vecOf104_msgKey_nil_0_8 A (sp0 - 184#64)
  rw [e7, e8] at h3
  have hgrp :
      (((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗
        ((sp0 - 216#64) ↦₆₄ 0#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64) ∗
        ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64) ∗
        ((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 8#64) ∗
        ((sp0 - 168#64) ↦₆₄ 0#64) ∗ ((sp0 - 160#64) ↦₆₄ noneCap)) ∗
        memRegion (sp0 - 152#64) 24 =
      (((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64)) ∗
      (((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64)) ∗
      (((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 8#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64)) ∗
      (((sp0 - 160#64) ↦₆₄ noneCap) ∗ memRegion (sp0 - 152#64) 24) := by
    ac_rfl
  rw [hgrp]
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (Entails.refl _)))

theorem prostChainGAt_default_of_cells_lit (sp0 : BitVec 64) :
    ((sp0 - 232#64) ↦₆₄ 0#64) ∗
    ((sp0 - 224#64) ↦₆₄ 1#64) ∗
    ((sp0 - 216#64) ↦₆₄ 0#64) ∗
    ((sp0 - 208#64) ↦₆₄ 0#64) ∗
    ((sp0 - 200#64) ↦₆₄ 1#64) ∗
    ((sp0 - 192#64) ↦₆₄ 0#64) ∗
    ((sp0 - 184#64) ↦₆₄ 0#64) ∗
    ((sp0 - 176#64) ↦₆₄ 8#64) ∗
    ((sp0 - 168#64) ↦₆₄ 0#64) ∗
    ((sp0 - 160#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
    memRegion (sp0 - 152#64) 24 ⊢
    prostChainGAt A0 (sp0 - 232#64) ChainG.empty := by
  simpa only [noneCap, sepConj_assoc] using prostChainGAt_default_of_cells A0 sp0

theorem vecOf104_msgKey_move_bytes (A : RustAlloc) (keys : List MessageKeyGenerator) (a : BitVec 64) :
    vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) a keys ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 24 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ vecOf A 104 8 (fun mk b' => prostMsgKeyAt A mk b') b keys⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  unfold vecOf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  rw [RawByteMove.vecAt_eq_bytes_sep_buf A 104 8 (fun mk b => prostMsgKeyAt A mk b) a cap ptr keys]
  refine Entails.sepExists_right (vecHeaderBytes cap ptr (BitVec.ofNat 64 keys.length)) ?_
  refine Entails.sepExists_right (vecBuf A 104 8 (fun mk b => prostMsgKeyAt A mk b) cap ptr keys) ?_
  refine Entails.pure_right ⟨by simp [vecHeaderBytes], fun b => ?_⟩ (Entails.refl _)
  rw [← RawByteMove.vecAt_eq_bytes_sep_buf A 104 8 (fun mk b' => prostMsgKeyAt A mk b') b cap ptr keys]
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem prostChainGAt_eq_parts (A : RustAlloc) (a : BitVec 64) (c : ChainG) :
    prostChainGAt A a c =
      vecU8 A a c.srk ∗ vecU8 A (a + 0x18#64) c.priv ∗
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c.keys ∗
      prostCkAt_receiverChains A (a + 0x48#64) c.ck := by
  unfold prostChainGAt prostCkAt_receiverChains
  have e50 : a + 0x48#64 + 8#64 = a + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have e60 : a + 0x48#64 + 0x18#64 = a + 0x60#64 := by rw [BitVec.add_assoc]; rfl
  have e64 : a + 0x48#64 + 0x1c#64 = a + 0x64#64 := by rw [BitVec.add_assoc]; rfl
  cases c.ck with
  | none =>
    dsimp only
    rw [e50]
  | some ik =>
    rcases ik with ⟨i, k⟩
    dsimp only
    rw [e60, e64]

theorem prostChainGAt_move_bytes (A : RustAlloc) (c : ChainG) (a : BitVec 64) :
    prostChainGAt A a c ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 104 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ prostChainGAt A b c⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  have h12 := move_bytes_pair_receiverChains
    (P1 := fun b => vecU8 A b c.srk)
    (P2 := fun b => vecU8 A b c.priv)
    (n1 := 24) (n2 := 24) (off := 0x18#64) rfl
    (fun b => vecU8_move_bytes_receiverChains A b c.srk)
    (fun b => vecU8_move_bytes_receiverChains A b c.priv)
  have h123 := move_bytes_pair_receiverChains
    (P1 := fun b => vecU8 A b c.srk ∗ vecU8 A (b + 0x18#64) c.priv)
    (P2 := fun b => vecOf A 104 8 (fun mk b' => prostMsgKeyAt A mk b') b c.keys)
    (n1 := 48) (n2 := 24) (off := 0x30#64) rfl
    h12
    (vecOf104_msgKey_move_bytes A c.keys)
  have h1234 := move_bytes_pair_receiverChains
    (P1 := fun b => (vecU8 A b c.srk ∗ vecU8 A (b + 0x18#64) c.priv) ∗
      vecOf A 104 8 (fun mk b' => prostMsgKeyAt A mk b') (b + 0x30#64) c.keys)
    (P2 := fun b => prostCkAt_receiverChains A b c.ck)
    (n1 := 72) (n2 := 32) (off := 0x48#64) rfl
    h123
    (prostCkAt_move_bytes_receiverChains A c.ck) a
  have heq : ∀ b : BitVec 64,
      prostChainGAt A b c =
        ((vecU8 A b c.srk ∗ vecU8 A (b + 0x18#64) c.priv) ∗
          vecOf A 104 8 (fun mk b' => prostMsgKeyAt A mk b') (b + 0x30#64) c.keys) ∗
        prostCkAt_receiverChains A (b + 0x48#64) c.ck := by
    intro b
    rw [prostChainGAt_eq_parts A b c]
    ac_rfl
  simp only [show (72 : Nat) + 32 = 104 from rfl, ← heq] at h1234
  exact h1234

theorem prostChainGAt_move_chunks104 (A : RustAlloc) (a : BitVec 64) (c : ChainG) :
    prostChainGAt A a c ⊢
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128,
      ∃∗ q3 : BitVec 128, ∃∗ q4 : BitVec 128, ∃∗ q5 : BitVec 128,
      ∃∗ w6 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ b : BitVec 64,
          (RawByteMove.chunks104_6QWAt b q0 q1 q2 q3 q4 q5 w6 ∗ H) ⊢ prostChainGAt A b c⌝ ∗
        RawByteMove.chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 ∗ H := by
  refine Entails.trans (prostChainGAt_move_bytes A c a) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.sepExists_elim; intro H
  apply Entails.pure_left; rintro ⟨hlen, hmov⟩
  obtain ⟨q0, q1, q2, q3, q4, q5, w6, _, hchunks⟩ := RawByteMove.exists_bytes104Of6QW hlen
  rw [hchunks a]
  refine Entails.sepExists_right q0 (Entails.sepExists_right q1
    (Entails.sepExists_right q2 (Entails.sepExists_right q3
      (Entails.sepExists_right q4 (Entails.sepExists_right q5
        (Entails.sepExists_right w6 (Entails.sepExists_right H ?_)))))))
  refine Entails.pure_right (fun b => ?_) (Entails.refl _)
  rw [← hchunks b]
  exact hmov b

theorem arrayAt_prostChainGAt_move_bytes (A : RustAlloc) (cs : List ChainG) (a : BitVec 64) :
    arrayAt (fun c b => prostChainGAt A b c) 104 a cs ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = cs.length * 104 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ arrayAt (fun c b' => prostChainGAt A b' c) 104 b cs⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  induction cs generalizing a with
  | nil =>
    dsimp only [arrayAt, List.length_nil, Nat.zero_mul]
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_)
    rw [pointsToBytes_nil, sepConj_emp]
    refine Entails.pure_right ⟨rfl, fun b => ?_⟩ (Entails.refl _)
    rw [pointsToBytes_nil, sepConj_emp]
    exact Entails.refl _
  | cons c cs ih =>
    dsimp only [arrayAt]
    have hm := move_bytes_pair_receiverChains
      (P1 := fun b => prostChainGAt A b c)
      (P2 := fun b => arrayAt (fun c' b' => prostChainGAt A b' c') 104 b cs)
      (n1 := 104) (n2 := cs.length * 104) (off := BitVec.ofNat 64 104) rfl
      (prostChainGAt_move_bytes A c)
      ih a
    have hlen : 104 + cs.length * 104 = (c :: cs).length * 104 := by
      simp [List.length_cons, Nat.add_mul]; omega
    rw [hlen] at hm
    exact hm

/-! ## `prostSSGAt` `recv` Open/Close and `growOneSpec` Helpers -/

def prostSSGRest (A : RustAlloc) (ss : BitVec 64) (v : SSG) : SepProp :=
  vecU8 A ss v.lik ∗ vecU8 A (ss + 0x18#64) v.rik ∗ vecU8 A (ss + 0x30#64) v.root ∗
    vecU8 A (ss + 0x60#64) [] ∗ vecU8 A (ss + 0x78#64) [] ∗
    (match v.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.prevCounter) ∗
    ((ss + 0x150#64) ↦₆₄ 0#64)

theorem prostSSGAt_eq_recv_sep_rest (A : RustAlloc) (ss : BitVec 64) (v : SSG) :
    prostSSGAt A ss v =
      vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.recv ∗
        prostSSGRest A ss v := by
  unfold prostSSGAt prostSSGRest
  ac_rfl

theorem prostSSGRest_apply_recv (A : RustAlloc) (ss : BitVec 64) (v : SSG) (c : ChainG) :
    prostSSGRest A ss (v.apply (.recv c)) = prostSSGRest A ss v := rfl

theorem vecAt_recv_open (ss : BitVec 64) (cs : List ChainG) :
    vecOf A0 104 8 (fun c a => prostChainGAt A0 a c) (ss + 0x48#64) cs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cs.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
        ((ss + 0x58#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        (if cap = 0#64 then emp
         else arrayAt (fun c a => prostChainGAt A0 a c) 104 ptr cs ∗
           memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) := by
  unfold vecOf vecAt vecHeader vecBuf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have e58 : ss + 0x48#64 + 16#64 = ss + 0x58#64 := by rw [BitVec.add_assoc]; rfl
  have hlive : A0.live ptr (cap.toNat * 104) 8 = emp := rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [e50, e58, hlive, h0]
  simp only [emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem ofNat_length_eq_cap_of_eq {cs : List ChainG} {cap : BitVec 64}
    (h : cs.length = cap.toNat) :
    BitVec.ofNat 64 cs.length = cap := by
  rw [h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem beq_ofNat_len_cap_false {cs : List ChainG} {cap : BitVec 64}
    (hlt : cs.length < cap.toNat) :
    (BitVec.ofNat 64 cs.length == cap) = false := by
  have hne : BitVec.ofNat 64 cs.length ≠ cap := by
    intro h
    have h' := congrArg BitVec.toNat h
    have hcap := cap.isLt
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
    omega
  cases hb : (BitVec.ofNat 64 cs.length == cap)
  · rfl
  · exact False.elim (hne (eq_of_beq hb))

theorem vecBuf_recv_full_open (cap ptr : BitVec 64) (cs : List ChainG)
    (hfull : cs.length = cap.toNat) :
    (if cap = 0#64 then emp
     else arrayAt (fun c a => prostChainGAt A0 a c) 104 ptr cs ∗
       memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = cap.toNat * 104 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ arrayAt (fun c b' => prostChainGAt A0 b' c) 104 b cs⌝ ∗
        (if cap = 0#64 then emp else A0.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗ H := by
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hcs : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hfull)
    subst hcs
    simp only [↓reduceIte, BitVec.toNat_ofNat]
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_)
    rw [emp_sepConj]
    refine Entails.pure_right ⟨rfl, fun b => ?_⟩ (Entails.refl _)
    rw [pointsToBytes_nil, sepConj_emp]
    exact Entails.refl _
  · simp only [hcap0, ↓reduceIte]
    have hrem : (cap.toNat - cs.length) * 104 = 0 := by omega
    rw [hrem, ProofLib.memRegion_zero, sepConj_emp]
    refine Entails.trans (arrayAt_prostChainGAt_move_bytes A0 cs ptr) ?_
    apply Entails.sepExists_elim; intro bs
    apply Entails.sepExists_elim; intro H
    apply Entails.pure_left; rintro ⟨hbs_len, hmov⟩
    have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs_len, hfull]
    have hlive' : A0.live ptr bs.length 8 = emp := rfl
    refine Entails.sepExists_right bs (Entails.sepExists_right H ?_)
    rw [hlive', emp_sepConj]
    exact Entails.pure_right ⟨hbs_cap, hmov⟩ (Entails.refl _)

theorem vecBuf_recv_not_full_open (cap ptr : BitVec 64) (cs : List ChainG)
    (hlt : cs.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) :
    (if cap = 0#64 then emp
     else arrayAt (fun c a => prostChainGAt A0 a c) 104 ptr cs ∗
       memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) =
      (arrayAt (fun c b => prostChainGAt A0 b c) 104 ptr cs ∗
        memRegion (ptr + BitVec.ofNat 64 cs.length * 104#64) 104 ∗
        memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
          ((cap.toNat - (cs.length + 1)) * 104)) := by
  have hcap0 : cap ≠ 0#64 := by
    intro h0; subst h0; simp at hlt
  simp only [hcap0, ↓reduceIte]
  have hrem : (cap.toNat - cs.length) * 104 =
      104 + (cap.toNat - (cs.length + 1)) * 104 := by
    have : cap.toNat - cs.length = 1 + (cap.toNat - (cs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  have hoff :
      ptr + BitVec.ofNat 64 (cs.length * 104) + BitVec.ofNat 64 104 =
        ptr + BitVec.ofNat 64 ((cs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hrem, memRegion_split (ptr + BitVec.ofNat 64 (cs.length * 104)) 104 _ (by omega),
      hoff, hmul]

theorem growOne_inImage_pre_eq (ss cap ptr sp : BitVec 64) (bs : List (BitVec 8))
    (s : State) (hsp : s.sp = sp) :
    ((CryptoVerification.LibsignalSession.growOneSpec A0).inImage sessionImg0).pre
      (ss + 0x48#64, cap, ptr, bs) s =
    ⌜(bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = ss + 0x48#64 ∧
        ptr ≠ 0#64 ∧ 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63) ∧
      sessionImg0.FrozenLoaded s ∧ s.symtab = sessionImg0.symtab⌝ ∗
    (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
      (if cap = 0#64 then emp else A0.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
      stackAt sp 4608) := by
  unfold Spec.inImage CryptoVerification.LibsignalSession.growOneSpec
  dsimp only
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have hpool : A0.pool = emp := rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [e50, hpool, hsp, h0]
  simp only [emp_sepConj, ← sepConj_assoc, pure_sepConj_pure]
  ac_rfl

theorem growOne_post_elim_sp (ss cap ptr sp : BitVec 64) (cs : List ChainG)
    (bs : List (BitVec 8)) (s_pre sf : State)
    (hsp : s_pre.sp = sp)
    (hfull : cs.length = cap.toNat)
    (hlt5 : cs.length < maxReceiverChains)
    (hbs : bs.length = cap.toNat * 104) :
    ((CryptoVerification.LibsignalSession.growOneSpec A0).inImage sessionImg0).post
        (ss + 0x48#64, cap, ptr, bs) s_pre sf ⊢
      ⌜sf.trace = s_pre.trace⌝ ∗
      ∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜cs.length < cap'.toNat ∧ cap'.toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        ((ss + 0x48#64) ↦₆₄ cap') ∗ ((ss + 0x50#64) ↦₆₄ p') ∗
        (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 cs.length * 104#64) 104 ∗
        memRegion (p' + BitVec.ofNat 64 ((cs.length + 1) * 104))
          ((cap'.toNat - (cs.length + 1)) * 104) ∗
        stackAt sp 4608 := by
  unfold Spec.inImage CryptoVerification.LibsignalSession.growOneSpec
  dsimp only
  apply Entails.pure_left; intro htr
  refine Entails.pure_right htr ?_
  apply Entails.sepExists_elim; intro p'
  set newCap : Nat := max (2 * cap.toNat) 4
  set cap' : BitVec 64 := BitVec.ofNat 64 newCap
  have h5 : maxReceiverChains = 5 := rfl
  have hcap'_toNat : cap'.toNat = newCap := by
    dsimp only [cap', newCap]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt_cap' : cs.length < cap'.toNat := by omega
  have hcap'_lt : cap'.toNat * 104 < 2 ^ 63 := by omega
  refine Entails.sepExists_right cap' (Entails.sepExists_right p' ?_)
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have hlive : A0.live p' (newCap * 104) 8 = emp := rfl
  have hpool : A0.pool = emp := rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [e50, hlive, hpool, hsp, h0]
  simp only [emp_sepConj]
  apply Entails.pure_left; intro hp'
  refine Entails.pure_right ⟨hlt_cap', hcap'_lt, hp'⟩ ?_
  have hrem : (newCap - cap.toNat) * 104 =
      104 + (cap'.toNat - (cs.length + 1)) * 104 := by
    have : newCap - cap.toNat = 1 + (cap'.toNat - (cs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hbs_eq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 (cs.length * 104) := by
    rw [hbs, hfull]
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  have hoff :
      p' + BitVec.ofNat 64 (cs.length * 104) + BitVec.ofNat 64 104 =
        p' + BitVec.ofNat 64 ((cs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hbs_eq, hrem,
      memRegion_split (p' + BitVec.ofNat 64 (cs.length * 104)) 104 _ (by omega),
      hoff, hmul]
  exact Entails.of_eq (by ac_rfl)

theorem vecAt_recv_push_fold (ss cap ptr : BitVec 64) (cs : List ChainG) (c : ChainG)
    (hlt : cs.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
      ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64)) ∗
      arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr cs ∗
      prostChainGAt A0 (ptr + BitVec.ofNat 64 cs.length * 104#64) c ∗
      memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
        ((cap.toNat - (cs.length + 1)) * 104) ⊢
    vecOf A0 104 8 (fun c' a => prostChainGAt A0 a c') (ss + 0x48#64) (cs ++ [c]) := by
  have hne0 : cap ≠ 0 := by
    intro h0; subst h0; simp at hlt
  have hlive : A0.live ptr (cap.toNat * 104) 8 = emp := rfl
  unfold vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have e58 : ss + 0x48#64 + 16#64 = ss + 0x58#64 := by rw [BitVec.add_assoc]; rfl
  have hlen_app : (cs ++ [c]).length = cs.length + 1 := by simp
  have hlen_bv : BitVec.ofNat 64 (cs.length + 1) = BitVec.ofNat 64 cs.length + 1#64 := by
    rw [BitVec.ofNat_add]
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  have h0 : (ptr ≠ (0 : BitVec 64)) = (ptr ≠ 0#64) := rfl
  rw [e50, e58, hlive, hlen_app, hlen_bv, arrayAt_concat, hmul, h0]
  simp only [hne0, ↓reduceIte, emp_sepConj]
  have hgrp :
      (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
        ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64))) ∗
        (⌜cs.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          (arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr cs ∗
            prostChainGAt A0 (ptr + BitVec.ofNat 64 cs.length * 104#64) c) ∗
          memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
            ((cap.toNat - (cs.length + 1)) * 104)) =
      ⌜cs.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
          ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64)) ∗
          arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr cs ∗
          prostChainGAt A0 (ptr + BitVec.ofNat 64 cs.length * 104#64) c ∗
          memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
            ((cap.toNat - (cs.length + 1)) * 104)) := by
    ac_rfl
  rw [hgrp]
  exact Entails.pure_right ⟨by omega, hcap_lt, hptr⟩ (Entails.refl _)

theorem prostSSGAt_fold_apply_recv (ss cap ptr : BitVec 64) (v : SSG) (c : ChainG)
    (hlt : v.recv.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
      ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 v.recv.length + 1#64)) ∗
      arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr v.recv ∗
      prostChainGAt A0 (ptr + BitVec.ofNat 64 v.recv.length * 104#64) c ∗
      memRegion (ptr + BitVec.ofNat 64 ((v.recv.length + 1) * 104))
        ((cap.toNat - (v.recv.length + 1)) * 104) ∗
      prostSSGRest A0 ss v) ⊢
    prostSSGAt A0 ss (v.apply (.recv c)) := by
  rw [prostSSGAt_eq_recv_sep_rest A0 ss (v.apply (.recv c)),
      prostSSGRest_apply_recv A0 ss v c]
  dsimp only [SSG.apply]
  have hgrp :
      (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
        ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 v.recv.length + 1#64)) ∗
        arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr v.recv ∗
        prostChainGAt A0 (ptr + BitVec.ofNat 64 v.recv.length * 104#64) c ∗
        memRegion (ptr + BitVec.ofNat 64 ((v.recv.length + 1) * 104))
          ((cap.toNat - (v.recv.length + 1)) * 104) ∗
        prostSSGRest A0 ss v) =
      (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
        ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 v.recv.length + 1#64)) ∗
        arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr v.recv ∗
        prostChainGAt A0 (ptr + BitVec.ofNat 64 v.recv.length * 104#64) c ∗
        memRegion (ptr + BitVec.ofNat 64 ((v.recv.length + 1) * 104))
          ((cap.toNat - (v.recv.length + 1)) * 104)) ∗
      prostSSGRest A0 ss v := by
    ac_rfl
  rw [hgrp]
  exact sepConj_mono_left (vecAt_recv_push_fold ss cap ptr v.recv c hlt hcap_lt hptr)

/-! ## Stepping Lemmas and `mergeFieldGenReceiverChains_ok` -/

attribute [local irreducible] prostSSGRest prostChainGAt prostSSGAt mfFramePad_receiverChains
  Prost.sliceCursorAt Prost.sliceCursorAfter mfSavedRegs_receiverChains

theorem recv_payload_append_eq {fld : GenField} {c : ChainG} (hfld : fld = .recv c)
    (tail : List (BitVec 8)) :
    c.payload ++ tail = fld.payload ++ tail := by
  subst hfld
  rfl

theorem chainMergeGen_pre_eq (x : MergeFieldGenGhost) (c : ChainG) (s0_sp_232 sp : BitVec 64)
    (s : State) (hfld : x.fld = .recv c) (hsp : s.sp = sp) :
    chainMergeGenSpec.pre ⟨s0_sp_232, c, x.bufRef, x.slot, x.ptr, x.tail⟩ s =
      ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = s0_sp_232 ∧
        s.readReg64 .x2 = x.bufRef ∧ (s.readReg64 .x3).setWidth 32 = 99#32 ∧
        c.Ok ∧ (x.fld.payload ++ x.tail).length < 2 ^ 32 ∧
        sessionImg0.FrozenLoaded s ∧ s.symtab = sessionImg0.symtab⌝ ∗
      (prostChainGAt A0 s0_sp_232 ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
        stackAt sp chainMergeStack) := by
  unfold chainMergeGenSpec
  dsimp only
  rw [recv_payload_append_eq hfld x.tail, hsp]

theorem chainMergeGen_post_eq (x : MergeFieldGenGhost) (c : ChainG) (s0_sp_232 sp : BitVec 64)
    (s_pre sf : State) (hfld : x.fld = .recv c) (hsp : s_pre.sp = sp) :
    chainMergeGenSpec.post ⟨s0_sp_232, c, x.bufRef, x.slot, x.ptr, x.tail⟩ s_pre sf ⊢
      ⌜sf.trace = s_pre.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostChainGAt A0 s0_sp_232 c ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt sp chainMergeStack := by
  unfold chainMergeGenSpec
  dsimp only
  rw [recv_payload_append_eq hfld x.tail, hsp]
  exact Entails.refl _

/-- Step from `+0x45c` (`entry + 1116#64`) through the 104-byte `Chain` move and epilogue
(`+0x758..+0x770`) to `ret`. -/
theorem step_receiverChains_from_0x45c_to_ret
    (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (P : GenField → Prop) (x : MergeFieldGenGhost) (c : ChainG)
    (s0 s : State) (Fr : SepProp) (w56 cap' ptr' : BitVec 64)
    (hfld : x.fld = .recv c)
    (hlt : x.v.recv.length < cap'.toNat) (hcap_lt : cap'.toNat * 104 < 2 ^ 63) (hptr : ptr' ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName + 1116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (hsp_align : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = x.ss)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.v.recv.length)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAt sessionImg0.base C ctl abs) (s0.readReg64 Reg.lr) s
      (((x.ss + 0x48#64) ↦₆₄ cap') ∗ ((x.ss + 0x50#64) ↦₆₄ ptr') ∗
        ((x.ss + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.v.recv.length) ∗
        arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr' x.v.recv ∗
        memRegion (ptr' + BitVec.ofNat 64 x.v.recv.length * 104#64) 104 ∗
        memRegion (ptr' + BitVec.ofNat 64 ((x.v.recv.length + 1) * 104))
          ((cap'.toNat - (x.v.recv.length + 1)) * 104) ∗
        prostSSGRest A0 x.ss x.v ∗
        prostChainGAt A0 (s0.sp - 232#64) c ∗
        mfSavedRegs_receiverChains s0.sp s0 w56 ∗ mfFramePad_receiverChains s0.sp ∗
        stackAt (s0.sp - 240#64) mfSubStack_receiverChains ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (mergeFieldGenSpec P).post x s0 sf ∗ Fr)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  mf7_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1116 1196
  mf7_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1880 1904
  dsimp only [tripleRatchetProgAt, mergeFieldName] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" = entry
  examples_hide_fetches
  apply SepWP.fold (prostChainGAt_move_chunks104 A0 (s0.sp - 232#64) c) (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro q0
  apply SepWP.exists_elim; intro q1
  apply SepWP.exists_elim; intro q2
  apply SepWP.exists_elim; intro q3
  apply SepWP.exists_elim; intro q4
  apply SepWP.exists_elim; intro q5
  apply SepWP.exists_elim; intro w6
  apply SepWP.exists_elim; intro H
  apply SepWP.pure_elim; intro hmov
  set dst : BitVec 64 := ptr' + BitVec.ofNat 64 x.v.recv.length * 104#64
  apply SepWP.fold (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_receiverChains dst)) (by sep_focus)
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro d0
  apply SepWP.exists_elim; intro d1
  apply SepWP.exists_elim; intro d2
  apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d4
  apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro dw6
  conv => arg 4; rw [chunks104_6QWAt_stack_eq_receiverChains s0.sp q0 q1 q2 q3 q4 q5 w6,
    chunks104_6QWAt_dst_eq_receiverChains dst d0 d1 d2 d3 d4 d5 dw6, mfSavedRegs_receiverChains]
  wp_steps
  conv => arg 4; rw [← chunks104_6QWAt_dst_eq_receiverChains dst q0 q1 q2 q3 q4 q5 w6,
    ← chunks104_6QWAt_stack_eq_receiverChains s0.sp q0 q1 q2 q3 q4 q5 w6,
    ← mfSavedRegs_receiverChains]
  apply SepWP.fold (hmov dst) (by sep_focus)
  apply SepWP.fold (prostSSGAt_fold_apply_recv x.ss cap' ptr' x.v c hlt hcap_lt hptr) (by sep_focus)
  apply SepWP.fold (stackAt_receiverChains_epilogue_fold_receiverChains s0.sp s0 w56 q0 q1 q2 q3 q4 q5 w6) (by sep_focus)
  simp only [mergeFieldGenSpec, hfld]
  wp_done

/-- Step from `+0x2bc` (`entry + 700#64`, return of `message::merge<Chain>`) to `ret`,
handling both `x.v.recv.length = cap.toNat` (`grow_one` at `+0x9ac`) and `x.v.recv.length < cap.toNat`. -/
theorem step_receiverChains_from_0x2bc_to_ret
    (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hG : subroutine_ok (tripleRatchetProgAt sessionImg0.base C ctl abs)
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr growOneChainName)
      ((CryptoVerification.LibsignalSession.growOneSpec A0).inImage sessionImg0))
    (P : GenField → Prop) (x : MergeFieldGenGhost) (c : ChainG)
    (s0 s : State) (Fr : SepProp) (w56 : BitVec 64)
    (hfresh : x.v.recv.length < maxReceiverChains)
    (hfld : x.fld = .recv c)
    (hF : sessionImg0.FrozenLoaded s)
    (hsym : s.symtab = sessionImg0.symtab)
    (hpc : s.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName + 700#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (hsp_align : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx20 : s.readReg64 .x20 = x.ss)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) (s0.readReg64 Reg.lr) s
      (prostChainGAt A0 (s0.sp - 232#64) c ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
        stackAt (s0.sp - 240#64) chainMergeStack ∗
        memRegion ((s0.sp - 240#64) - 16144#64) 3856 ∗
        mfSavedRegs_receiverChains s0.sp s0 w56 ∗
        mfFramePad_receiverChains s0.sp ∗
        prostSSGAt A0 x.ss x.v)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (mergeFieldGenSpec P).post x s0 sf ∗ Fr)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (mergeFieldGenSpec P).onPanic x s0 sf ∗ Fr)) := by
  have hG' : subroutine_ok (tripleRatchetProgAt sessionImg0.base C ctl abs)
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"))
      ((CryptoVerification.LibsignalSession.growOneSpec A0).inImage sessionImg0) := by
    rwa [growOneChain_fnAddr_eq_receiverChains]
  have h45c := @step_receiverChains_from_0x45c_to_ret C ctl abs P x c s0
  mf7_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 700 700
  mf7_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1096 1112
  mf7_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 2472 2484
  dsimp only [tripleRatchetProgAt, mergeFieldName] at hG' h45c hpc ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" = entry
  examples_hide_fetches
  apply SepWPp.fold (Entails.of_eq (stackAt_sub_to_chainMerge_receiverChains (s0.sp - 240#64)).symm) (by sep_focus)
  rw [prostSSGAt_eq_recv_sep_rest A0 x.ss x.v]
  apply SepWPp.fold (vecAt_recv_open x.ss x.v.recv) (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_left; rintro ⟨hlen_le, hcap_lt, hptr⟩
  by_cases hfull : x.v.recv.length = cap.toNat
  · apply SepWPp.fold (vecBuf_recv_full_open cap ptr x.v.recv hfull) (by sep_focus)
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro bs
    apply SepWPp.exists_elim; intro H
    apply SepWPp.pure_left; rintro ⟨hbs_len, hmov⟩
    have hlen_cap : BitVec.ofNat 64 x.v.recv.length = cap := ofNat_length_eq_cap_of_eq hfull
    have hmax_lt : 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 := by
      have h5 : maxReceiverChains = 5 := rfl
      omega
    rw [hlen_cap, stackAt_sub_to_growOne_receiverChains (s0.sp - 240#64)]
    apply of_sepWP_inImage_receiverChains (entry + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) hF hsym
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) ?_
    intro hF1 hsym1
    refine SepWPp.call_frame (x := (x.ss + 0x48#64, cap, ptr, bs))
      (ret_pc := entry + bv% (2480)) hG'
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm] at hsp_align ⊢; exact hsp_align)
      (by simp only [arm64_norm])
      (growOne_inImage_pre_eq x.ss cap ptr (s0.sp - 240#64) bs _ (by simp only [arm64_norm, hsp]))
      ⟨⟨hbs_len, by simp only [arm64_norm], hptr, hmax_lt⟩, hF1, hsym1⟩
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans_receiverChains (by simp only [arm64_norm, htr])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, hvregsm⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hx20, hx26, hx27, hx28, hsp, hvregs] at hpcm hspm hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m hx28m hfpm hvregsm
    have hsp_align_m : sm.spAligned = true := by
      simp only [State.spAligned] at hsp_align ⊢
      rw [hspm, ← hsp]
      exact hsp_align
    refine SepWPp.fold
      (growOne_post_elim_sp x.ss cap ptr (s0.sp - 240#64) x.v.recv bs _ sm ?_ hfull hfresh hbs_len) rfl ?_
    · simp only [arm64_norm, hsp]
    simp only [sepConj_assoc]
    apply SepWPp.pure_left; intro htr_m
    have htr_m' : sm.trace = s0.trace := by simpa only [arm64_norm, htr] using htr_m
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro cap'
    apply SepWPp.exists_elim; intro p'
    apply SepWPp.pure_left; rintro ⟨hlt_cap', hcap_lt', hp'⟩
    apply SepWPp.fold (hmov p') (by sep_focus)
    apply SepWPp.fold (Entails.of_eq (stackAt_sub_to_growOne_receiverChains (s0.sp - 240#64)).symm) (by sep_focus)
    rw [← hlen_cap] at hx19m ⊢
    apply SepWPp.of_sepWP (mid := entry + bv% (1116))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre ?_
      (h45c _ Fr w56 cap' p' hfld hlt_cap' hcap_lt' hp' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · exact Entails.of_eq (by ac_rfl)
    · simp only [arm64_norm]
    · simp only [arm64_norm, hrunm]
    · simp only [arm64_norm, hspm]
    · simp only [State.spAligned, arm64_norm] at hsp_align_m ⊢; exact hsp_align_m
    · simp only [arm64_norm, htr_m']
    · simp only [arm64_norm]
    · simp only [arm64_norm, hx19m]
    · simp only [arm64_norm, hx26m]
    · simp only [arm64_norm, hx27m]
    · simp only [arm64_norm, hx28m]
    · simp only [arm64_norm, hvregsm]
  · have hlt : x.v.recv.length < cap.toNat := by omega
    have hbeq : (BitVec.ofNat 64 x.v.recv.length == cap) = false := beq_ofNat_len_cap_false hlt
    rw [vecBuf_recv_not_full_open cap ptr x.v.recv hlt hcap_lt]
    apply SepWPp.of_sepWP (mid := entry + bv% (1116))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre ?_
      (h45c _ Fr w56 cap ptr hfld hlt hcap_lt hptr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · exact Entails.of_eq (by ac_rfl)
    · simp only [arm64_norm]
    · simp only [arm64_norm, hrun]
    · simp only [arm64_norm, hsp]
    · simp only [State.spAligned, arm64_norm] at hsp_align ⊢; exact hsp_align
    · simp only [arm64_norm, htr]
    · simp only [arm64_norm]
    · simp only [arm64_norm]
    · simp only [arm64_norm, hx26]
    · simp only [arm64_norm, hx27]
    · simp only [arm64_norm, hx28]
    · simp only [arm64_norm, hvregs]

theorem mergeFieldGenReceiverChains_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (hCh : ChainMergeGenOk C ctl abs) :
    MergeFieldGenOk C ctl (fun fl => fl.tag = 7) abs := by
  apply subroutine_ok_of_sepWPp
  intro x Fr s0 hpc hrun hpre hsp
  refine ⟨_, Fr, hpre, ?_⟩
  conv => arg 4; dsimp only [mergeFieldGenSpec]
  apply SepWPp.pure_left
  rintro ⟨hx0, hx1, hx2, hx3, hx4, htag, hOk, hFresh, hlen, hF, hsym⟩
  obtain ⟨c, hfld⟩ := eq_recv_of_tag_eq_7 htag
  have hcOk : c.Ok := by rw [hfld] at hOk; exact hOk.1
  have hfresh : x.v.recv.length < maxReceiverChains := by rw [hfld] at hFresh; exact hFresh
  rw [hfld] at hx1 hx2
  dsimp only [GenField.tag, GenField.wt, CryptoVerification.LibsignalProtoCodec.WireType.toNat,
    BitVec.ofNat_eq_ofNat] at hx1 hx2
  have hx2' : BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x2)) &&& 255#64 = 2#64 :=
    zext64_trunc32_and_255_eq_of_trunc8_receiverChains hx2
  have hsp0 : s0.sp &&& 15#64 = 0#64 := eq_of_beq hsp
  have hsp240 : (s0.sp - 240#64) &&& 15#64 = 0#64 := sp_sub_240_aligned_receiverChains hsp0
  have hsp240_beq : ((s0.sp - 240#64) &&& 15#64 == 0#64) = true := beq_iff_eq.mpr hsp240
  have he : (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName =
      sessionImg0.base + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") :=
    mergeField_fnAddr_eq_base_add_receiverChains C ctl
  have hCh' : subroutine_ok (tripleRatchetProgAt sessionImg0.base C ctl abs)
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")))
      chainMergeGenSpec := by
    rw [chainMerge_fnAddr_eq_receiverChains]
    exact hCh
  have h2bc := @step_receiverChains_from_0x2bc_to_ret C ctl abs hC.2.2.2
    (fun fl => fl.tag = 7) x c s0
  mf7_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0 60
  mf7_fetches_range sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) 628 696
  rw [stackAt_mergeFieldStack_split_receiverChains s0.sp,
    memRegion80_chainInit_eq_cells10_receiverChains s0.sp,
    memRegion80_eq_cells10_receiverChains s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro c0
  apply SepWPp.exists_elim; intro c1
  apply SepWPp.exists_elim; intro c2
  apply SepWPp.exists_elim; intro c3
  apply SepWPp.exists_elim; intro c4
  apply SepWPp.exists_elim; intro c5
  apply SepWPp.exists_elim; intro c6
  apply SepWPp.exists_elim; intro c7
  apply SepWPp.exists_elim; intro c8
  apply SepWPp.exists_elim; intro c9
  apply SepWPp.exists_elim; intro w80
  apply SepWPp.exists_elim; intro w72
  apply SepWPp.exists_elim; intro w64
  apply SepWPp.exists_elim; intro w56
  apply SepWPp.exists_elim; intro w48
  apply SepWPp.exists_elim; intro w40
  apply SepWPp.exists_elim; intro w32
  apply SepWPp.exists_elim; intro w24
  apply SepWPp.exists_elim; intro w16
  apply SepWPp.exists_elim; intro w8
  dsimp only [tripleRatchetProgAt, mergeFieldName] at he hCh' h2bc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" = entry
  have hadrp : (entry + bv% (40) &&& bv% (2 ^ 64 - 4096)) = sessionImg0.base + 20480#64 :=
    adrp_0x4601c_40_eq_receiverChains he
  clear he
  examples_hide_fetches
  apply of_sepWP_inImage_receiverChains (entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"))) hF hsym
  apply sepWP_intro_rodata_tag7_receiverChains hF
  wp_steps
  apply sepWP_drop_left_receiverChains
  apply SepWP.fold (prostChainGAt_default_of_cells_lit s0.sp) (by sep_focus)
  apply SepWP.fold (mfSavedRegs_intro_receiverChains s0.sp s0 c3) (by sep_focus)
  apply SepWP.fold (Entails.of_eq (stackAt_sub_to_chainMerge_receiverChains (s0.sp - 240#64))) (by sep_focus)
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) ?_
  intro hF1 hsym1
  refine call_frame_inImage_receiverChains (ret_pc := entry + bv% (700)) hF1 hsym1 hCh'
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
    (by simp only [arm64_norm])
    (chainMergeGen_pre_eq x c (s0.sp - 232#64) (s0.sp - 240#64) _ hfld (by simp only [arm64_norm]))
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], hcOk, hlen, hF1, hsym1⟩
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans_receiverChains (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hF2 hsym2
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, hvregsm⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m hx28m hfpm hvregsm
  have hsp_align_m : sm.spAligned = true := by
    simp only [State.spAligned, hspm]
    exact hsp240_beq
  refine SepWPp.fold
    (chainMergeGen_post_eq x c (s0.sp - 232#64) (s0.sp - 240#64) _ sm hfld ?_) rfl ?_
  · simp only [arm64_norm]
  simp only [sepConj_assoc]
  apply SepWPp.pure_left; rintro ⟨htr_m, hx0_m⟩
  have htr_m' : sm.trace = s0.trace := by simpa only [arm64_norm] using htr_m
  refine SepWPp.weaken_pre ?_
    (h2bc sm Fr c3 hfresh hfld hF2 hsym2 hpcm hrunm hspm hsp_align_m htr_m' hx0_m hx20m hx26m hx27m hx28m hvregsm)
  have hsub16384 : (s0.sp - 240#64) - 16144#64 = s0.sp - 16384#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  exact Entails.of_eq (by rw [hsub16384]; ac_rfl)

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains





