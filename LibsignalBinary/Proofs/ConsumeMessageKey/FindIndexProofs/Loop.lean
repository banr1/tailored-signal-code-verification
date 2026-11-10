/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Deserialize
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEq
import all Init.Data.Nat.Bitwise.Basic
public import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import ProofLib.SepLogic.WP.Apply

@[expose] public section

namespace CryptoVerification.LibsignalSession.FindReceiverChainIndex

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

set_option maxRecDepth 400000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?

theorem deserialize_ok_at (b : BitVec 64) (H : String → Option (State → State))
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = 252980) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k)
      (deserializeSpec b) := by
  have h := deserialize_ok b H
  rwa [Program.fnAddr_rel hfn (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::deserialize") hk] at h

theorem publicKey_eq_ok_at (b : BitVec 64) {H : String → Option (State → State)}
    (h_bb : H "subtle::black_box::<u8>" = some blackBoxHook)
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = 257236) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k)
      publicKeyEqSpec := by
  have h := publicKey_eq_ok b h_bb
  rwa [Program.fnAddr_rel hfn (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq") hk] at h

theorem fnAddr_adrp_eacc {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr
      "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" +
      68#64) &&& 0xfffffffffffff000#64) = b + bv% (page% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 296)) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index"), BitVec.add_assoc,
    adrp_page_of_aligned hb]
  rfl

theorem fnAddr_adrp_ead0 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr
      "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" +
      72#64) &&& 0xfffffffffffff000#64) = b + bv% (page% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 296)) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index"), BitVec.add_assoc,
    adrp_page_of_aligned hb]
  rfl

theorem out33_entails_memRegion (sp : BitVec 64) {pk : List (BitVec 8)} (hpk : pk.length = 32) :
    ((sp - 248#64) ↦₈ 0#8) ∗ ((sp - 247#64) ↦ₛ pk) ⊢
      memRegion (sp - 248#64) 33 := by
  rw [ProofLib.memRegion_split' (b := sp - 248#64) (n := 1) (k := 32)
      (b' := sp - 247#64) rfl (by bv_omega) (by decide),
    memRegion_one]
  refine sepConj_mono (Entails.sepExists_right 0#8 (Entails.refl _)) ?_
  rw [← hpk]
  exact pointsToBytes_entails_memRegion (sp - 247#64) pk

theorem nat_lor_one (n : Nat) : (n ||| 1) = 2 * (n / 2) + 1 := by
  change Nat.bitwise or n 1 = 2 * (n / 2) + 1
  rw [Nat.bitwise]
  by_cases hn : n = 0
  · subst hn; rfl
  · simp only [hn, ↓reduceIte, show ¬(1 = 0) by decide,
      show 1 / 2 = 0 by rfl, show 1 % 2 = 1 by rfl, decide_true, Bool.or_true]
    rw [Nat.bitwise]
    by_cases hn2 : n / 2 = 0
    · simp [hn2]
    · simp [hn2]; omega

theorem sp_sub_248_orr_1 {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    (sp - 248#64) ||| 1#64 = sp - 247#64 := by
  have hmod : (sp - 248#64).toNat % 2 = 0 ∧ (sp - 248#64).toNat + 1 = (sp - 247#64).toNat := by
    have h16 : (sp &&& 15#64).toNat = 0 := by
      have heq : sp &&& 15#64 = 0#64 := beq_iff_eq.mp h
      rw [heq]; rfl
    rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 by rfl,
      Nat.and_two_pow_sub_one_eq_mod] at h16
    have hsp := sp.isLt
    rw [BitVec.toNat_sub, BitVec.toNat_sub]
    change (2 ^ 64 - 248 + sp.toNat) % 2 ^ 64 % 2 = 0 ∧
      (2 ^ 64 - 248 + sp.toNat) % 2 ^ 64 + 1 = (2 ^ 64 - 247 + sp.toNat) % 2 ^ 64
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or]
  change (sp - 248#64).toNat ||| 1 = (sp - 247#64).toNat
  rw [nat_lor_one]
  omega

theorem pk_208_merge {sp w0 w1 w2 w3 : BitVec 64} {pk : List (BitVec 8)}
    (hpk : ∀ a : BitVec 64,
      (a ↦ₛ pk) =
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) :
    ((sp - 208#64) ↦₆₄ w0) ∗ ((sp - 200#64) ↦₆₄ w1) ∗
      ((sp - 192#64) ↦₆₄ w2) ∗ ((sp - 184#64) ↦₆₄ w3) ⊢
      (sp - 208#64) ↦ₛ pk := by
  rw [hpk (sp - 208#64)]
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]
  exact Entails.refl _

theorem pk_247_merge {sp w0 w1 w2 w3 : BitVec 64} {pk : List (BitVec 8)}
    (hpk : ∀ a : BitVec 64,
      (a ↦ₛ pk) =
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) :
    ((sp - 247#64) ↦₆₄ w0) ∗ ((sp - 239#64) ↦₆₄ w1) ∗
      ((sp - 231#64) ↦₆₄ w2) ∗ ((sp - 223#64) ↦₆₄ w3) ⊢
      (sp - 247#64) ↦ₛ pk := by
  rw [hpk (sp - 247#64)]
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]
  exact Entails.refl _

def deserializeMemSpec (b : BitVec 64) : Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) where
  pre := fun (ptr, bs, pk, sret) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = sret ∧ bs.length < 2 ^ 63 ∧
      PublicKey.deserialize bs = .ok pk ∧
      b &&& 0xfff#64 = 0#64⌝ ∗
    (ptr ↦ₛ bs) ∗
    memRegion sret 33 ∗
    ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64)
  post := fun (ptr, bs, pk, sret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦ₛ bs) ∗
    (sret ↦₈ 0#8) ∗ ((sret + 1#64) ↦ₛ pk.bytes.toList) ∗
    ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64)

theorem memRegion_33_eq (sret : BitVec 64) :
    memRegion sret 33 =
      ∃∗ tag0 : BitVec 8, ∃∗ out32 : List (BitVec 8),
        ⌜out32.length = 32⌝ ∗ (sret ↦₈ tag0) ∗ ((sret + 1#64) ↦ₛ out32) := by
  rw [ProofLib.memRegion_split' (b := sret) (n := 1) (k := 32)
      (b' := sret + 1#64) rfl (by rfl) (by decide),
    memRegion_one, memRegion_eq_exists_bytes (sret + 1#64) 32 (by decide)]
  rw [sepExists_sepConj_left]
  apply congrArg sepExists; funext tag0
  rw [sepExists_sepConj_right]
  apply congrArg sepExists; funext out32
  rw [← sepConj_assoc, sepConj_comm (sret ↦₈ tag0), sepConj_assoc]

theorem deserializeMem_ok_at (b : BitVec 64) (H : String → Option (State → State))
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = 252980) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k)
      (deserializeMemSpec b) := by
  refine subroutine_ok_map (deserialize_ok_at b H hfn hk) ?_
  rintro ⟨ptr, bs, pk, sret⟩ R s0 hpre
  simp only [deserializeMemSpec, memRegion_33_eq] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at hpre
  rcases hpre with ⟨tag0, out32, hpre⟩
  rw [satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlt, hdeser, hb⟩, hpre⟩
  rw [sepConj_pure_left_comm (ptr ↦ₛ bs), satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hout32, hpre⟩
  refine ⟨(ptr, bs, pk, sret, tag0, out32), R, ?_, ?_⟩
  · dsimp only [deserializeSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlt, hdeser, hout32, hb⟩, hpre⟩
  · intro sf hpost
    exact hpost

theorem memRegion_16_eq_stackFrameFor_eq (sp : BitVec 64) :
    memRegion (sp - 16#64) 16 =
      stackFrameFor libsignalSessionImage
        "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp := by
  rw [show (16 : Nat) = 8 * 2 by rfl, memRegion_cells (sp - 16#64) 2 (by decide)]
  cells_unfold
  simp only [stackFrameFor, libsignalSessionCode_frameBytes_0x3ecd4, reduceStackFrameAt]

theorem memRegion_48_eq_stackFrameFor_ct_eq (sp : BitVec 64) :
    memRegion (sp - 48#64) 48 =
      stackFrameFor libsignalSessionImage
        "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp := by
  rw [show (48 : Nat) = 8 * 6 by rfl, memRegion_cells (sp - 48#64) 6 (by decide)]
  cells_unfold
  simp only [stackFrameFor, libsignalSessionCode_frameBytes_0x3eda8, reduceStackFrameAt]

def publicKeyEqMemSpec : Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    memRegion (sp - 16#64) 16 ∗
    memRegion (sp - 16#64 - 48#64) 48
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    memRegion (sp - 16#64) 16 ∗
    memRegion (sp - 16#64 - 48#64) 48

theorem publicKeyEqMem_ok_at (b : BitVec 64) {H : String → Option (State → State)}
    (h_bb : H "subtle::black_box::<u8>" = some blackBoxHook)
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = 257236) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k)
      publicKeyEqMemSpec := by
  refine subroutine_ok_map (publicKey_eq_ok_at b h_bb hfn hk) ?_
  rintro ⟨p1, pk1, p2, pk2, sp⟩ R s0 hpre
  refine ⟨(p1, pk1, p2, pk2, sp), R, ?_, ?_⟩
  · simpa only [publicKeyEqSpec, publicKeyEqMemSpec,
      ← memRegion_16_eq_stackFrameFor_eq sp,
      ← memRegion_48_eq_stackFrameFor_ct_eq (sp - 16#64)] using hpre
  · intro sf hpost
    simpa only [publicKeyEqSpec, publicKeyEqMemSpec,
      ← memRegion_16_eq_stackFrameFor_eq sp,
      ← memRegion_48_eq_stackFrameFor_ct_eq (sp - 16#64)] using hpost

abbrev eqStack (sp : BitVec 64) : SepProp :=
  memRegion (sp - 272#64) 16 ∗
  memRegion (sp - 320#64) 48

theorem findIdxStack_split (sp : BitVec 64) :
    stackAt sp 1024 =
      memRegion (sp - 1024#64) 704 ∗
      eqStack sp ∗
      memRegion (sp - 256#64) 8 ∗
      memRegion (sp - 248#64) 33 ∗
      memRegion (sp - 215#64) 7 ∗
      cells (sp - 208#64) 4 ∗
      memRegion (sp - 176#64) 80 ∗
      cells (sp - 96#64) 12 := by
  simp only [stackAt, eqStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 1024) (n := 704) (k := 320)
      (b' := sp - 320#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 320#64) (n := 48) (k := 272)
      (b' := sp - 272#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 272#64) (n := 16) (k := 256)
      (b' := sp - 256#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 256#64) (n := 8) (k := 248)
      (b' := sp - 248#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 248#64) (n := 33) (k := 215)
      (b' := sp - 215#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 215#64) (n := 7) (k := 208)
      (b' := sp - 208#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 208#64) (n := 32) (k := 176)
      (b' := sp - 176#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 176#64) (n := 80) (k := 96)
      (b' := sp - 96#64) rfl (by bv_omega) (by decide),
    (memRegion_cells (sp - 208#64) 4 (by decide) :
      memRegion (sp - 208#64) 32 = cells (sp - 208#64) 4),
    (memRegion_cells (sp - 96#64) 12 (by decide) :
      memRegion (sp - 96#64) 96 = cells (sp - 96#64) 12)]
  simp only [sepConj_assoc]
  congr 1
  rw [← sepConj_assoc (memRegion (sp - 320#64) 48) (memRegion (sp - 272#64) 16),
    sepConj_comm (memRegion (sp - 320#64) 48) (memRegion (sp - 272#64) 16),
    sepConj_assoc]

def chainTail (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

def srkRest (g : VecGhost) : SepProp :=
  memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)

theorem chainAt_unfold (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    chainAt A gc a =
      (⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length ∧
        gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗
       (a ↦₆₄ gc.1.srk.cap) ∗
       ((a + 8#64) ↦₆₄ gc.1.srk.ptr) ∗
       ((a + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
       ⌜gc.1.srk.bytes.length ≤ gc.1.srk.cap.toNat ∧ gc.1.srk.cap.toNat < 2 ^ 63 ∧ gc.1.srk.ptr ≠ 0⌝ ∗
       (if gc.1.srk.cap = 0 then emp
        else A.live gc.1.srk.ptr gc.1.srk.cap.toNat 1 ∗ (gc.1.srk.ptr ↦ₛ gc.1.srk.bytes) ∗ srkRest gc.1.srk) ∗
       chainTail A gc a) := by
  simp only [chainAt, vecGhostAt, vecU8At, vecHeader, chainTail, srkRest, sepConj_assoc]

theorem pure_eq_emp {φ : Prop} (h : φ) : (⌜φ⌝ : SepProp) = emp := by
  rw [← sepConj_emp ⌜φ⌝, pure_sepConj_of_true h emp]

def findCodeSpec (b : BitVec 64) (A : RustAlloc) : Spec FindIndexGhost where
  pre := fun (p, cs, theirA, their) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = cs.length ∧ s.readReg64 .x2 = theirA ∧
      cs.length * 104 < 2 ^ 63 ∧ (s.sp &&& 15#64 == 0#64) = true ∧ b &&& 0xfff#64 = 0#64⌝ ∗
    arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ stackAt s.sp 1024
  post := fun (p, cs, theirA, their) s0 sf =>
    ⌜sf.trace = s0.trace ∧
      match (cs.map (·.2)).findIdx? (fun c => c.senderRatchetKey == their) with
      | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
      | none => sf.readReg64 .x0 = 0#64⌝ ∗
    arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ stackAt s0.sp 1024

theorem cells_208_unfold (sp : BitVec 64) :
    cells (sp - 208#64) 4 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 208#64) ↦₆₄ v0) ∗ ((sp - 200#64) ↦₆₄ v1) ∗
        ((sp - 192#64) ↦₆₄ v2) ∗ ((sp - 184#64) ↦₆₄ v3) := by
  cells_unfold

theorem cells_96_unfold (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
      ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11) := by
  cells_unfold

theorem entails_stackAt_1024 (sp : BitVec 64)
    (u0 u1 u2 u3 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    memRegion (sp - 1024#64) 704 ∗
    memRegion (sp - 272#64) 16 ∗
    memRegion (sp - 320#64) 48 ∗
    memRegion (sp - 256#64) 8 ∗
    memRegion (sp - 248#64) 33 ∗
    memRegion (sp - 215#64) 7 ∗
    ((sp - 208#64) ↦₆₄ u0) ∗ ((sp - 200#64) ↦₆₄ u1) ∗
    ((sp - 192#64) ↦₆₄ u2) ∗ ((sp - 184#64) ↦₆₄ u3) ∗
    memRegion (sp - 176#64) 80 ∗
    ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
    ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
    ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
    ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
    ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
    ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11) ⊢
    stackAt sp 1024 := by
  rw [findIdxStack_split sp, cells_208_unfold sp, cells_96_unfold sp]
  simp only [eqStack, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
    (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
    (Entails.sepExists_right v9 (Entails.sepExists_right v10 (Entails.sepExists_right v11
    (Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2
    (Entails.sepExists_right u3 (Entails.refl _))))))))))))))))

theorem SepWP_sepExists {α : Type _} {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : α → SepProp} {post : State → SepProp → Prop}
    (h : ∀ x, SepWP prog target_pc s (P x) post) :
    SepWP prog target_pc s (∃∗ x, P x) post := by
  unfold SepWP
  intro R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hm⟩
  have hx := h x
  unfold SepWP at hx
  exact hx R hm

theorem SepWP_entails_pre {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  exact h R (Satisfies.mono (sepConj_mono_left hent) hm)

theorem SepWP_chainAt_info {A : RustAlloc} {gc : ChainGhost × ReceiverChain} {a : BitVec 64}
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (h :
      (PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length ∧
        gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []) →
      (gc.1.srk.bytes.length ≤ gc.1.srk.cap.toNat ∧ gc.1.srk.cap.toNat < 2 ^ 63 ∧ gc.1.srk.ptr ≠ 0) →
      gc.1.srk.cap ≠ 0 →
      gc.1.srk.bytes.length < 2 ^ 63 →
      SepWP prog target_pc s (chainAt A gc a ∗ P) post) :
    SepWP prog target_pc s (chainAt A gc a ∗ P) post := by
  unfold SepWP
  intro R hm
  have hm' := hm
  rw [chainAt_unfold A gc a] at hm'
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hm'
  rcases hm' with ⟨h1, hm'⟩
  rw [sepConj_pure_left_comm ((a + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length),
    sepConj_pure_left_comm ((a + 8#64) ↦₆₄ gc.1.srk.ptr),
    sepConj_pure_left_comm (a ↦₆₄ gc.1.srk.cap),
    satisfies_pure_sepConj] at hm'
  rcases hm' with ⟨h2, _⟩
  obtain ⟨_, hge33⟩ := publicKey_deserialize_ok_inversion h1.1
  have hlen : gc.1.srk.bytes.length < 2 ^ 63 := by omega
  have hcap : gc.1.srk.cap ≠ 0 := by
    intro hc
    have hc0 : gc.1.srk.cap.toNat = 0 := by rw [hc]; rfl
    omega
  have hx := h h1 h2 hcap hlen
  unfold SepWP at hx
  exact hx R hm

theorem chainAt_eq_of_ok (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64)
    (h1 : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
      gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length ∧
      gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = [])
    (h2 : gc.1.srk.bytes.length ≤ gc.1.srk.cap.toNat ∧ gc.1.srk.cap.toNat < 2 ^ 63 ∧ gc.1.srk.ptr ≠ 0)
    (hcap : gc.1.srk.cap ≠ 0) :
    chainAt A gc a =
      ((a ↦₆₄ gc.1.srk.cap) ∗ ((a + 8#64) ↦₆₄ gc.1.srk.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
        A.live gc.1.srk.ptr gc.1.srk.cap.toNat 1 ∗
        (gc.1.srk.ptr ↦ₛ gc.1.srk.bytes) ∗ srkRest gc.1.srk ∗ chainTail A gc a) := by
  rw [chainAt_unfold A gc a, pure_eq_emp h1, pure_eq_emp h2]
  simp only [hcap, ↓reduceIte, emp_sepConj, sepConj_assoc]

theorem pk_208_eq {sp w0 w1 w2 w3 : BitVec 64} {pk : List (BitVec 8)}
    (hpk : ∀ a : BitVec 64,
      (a ↦ₛ pk) =
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) :
    ((sp - 208#64) ↦ₛ pk) =
      (((sp - 208#64) ↦₆₄ w0) ∗ ((sp - 200#64) ↦₆₄ w1) ∗
        ((sp - 192#64) ↦₆₄ w2) ∗ ((sp - 184#64) ↦₆₄ w3)) := by
  rw [hpk (sp - 208#64)]
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]

theorem pk_247_eq {sp w0 w1 w2 w3 : BitVec 64} {pk : List (BitVec 8)}
    (hpk : ∀ a : BitVec 64,
      (a ↦ₛ pk) =
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) :
    ((sp - 247#64) ↦ₛ pk) =
      (((sp - 247#64) ↦₆₄ w0) ∗ ((sp - 239#64) ↦₆₄ w1) ∗
        ((sp - 231#64) ↦₆₄ w2) ∗ ((sp - 223#64) ↦₆₄ w3)) := by
  rw [hpk (sp - 247#64)]
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]

theorem pk_208_eq_sep {sp w0 w1 w2 w3 : BitVec 64} {pk : List (BitVec 8)} (P : SepProp)
    (hpk : ∀ a : BitVec 64,
      (a ↦ₛ pk) =
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) :
    (((sp - 208#64) ↦₆₄ w0) ∗ ((sp - 200#64) ↦₆₄ w1) ∗
      ((sp - 192#64) ↦₆₄ w2) ∗ ((sp - 184#64) ↦₆₄ w3) ∗ P) =
      (((sp - 208#64) ↦ₛ pk) ∗ P) := by
  rw [pk_208_eq hpk]
  simp only [sepConj_assoc]

theorem pk_247_eq_sep {sp w0 w1 w2 w3 : BitVec 64} {pk : List (BitVec 8)} (P : SepProp)
    (hpk : ∀ a : BitVec 64,
      (a ↦ₛ pk) =
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) :
    (((sp - 247#64) ↦₆₄ w0) ∗ ((sp - 239#64) ↦₆₄ w1) ∗
      ((sp - 231#64) ↦₆₄ w2) ∗ ((sp - 223#64) ↦₆₄ w3) ∗ P) =
      (((sp - 247#64) ↦ₛ pk) ∗ P) := by
  rw [pk_247_eq hpk]
  simp only [sepConj_assoc]

@[local simp, wp_norm, arm64_norm]
theorem ite_1_0_getLsbD_0_eq_true (b : Bool) :
    ((if b = true then 1#64 else 0#64).getLsbD 0 == true) = b := by
  cases b <;> rfl

attribute [local simp, wp_norm, arm64_norm] bv_sub_add_lit

local instance : Std.Associative SepProp.sepConj := ⟨sepConj_assoc⟩
local instance : Std.Commutative SepProp.sepConj := ⟨sepConj_comm⟩

abbrev loopStack (s0 : State) (u0 u1 u2 u3 : BitVec 64) : SepProp :=
  memRegion (s0.sp - 1024#64) 704 ∗
  memRegion (s0.sp - 272#64) 16 ∗
  memRegion (s0.sp - 320#64) 48 ∗
  memRegion (s0.sp - 256#64) 8 ∗
  memRegion (s0.sp - 248#64) 33 ∗
  memRegion (s0.sp - 215#64) 7 ∗
  ((s0.sp - 208#64) ↦₆₄ u0) ∗ ((s0.sp - 200#64) ↦₆₄ u1) ∗
  ((s0.sp - 192#64) ↦₆₄ u2) ∗ ((s0.sp - 184#64) ↦₆₄ u3) ∗
  memRegion (s0.sp - 176#64) 80 ∗
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

theorem loopStack_entails_stackAt (s0 : State) (u0 u1 u2 u3 : BitVec 64) :
    loopStack s0 u0 u1 u2 u3 ⊢ stackAt s0.sp 1024 :=
  entails_stackAt_1024 s0.sp u0 u1 u2 u3
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
    (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 27#5))
    (s0.readReg64 (Reg.gpr 26#5)) (s0.readReg64 (Reg.gpr 25#5))
    (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
    (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
    (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))

theorem after_heq_entails (b : BitVec 64) (A : RustAlloc) (s0 : State)
    (theirA : BitVec 64) (their : PublicKey)
    (gc : ChainGhost × ReceiverChain) (rest : List (ChainGhost × ReceiverChain))
    (cur_p : BitVec 64) (P_pre : SepProp) (w0 w1 w2 w3 : BitVec 64)
    (h1 : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
      gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length ∧
      gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = [])
    (h2 : gc.1.srk.bytes.length ≤ gc.1.srk.cap.toNat ∧ gc.1.srk.cap.toNat < 2 ^ 63 ∧ gc.1.srk.ptr ≠ 0)
    (hcap : gc.1.srk.cap ≠ 0)
    (hpk_cells : ∀ a : BitVec 64,
      (a ↦ₛ gc.2.senderRatchetKey.bytes.toList) =
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) :
    ((s0.sp - 208#64) ↦ₛ gc.2.senderRatchetKey.bytes.toList ∗
      theirA ↦ₛ their.bytes.toList ∗
      memRegion (s0.sp - 272#64) 16 ∗
      memRegion (s0.sp - 320#64) 48 ∗
      gc.1.srk.ptr ↦ₛ gc.1.srk.bytes ∗
      (s0.sp - 248#64) ↦₈ 0#8 ∗
      (s0.sp - 247#64) ↦ₛ gc.2.senderRatchetKey.bytes.toList ∗
      (b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64 ∗
      cur_p ↦₆₄ gc.1.srk.cap ∗
      (cur_p + 8#64) ↦₆₄ gc.1.srk.ptr ∗
      (cur_p + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length ∗
      A.live gc.1.srk.ptr gc.1.srk.cap.toNat 1 ∗
      srkRest gc.1.srk ∗
      chainTail A gc cur_p ∗
      arrayAt (chainAt A) 104 (cur_p + 104#64) rest ∗
      P_pre ∗
      memRegion (s0.sp - 1024#64) 704 ∗
      memRegion (s0.sp - 256#64) 8 ∗
      memRegion (s0.sp - 215#64) 7 ∗
      memRegion (s0.sp - 176#64) 80 ∗
      (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
      (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
      (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
      (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
      (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
      (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
      (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
    (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗
      (theirA ↦ₛ their.bytes.toList) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      loopStack s0 w0 w1 w2 w3) := by
  have heq_rhs :
      (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗
        (theirA ↦ₛ their.bytes.toList) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        loopStack s0 w0 w1 w2 w3) =
      ((s0.sp - 208#64) ↦ₛ gc.2.senderRatchetKey.bytes.toList ∗
        theirA ↦ₛ their.bytes.toList ∗
        memRegion (s0.sp - 272#64) 16 ∗
        memRegion (s0.sp - 320#64) 48 ∗
        gc.1.srk.ptr ↦ₛ gc.1.srk.bytes ∗
        memRegion (s0.sp - 248#64) 33 ∗
        (b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64 ∗
        cur_p ↦₆₄ gc.1.srk.cap ∗
        (cur_p + 8#64) ↦₆₄ gc.1.srk.ptr ∗
        (cur_p + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length ∗
        A.live gc.1.srk.ptr gc.1.srk.cap.toNat 1 ∗
        srkRest gc.1.srk ∗
        chainTail A gc cur_p ∗
        arrayAt (chainAt A) 104 (cur_p + 104#64) rest ∗
        P_pre ∗
        memRegion (s0.sp - 1024#64) 704 ∗
        memRegion (s0.sp - 256#64) 8 ∗
        memRegion (s0.sp - 215#64) 7 ∗
        memRegion (s0.sp - 176#64) 80 ∗
        (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
        (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
        (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
        (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
        (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
        (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
        (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
        (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
        (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
        (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) := by
    dsimp only [arrayAt, loopStack]
    rw [chainAt_eq_of_ok A gc cur_p h1 h2 hcap, pk_208_eq hpk_cells]
    ac_rfl
  rw [heq_rhs]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right ?_))))
  rw [← sepConj_assoc]
  exact sepConj_mono_left (out33_entails_memRegion s0.sp (by simp))

theorem findIdx?_map_cons_pos {gc : ChainGhost × ReceiverChain} {rest : List (ChainGhost × ReceiverChain)}
    {their : PublicKey} (idx : Nat) (h : (gc.2.senderRatchetKey == their) = true) :
    Option.map (· + idx) ((List.map (·.2) (gc :: rest)).findIdx? (fun c => c.senderRatchetKey == their)) =
      some idx := by
  simp [List.findIdx?_cons, h]

theorem findIdx?_map_cons_neg {gc : ChainGhost × ReceiverChain} {rest : List (ChainGhost × ReceiverChain)}
    {their : PublicKey} (idx : Nat) (h : ¬(gc.2.senderRatchetKey == their) = true) :
    Option.map (· + idx) ((List.map (·.2) (gc :: rest)).findIdx? (fun c => c.senderRatchetKey == their)) =
      Option.map (· + (idx + 1)) ((List.map (·.2) rest).findIdx? (fun c => c.senderRatchetKey == their)) := by
  have hf : (gc.2.senderRatchetKey == their) = false := Bool.eq_false_iff.mpr h
  simp only [List.map_cons, List.findIdx?_cons, hf, Bool.false_eq_true, ↓reduceIte, Option.map_map]
  congr 1
  funext k
  simp only [Function.comp_apply]
  omega

theorem add_208_ne_104 (k : Nat) (h : k + 104 + 104 = 104) : False := by
  omega

theorem toNat_ofNat_of_lt {idx : Nat} (h : idx < 2 ^ 64) :
    (BitVec.ofNat 64 idx).toNat = idx := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem list_cons_cons_mul_104_ne_104 {α : Type} (x y : α) (xs : List α)
    (hlen : (x :: y :: xs).length * 104 < 2 ^ 63) :
    (BitVec.ofNat 64 ((x :: y :: xs).length * 104) == 104#64) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hlt64 : (x :: y :: xs).length * 104 < 2 ^ 64 :=
    Nat.lt_trans hlen (by decide)
  have heq : (BitVec.ofNat 64 ((x :: y :: xs).length * 104)).toNat = (104#64).toNat :=
    congrArg BitVec.toNat (beq_iff_eq.mp h)
  rw [toNat_ofNat_of_lt hlt64] at heq
  have h104 : (104#64).toNat = 104 := rfl
  rw [h104] at heq
  simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at heq
  exact add_208_ne_104 (xs.length * 104) heq

theorem list_cons_mul_104_sub_104 {α : Type} (x : α) (xs : List α) :
    BitVec.ofNat 64 ((x :: xs).length * 104) - 104#64 =
      BitVec.ofNat 64 (xs.length * 104) := by
  simp only [List.length_cons, Nat.add_mul, Nat.one_mul, BitVec.ofNat_add]
  bv_omega

theorem idx_lt_two_pow_64_of_cons {α : Type} {idx : Nat} {x : α} {xs : List α}
    (h : idx + (x :: xs).length < 2 ^ 63) :
    idx < 2 ^ 64 := by
  simp only [List.length_cons] at h
  omega

theorem length_lt_cons {α : Type} (y : α) (xs : List α) :
    xs.length < (y :: xs).length :=
  Nat.lt_succ_self xs.length

theorem ofNat_idx_add_one (idx : Nat) :
    BitVec.ofNat 64 idx + 1#64 = BitVec.ofNat 64 (idx + 1) := by
  simp [BitVec.ofNat_add]

theorem add_120_eq_add_104_add_16 (cur_p : BitVec 64) :
    cur_p + 120#64 = cur_p + 104#64 + 16#64 := by
  bv_omega

theorem idx_len_step_of_cons_cons {α : Type} {idx : Nat} {x y : α} {xs : List α}
    (h : idx + (x :: y :: xs).length < 2 ^ 63) :
    idx + 1 + (y :: xs).length < 2 ^ 63 := by
  simp only [List.length_cons] at h ⊢
  omega

theorem len_mul_104_step_of_cons_cons {α : Type} {x y : α} {xs : List α}
    (h : (x :: y :: xs).length * 104 < 2 ^ 63) :
    (y :: xs).length * 104 < 2 ^ 63 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 104 (Nat.le_succ (y :: xs).length)) h

theorem zero_add_len_lt_of_mul_104 {α : Type} {x : α} {xs : List α}
    (h : (x :: xs).length * 104 < 2 ^ 63) :
    0 + (x :: xs).length < 2 ^ 63 := by
  simp only [List.length_cons] at h ⊢
  omega

theorem fnAddr_find_add_136 (b : BitVec 64) (H : String → Option (State → State)) :
    b + 60176#64 =
      (libsignalSessionCode.rebase b H).fnAddr
        "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" + 136#64 := by
  have h : (libsignalSessionCode.rebase b H).fnAddr
      "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" + 136#64 =
      b + 60176#64 := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index"), BitVec.add_assoc]
    rfl
  exact h.symm

theorem arrayAt_cons_sep_pre (A : ChainGhost × ReceiverChain → BitVec 64 → SepProp)
    (gc : ChainGhost × ReceiverChain)
    (rest : List (ChainGhost × ReceiverChain)) (cur_p : BitVec 64) (P_pre Q : SepProp) :
    (arrayAt A 104 cur_p (gc :: rest) ∗ P_pre ∗ Q) =
      (arrayAt A 104 (cur_p + 104#64) rest ∗ (A gc cur_p ∗ P_pre) ∗ Q) := by
  dsimp only [arrayAt]
  ac_rfl

theorem reg_mul_104_eq_ofNat {r : BitVec 64} {n : Nat} (h : r.toNat = n) :
    r * 104#64 = BitVec.ofNat 64 (n * 104) := by
  apply BitVec.eq_of_toNat_eq
  simp [h]

@[elab_as_elim]
theorem list_length_induction {α : Type _} {P : List α → Prop}
    (h : ∀ xs : List α, (∀ ys : List α, ys.length < xs.length → P ys) → P xs)
    (xs : List α) : P xs :=
  WellFounded.induction (measure List.length).wf xs h

set_option maxHeartbeats 1600000 in
theorem find_loop_ok (b : BitVec 64) {H : String → Option (State → State)}
    (A : RustAlloc)
    (h_bb : H "subtle::black_box::<u8>" = some blackBoxHook)
    (s0 : State) (theirA : BitVec 64) (their : PublicKey) (R : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (rest : List (ChainGhost × ReceiverChain))
    (gc : ChainGhost × ReceiverChain)
    (cur_p : BitVec 64) (idx : Nat) (P_pre : SepProp)
    (u0 u1 u2 u3 : BitVec 64) (s : State)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr
      "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = BitVec.ofNat 64 idx)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = theirA)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 1#64)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 ((gc :: rest).length * 104))
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 247#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = cur_p + 16#64)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hidx_len : idx + (gc :: rest).length < 2 ^ 63)
    (hlen_lt : (gc :: rest).length * 104 < 2 ^ 63) :
    SepWP (libsignalSessionCode.rebase b H) (s0.readReg64 .lr) s
      (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗
        (theirA ↦ₛ their.bytes.toList) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        loopStack s0 u0 u1 u2 u3)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            ⌜sf.trace = s0.trace ∧
              match Option.map (· + idx)
                ((List.map (·.2) (gc :: rest)).findIdx? (fun c => c.senderRatchetKey == their)) with
              | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
              | none => sf.readReg64 .x0 = 0#64⌝ ∗
            arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗
            (theirA ↦ₛ their.bytes.toList) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
            stackAt s0.sp 1024 ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hdeser := deserializeMem_ok_at b H (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index") (k := num% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")) rfl
  simp only [deserializeMemSpec] at hdeser
  have heq := publicKeyEqMem_ok_at b h_bb (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index") (k := num% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")) rfl
  simp only [publicKeyEqMemSpec] at heq
  code_fetches libsignalSessionCode libsignalSessionBin b H (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index") (num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")) 284
  generalize (libsignalSessionCode.rebase b H).fnAddr
    "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" = entry at *
  examples_hide_fetches
  induction rest using list_length_induction generalizing gc cur_p idx P_pre u0 u1 u2 u3 s with
  | h rest ih =>
    conv =>
      arg 4
      dsimp only [arrayAt]
      simp only [sepConj_assoc]
    apply SepWP_chainAt_info
    intro h1 h2 hcap hlen
    conv =>
      arg 4
      rw [chainAt_eq_of_ok A gc cur_p h1 h2 hcap]
      simp only [sepConj_assoc]
    wp_steps
    wp_apply
    simp only [hsp, hx19, hx20, hx21, hx22, hx23, hx24, htrace.1, htrace.2] at *
    obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
      exists_unpack64_of_length_32 (bs := gc.2.senderRatchetKey.bytes.toList) (by simp)
    rw [← pk_247_eq_sep _ hpk_cells]
    wp_steps
    rw [pk_247_eq_sep _ hpk_cells, pk_208_eq_sep _ hpk_cells]
    wp_apply
    simp only [hsp_sf, h, h_1, h_2, h_3, h_4, h_5, hvregs, hpost] at *
    refine SepWP_entails_pre
      (after_heq_entails b A s0 theirA their gc rest cur_p P_pre w0 w1 w2 w3 h1 h2 hcap hpk_cells) ?_
    wp_steps
    wp_if hmatch
    · dsimp only [loopStack]
      wp_steps
      rw [findIdx?_map_cons_pos idx (beq_iff_eq.mpr hmatch)]
      have hidx_toNat : (BitVec.ofNat 64 idx).toNat = idx :=
        toNat_ofNat_of_lt (idx_lt_two_pow_64_of_cons hidx_len)
      refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (loopStack_entails_stackAt s0 w0 w1 w2 w3))))) ?_
      wp_done
    · have hmatch_b : ¬(gc.2.senderRatchetKey == their) = true := by
        rw [beq_iff_eq]; exact hmatch
      rw [findIdx?_map_cons_neg idx hmatch_b]
      rcases rest with _ | ⟨gc', rest'⟩
      · simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul] at *
        dsimp only [loopStack]
        wp_steps
        simp only [List.map_nil, List.findIdx?_nil, Option.map_none]
        refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (loopStack_entails_stackAt s0 w0 w1 w2 w3))))) ?_
        wp_done
      · wp_steps
        rw [list_cons_cons_mul_104_ne_104 gc gc' rest' hlen_lt]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [arrayAt_cons_sep_pre (chainAt A) gc (gc' :: rest') cur_p P_pre]
        conv =>
          arg 5; ext sf P_f
          rw [arrayAt_cons_sep_pre (chainAt A) gc (gc' :: rest') cur_p P_pre]
        refine ih rest' (length_lt_cons gc' rest') gc' (cur_p + 104#64) (idx + 1)
          (chainAt A gc cur_p ∗ P_pre) w0 w1 w2 w3 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · exact hrun_sf_1
        · exact hsp_sf_1
        · exact ofNat_idx_add_one idx
        · exact h_11
        · exact h_12
        · exact list_cons_mul_104_sub_104 gc (gc' :: rest')
        · exact h_14
        · exact add_120_eq_add_104_add_16 cur_p
        · exact ⟨hpost_1, hvregs_1⟩
        · exact idx_len_step_of_cons_cons hidx_len
        · exact len_mul_104_step_of_cons_cons hlen_lt
        · rfl

theorem find_loop_ok_zero (b : BitVec 64) {H : String → Option (State → State)}
    (A : RustAlloc)
    (h_bb : H "subtle::black_box::<u8>" = some blackBoxHook)
    (s0 : State) (theirA : BitVec 64) (their : PublicKey) (R : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (rest : List (ChainGhost × ReceiverChain))
    (gc : ChainGhost × ReceiverChain)
    (cur_p : BitVec 64)
    {u0 u1 u2 u3 : BitVec 64} {s : State}
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr
      "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = theirA)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 1#64)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 ((gc :: rest).length * 104))
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 247#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = cur_p + 16#64)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlen_lt : (gc :: rest).length * 104 < 2 ^ 63) :
    SepWP (libsignalSessionCode.rebase b H) (s0.readReg64 .lr) s
      (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗
        (theirA ↦ₛ their.bytes.toList) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        loopStack s0 u0 u1 u2 u3)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            ⌜sf.trace = s0.trace ∧
              match (List.map (·.2) (gc :: rest)).findIdx? (fun c => c.senderRatchetKey == their) with
              | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
              | none => sf.readReg64 .x0 = 0#64⌝ ∗
            arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗
            (theirA ↦ₛ their.bytes.toList) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
            stackAt s0.sp 1024 ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have h := find_loop_ok b A h_bb s0 theirA their R hb hsp0 rest gc cur_p 0 emp u0 u1 u2 u3 s
    hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 htrace
    (zero_add_len_lt_of_mul_104 hlen_lt) hlen_lt
  simpa only [emp_sepConj, Nat.add_zero, Option.map_id'] using h

theorem find_receiver_chain_index_code_ok (b : BitVec 64) {H : String → Option (State → State)}
    (A : RustAlloc)
    (h_bb : H "subtle::black_box::<u8>" = some blackBoxHook) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr
        "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")
      (findCodeSpec b A) := by
  simp only [findCodeSpec]
  code_fetches libsignalSessionCode libsignalSessionBin b H (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index") (num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")) 284
  wp_init g s0
  examples_hide_fetches
  obtain ⟨p, cs, theirA, their⟩ := g
  dsimp only at *
  subst h_1 h_3
  conv =>
    arg 4
    rw [findIdxStack_split s0.sp, cells_208_unfold s0.sp, cells_96_unfold s0.sp]
    simp only [eqStack, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  iterate 16 (apply SepWP_sepExists; intro _)
  wp_steps
  wp_if hcbz
  · wp_steps
    have hcs_nil : cs = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← h_2, hcbz]
      rfl
    subst hcs_nil
    simp only [List.map_nil, List.findIdx?_nil]
    refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (entails_stackAt_1024 s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)))) ?_
    wp_done
  · wp_steps
    rcases cs with _ | ⟨gc, rest⟩
    · exfalso
      apply hcbz
      apply BitVec.eq_of_toNat_eq
      simpa using h_2
    · simp only [sepConj_assoc]
      refine find_loop_ok_zero b A h_bb s0 (s0.readReg64 (Reg.gpr 2#5)) their R h h_5
        rest gc (s0.readReg64 (Reg.gpr 0#5)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact fnAddr_find_add_136 b H
      · exact hrun
      · rfl
      · rfl
      · rfl
      · rfl
      · exact reg_mul_104_eq_ofNat h_2
      · exact sp_sub_248_orr_1 h_5
      · rfl
      · exact ⟨rfl, rfl⟩
      · exact h_4

theorem find_receiver_chain_index_bridge (img : Obj.Image)
    (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) (A : RustAlloc)
    (himg : Obj.Loads libsignalSessionImage img) :
    FindIndexOk img F alloc A := by
  unfold FindIndexOk
  have hprog : sessionProg img F alloc =
      libsignalSessionCode.rebase img.base (Rust.withPanics (sessionExterns F alloc)) :=
    Program.ofImage_eq_rebase rfl himg
  have haddr : (libsignalSessionCode.rebase img.base (Rust.withPanics (sessionExterns F alloc))).fnAddr
      "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" =
      img.base + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index") := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")]
  have hbb : Rust.withPanics (sessionExterns F alloc) "subtle::black_box::<u8>" = some blackBoxHook := by
    simp [Rust.withPanics, Rust.isPanicSymbol, sessionExterns]
  have hcode := find_receiver_chain_index_code_ok img.base A hbb
  rw [hprog, ← haddr]
  refine subroutine_ok_outcome_intro fun ⟨p, cs, theirA, their⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, findIndexSpec, logFilterAddr, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_, ⟨h1, h2, h3, h4⟩, hm⟩
  refine hcode.mono_outcome (p, cs, theirA, their) R s0 hpc hrun ?_ hsp fun _ hout => hout
  simp only [findCodeSpec, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨h1, h2, h3, h4, hsp, ProofLib.ObjectLoad.base_aligned_of_loads himg⟩, hm⟩

/-! ## Stacked 32-Bit `black_box` Variant (`1024 + 16384 = 17408` B) -/

attribute [local irreducible] Program.fnOff blackBoxSpec32

def publicKeyEqMemSpecExt : Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    memRegion (sp - 16#64) 16 ∗ memRegion (sp - 16#64 - 48#64) 48 ∗ stackAt (sp - 64#64) extHookStack32
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    memRegion (sp - 16#64) 16 ∗ memRegion (sp - 16#64 - 48#64) 48 ∗ stackAt (sp - 64#64) extHookStack32

theorem publicKeyEqMem_ok_at_ext32 (b : BitVec 64) {H : String → Option (State → State)}
    (h_bb : HookSat H "subtle::black_box::<u8>" blackBoxSpec32) {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq")) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k) publicKeyEqMemSpecExt := by
  have heq := publicKey_eq_ok_ext32 b h_bb
  rw [Program.fnAddr_rel hfn
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq") hk] at heq
  refine subroutine_ok_map heq ?_
  rintro ⟨p1, pk1, p2, pk2, sp⟩ R s0 hpre
  refine ⟨(p1, pk1, p2, pk2, sp), R, ?_, fun _ hpost => ?_⟩
  · simpa only [publicKeyEqSpecExt, publicKeyEqMemSpecExt,
      ← stackFrameFor_eq_eq_memRegion_ext32 sp,
      ← stackFrameFor_ctEq_eq_memRegion_ext32 (sp - 16#64)] using hpre
  · simpa only [publicKeyEqSpecExt, publicKeyEqMemSpecExt,
      ← stackFrameFor_eq_eq_memRegion_ext32 sp,
      ← stackFrameFor_ctEq_eq_memRegion_ext32 (sp - 16#64)] using hpost

abbrev findIndexStackExt : Nat := 1024 + extHookStack32

abbrev eqStackExt (sp : BitVec 64) : SepProp :=
  memRegion (sp - 272#64) 16 ∗ memRegion (sp - 320#64) 48 ∗ stackAt (sp - 320#64) extHookStack32

theorem findIdxStackExt_split_full (sp : BitVec 64) :
    stackAt sp findIndexStackExt =
      memRegion (sp - BitVec.ofNat 64 findIndexStackExt) 704 ∗ eqStackExt sp ∗
      memRegion (sp - 256#64) 8 ∗ memRegion (sp - 248#64) 33 ∗ memRegion (sp - 215#64) 7 ∗
      cells (sp - 208#64) 4 ∗ memRegion (sp - 176#64) 80 ∗ cells (sp - 96#64) 12 := by
  have htop : stackAt sp findIndexStackExt =
      memRegion (sp - BitVec.ofNat 64 findIndexStackExt) extHookStack32 ∗ stackAt sp 1024 := by
    simp only [stackAt]; exact ProofLib.memRegion_split' (N := findIndexStackExt)
      (b := sp - BitVec.ofNat 64 findIndexStackExt) (n := extHookStack32) (k := 1024)
      (b' := sp - BitVec.ofNat 64 1024) (by decide)
      (by dsimp only [findIndexStackExt, extHookStack32]; bv_omega) (by decide)
  have hmerge : memRegion (sp - BitVec.ofNat 64 findIndexStackExt) extHookStack32 ∗ memRegion (sp - 1024#64) 704 =
      memRegion (sp - BitVec.ofNat 64 findIndexStackExt) 704 ∗ stackAt (sp - 320#64) extHookStack32 := by
    simp only [stackAt]
    rw [← ProofLib.memRegion_split' (N := 704 + extHookStack32) (b := sp - BitVec.ofNat 64 findIndexStackExt)
          (n := extHookStack32) (k := 704) (b' := sp - 1024#64) (by decide)
          (by dsimp only [findIndexStackExt, extHookStack32]; bv_omega) (by decide),
        ProofLib.memRegion_split' (N := 704 + extHookStack32) (b := sp - BitVec.ofNat 64 findIndexStackExt)
          (n := 704) (k := extHookStack32) (b' := (sp - 320#64) - BitVec.ofNat 64 extHookStack32) (by decide)
          (by dsimp only [findIndexStackExt, extHookStack32]; bv_omega) (by decide)]
  rw [htop, findIdxStack_split sp, ← sepConj_assoc, hmerge]; dsimp only [eqStackExt, eqStack]; ac_rfl

abbrev loopStackExt (s0 : State) (u0 u1 u2 u3 : BitVec 64) : SepProp :=
  memRegion (s0.sp - BitVec.ofNat 64 findIndexStackExt) 704 ∗
  memRegion (s0.sp - 272#64) 16 ∗ memRegion (s0.sp - 320#64) 48 ∗ stackAt (s0.sp - 320#64) extHookStack32 ∗
  memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 248#64) 33 ∗ memRegion (s0.sp - 215#64) 7 ∗
  ((s0.sp - 208#64) ↦₆₄ u0) ∗ ((s0.sp - 200#64) ↦₆₄ u1) ∗ ((s0.sp - 192#64) ↦₆₄ u2) ∗ ((s0.sp - 184#64) ↦₆₄ u3) ∗
  memRegion (s0.sp - 176#64) 80 ∗
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

theorem entails_stackAt_findIndexStackExt (sp : BitVec 64)
    (u0 u1 u2 u3 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 findIndexStackExt) 704 ∗
    memRegion (sp - 272#64) 16 ∗ memRegion (sp - 320#64) 48 ∗ stackAt (sp - 320#64) extHookStack32 ∗
    memRegion (sp - 256#64) 8 ∗ memRegion (sp - 248#64) 33 ∗ memRegion (sp - 215#64) 7 ∗
    ((sp - 208#64) ↦₆₄ u0) ∗ ((sp - 200#64) ↦₆₄ u1) ∗ ((sp - 192#64) ↦₆₄ u2) ∗ ((sp - 184#64) ↦₆₄ u3) ∗
    memRegion (sp - 176#64) 80 ∗ ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
    ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗ ((sp - 48#64) ↦₆₄ v6) ∗
    ((sp - 40#64) ↦₆₄ v7) ∗ ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗ ((sp - 16#64) ↦₆₄ v10) ∗
    ((sp - 8#64) ↦₆₄ v11) ⊢ stackAt sp findIndexStackExt := by
  rw [findIdxStackExt_split_full sp, cells_208_unfold sp, cells_96_unfold sp]
  simp only [eqStackExt, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
    (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
    (Entails.sepExists_right v9 (Entails.sepExists_right v10 (Entails.sepExists_right v11
    (Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2
    (Entails.sepExists_right u3 (Entails.refl _))))))))))))))))

theorem loopStackExt_entails_stackAt (s0 : State) (u0 u1 u2 u3 : BitVec 64) :
    loopStackExt s0 u0 u1 u2 u3 ⊢ stackAt s0.sp findIndexStackExt :=
  entails_stackAt_findIndexStackExt s0.sp u0 u1 u2 u3 (s0.readReg64 (Reg.gpr 29#5))
    (s0.readReg64 (Reg.gpr 30#5)) (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 27#5))
    (s0.readReg64 (Reg.gpr 26#5)) (s0.readReg64 (Reg.gpr 25#5)) (s0.readReg64 (Reg.gpr 24#5))
    (s0.readReg64 (Reg.gpr 23#5)) (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
    (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))

theorem after_heq_entails_ext32 (b : BitVec 64) (A : RustAlloc) (s0 : State) (theirA : BitVec 64)
    (their : PublicKey) (gc : ChainGhost × ReceiverChain) (rest : List (ChainGhost × ReceiverChain))
    (cur_p : BitVec 64) (P_pre : SepProp) (w0 w1 w2 w3 : BitVec 64)
    (h1 : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
      gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length ∧
      gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = [])
    (h2 : gc.1.srk.bytes.length ≤ gc.1.srk.cap.toNat ∧ gc.1.srk.cap.toNat < 2 ^ 63 ∧ gc.1.srk.ptr ≠ 0)
    (hcap : gc.1.srk.cap ≠ 0)
    (hpk_cells : ∀ a : BitVec 64, (a ↦ₛ gc.2.senderRatchetKey.bytes.toList) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) :
    ((s0.sp - 208#64) ↦ₛ gc.2.senderRatchetKey.bytes.toList ∗ theirA ↦ₛ their.bytes.toList ∗
      memRegion (s0.sp - 272#64) 16 ∗ memRegion (s0.sp - 320#64) 48 ∗
      stackAt (s0.sp - 320#64) extHookStack32 ∗ gc.1.srk.ptr ↦ₛ gc.1.srk.bytes ∗
      (s0.sp - 248#64) ↦₈ 0#8 ∗ (s0.sp - 247#64) ↦ₛ gc.2.senderRatchetKey.bytes.toList ∗
      (b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64 ∗
      cur_p ↦₆₄ gc.1.srk.cap ∗ (cur_p + 8#64) ↦₆₄ gc.1.srk.ptr ∗
      (cur_p + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length ∗
      A.live gc.1.srk.ptr gc.1.srk.cap.toNat 1 ∗ srkRest gc.1.srk ∗ chainTail A gc cur_p ∗
      arrayAt (chainAt A) 104 (cur_p + 104#64) rest ∗ P_pre ∗
      memRegion (s0.sp - BitVec.ofNat 64 findIndexStackExt) 704 ∗
      memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 215#64) 7 ∗ memRegion (s0.sp - 176#64) 80 ∗
      (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗ (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗ (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗ (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗ (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗ (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
    (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗ (theirA ↦ₛ their.bytes.toList) ∗
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      loopStackExt s0 w0 w1 w2 w3) := by
  have hout : ∀ R : SepProp, (s0.sp - 248#64) ↦₈ 0#8 ∗ ((s0.sp - 247#64) ↦ₛ gc.2.senderRatchetKey.bytes.toList ∗ R) ⊢
      memRegion (s0.sp - 248#64) 33 ∗ R := fun _ => by
    rw [← sepConj_assoc]; exact sepConj_mono_left (out33_entails_memRegion s0.sp (by simp))
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (hout _)))))))
    (Eq.ndrec (motive := (_ ⊢ ·)) (Entails.refl _) (by
      dsimp only [arrayAt, loopStackExt]
      rw [chainAt_eq_of_ok A gc cur_p h1 h2 hcap, pk_208_eq hpk_cells]; ac_rfl))

def findCodeSpecExt (b : BitVec 64) (A : RustAlloc) : Spec FindIndexGhost where
  pre := fun (p, cs, theirA, their) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = cs.length ∧ s.readReg64 .x2 = theirA ∧
      cs.length * 104 < 2 ^ 63 ∧ (s.sp &&& 15#64 == 0#64) = true ∧ b &&& 0xfff#64 = 0#64⌝ ∗
    arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
    stackAt s.sp findIndexStackExt
  post := fun (p, cs, theirA, their) s0 sf =>
    ⌜sf.trace = s0.trace ∧ match (cs.map (·.2)).findIdx? (fun c => c.senderRatchetKey == their) with
      | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
      | none => sf.readReg64 .x0 = 0#64⌝ ∗
    arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
    stackAt s0.sp findIndexStackExt

set_option maxHeartbeats 1600000 in
theorem find_loop_ok_ext32 (b : BitVec 64) {H : String → Option (State → State)} (A : RustAlloc)
    (h_bb : HookSat H "subtle::black_box::<u8>" blackBoxSpec32) (s0 : State) (theirA : BitVec 64)
    (their : PublicKey) (R : SepProp) (hb : b &&& 0xfff#64 = 0#64) (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (rest : List (ChainGhost × ReceiverChain)) (gc : ChainGhost × ReceiverChain) (cur_p : BitVec 64)
    (idx : Nat) (P_pre : SepProp) (u0 u1 u2 u3 : BitVec 64) (s : State)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr
      "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" + 136#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 256#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = BitVec.ofNat 64 idx)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = theirA) (hx21 : s.readReg64 (Reg.gpr 21#5) = 1#64)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 ((gc :: rest).length * 104))
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 247#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = cur_p + 16#64)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hidx_len : idx + (gc :: rest).length < 2 ^ 63) (hlen_lt : (gc :: rest).length * 104 < 2 ^ 63) :
    SepWP (libsignalSessionCode.rebase b H) (s0.readReg64 .lr) s
      (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗ (theirA ↦ₛ their.bytes.toList) ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        loopStackExt s0 u0 u1 u2 u3)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨
        ⌜sf.trace = s0.trace ∧ match Option.map (· + idx)
            ((List.map (·.2) (gc :: rest)).findIdx? (fun c => c.senderRatchetKey == their)) with
          | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
          | none => sf.readReg64 .x0 = 0#64⌝ ∗
        arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗ (theirA ↦ₛ their.bytes.toList) ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        stackAt s0.sp findIndexStackExt ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hdeser := deserializeMem_ok_at b H
    (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")
    (k := num% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")) rfl
  have heq := publicKeyEqMem_ok_at_ext32 b h_bb
    (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")
    (k := num% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")) rfl
  simp only [deserializeMemSpec] at hdeser; simp only [publicKeyEqMemSpecExt] at heq
  code_fetches libsignalSessionCode libsignalSessionBin b H
    (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")
    (num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")) 284
  generalize (libsignalSessionCode.rebase b H).fnAddr
    "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" = entry at *
  examples_hide_fetches
  induction rest using list_length_induction generalizing gc cur_p idx P_pre u0 u1 u2 u3 s with
  | h rest ih =>
    conv => arg 4; dsimp only [arrayAt]; simp only [sepConj_assoc]
    apply SepWP_chainAt_info; intro h1 h2 hcap hlen
    conv => arg 4; rw [chainAt_eq_of_ok A gc cur_p h1 h2 hcap]; simp only [sepConj_assoc]
    wp_steps; wp_apply
    simp only [hsp, hx19, hx20, hx21, hx22, hx23, hx24, htrace.1, htrace.2] at *
    obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
      exists_unpack64_of_length_32 (bs := gc.2.senderRatchetKey.bytes.toList) (by simp)
    rw [← pk_247_eq_sep _ hpk_cells]; wp_steps
    rw [pk_247_eq_sep _ hpk_cells, pk_208_eq_sep _ hpk_cells]; wp_apply
    simp only [hsp_sf, h, h_1, h_2, h_3, h_4, h_5, hvregs, hpost] at *
    refine SepWP_entails_pre
      (after_heq_entails_ext32 b A s0 theirA their gc rest cur_p P_pre w0 w1 w2 w3 h1 h2 hcap hpk_cells) ?_
    wp_steps; wp_if hmatch
    · dsimp only [loopStackExt]; wp_steps; rw [findIdx?_map_cons_pos idx (beq_iff_eq.mpr hmatch)]
      have hidx_toNat : (BitVec.ofNat 64 idx).toNat = idx := toNat_ofNat_of_lt (idx_lt_two_pow_64_of_cons hidx_len)
      refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (loopStackExt_entails_stackAt s0 w0 w1 w2 w3))))) ?_
      wp_done
    · have hmatch_b : ¬(gc.2.senderRatchetKey == their) = true := by rw [beq_iff_eq]; exact hmatch
      rw [findIdx?_map_cons_neg idx hmatch_b]; rcases rest with _ | ⟨gc', rest'⟩
      · simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul] at *
        dsimp only [loopStackExt]; wp_steps; simp only [List.map_nil, List.findIdx?_nil, Option.map_none]
        refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (loopStackExt_entails_stackAt s0 w0 w1 w2 w3))))) ?_
        wp_done
      · wp_steps; rw [list_cons_cons_mul_104_ne_104 gc gc' rest' hlen_lt]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [arrayAt_cons_sep_pre (chainAt A) gc (gc' :: rest') cur_p P_pre]
        conv => arg 5; ext sf P_f; rw [arrayAt_cons_sep_pre (chainAt A) gc (gc' :: rest') cur_p P_pre]
        exact ih rest' (length_lt_cons gc' rest') gc' (cur_p + 104#64) (idx + 1)
          (chainAt A gc cur_p ∗ P_pre) w0 w1 w2 w3 _ hrun_sf_1 hsp_sf_1 (ofNat_idx_add_one idx)
          h_11 h_12 (list_cons_mul_104_sub_104 gc (gc' :: rest')) h_14
          (add_120_eq_add_104_add_16 cur_p) ⟨hpost_1, hvregs_1⟩
          (idx_len_step_of_cons_cons hidx_len) (len_mul_104_step_of_cons_cons hlen_lt) rfl

theorem find_receiver_chain_index_code_ok_ext32 (b : BitVec 64) {H : String → Option (State → State)}
    (A : RustAlloc) (h_bb : HookSat H "subtle::black_box::<u8>" blackBoxSpec32) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr
        "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")
      (findCodeSpecExt b A) := by
  simp only [findCodeSpecExt]
  code_fetches libsignalSessionCode libsignalSessionBin b H
    (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")
    (num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index")) 284
  wp_init g s0; examples_hide_fetches; obtain ⟨p, cs, theirA, their⟩ := g; dsimp only at *; subst h_1 h_3
  conv =>
    arg 4; rw [findIdxStackExt_split_full s0.sp, cells_208_unfold s0.sp, cells_96_unfold s0.sp]
    simp only [eqStackExt, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  iterate 16 (apply SepWP_sepExists; intro _)
  wp_steps; wp_if hcbz
  · wp_steps
    have hcs_nil : cs = [] := List.eq_nil_of_length_eq_zero (by rw [← h_2, hcbz]; rfl)
    subst hcs_nil; simp only [List.map_nil, List.findIdx?_nil]
    refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (entails_stackAt_findIndexStackExt s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)))) ?_
    wp_done
  · wp_steps; rcases cs with _ | ⟨gc, rest⟩
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h_2)) hcbz
    · simp only [sepConj_assoc]
      conv => arg 4; rw [← sepConj_emp (arrayAt (chainAt A) 104 (s0.readReg64 (Reg.gpr 0#5)) (gc :: rest)), sepConj_assoc]
      conv => arg 5; ext sf P_f; rw [← sepConj_emp (arrayAt (chainAt A) 104 (s0.readReg64 (Reg.gpr 0#5)) (gc :: rest)), sepConj_assoc,
        show ((List.map (·.2) (gc :: rest)).findIdx? (fun c => c.senderRatchetKey == their)) =
          Option.map (· + 0) ((List.map (·.2) (gc :: rest)).findIdx? (fun c => c.senderRatchetKey == their)) by simp]
      refine find_loop_ok_ext32 b A h_bb s0 (s0.readReg64 (Reg.gpr 2#5)) their R h h_5
        rest gc (s0.readReg64 (Reg.gpr 0#5)) 0 emp _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact fnAddr_find_add_136 b H
      · assumption
      · rfl
      · rfl
      · rfl
      · rfl
      · exact reg_mul_104_eq_ofNat h_2
      · exact sp_sub_248_orr_1 h_5
      · rfl
      · exact ⟨rfl, rfl⟩
      · exact zero_add_len_lt_of_mul_104 h_4
      · exact h_4

/-! ## Relocatable `[LibsignalPlacement]` Contracts (Block 26) -/

open Arm64.Obj CryptoVerification

def deserializeMemPlacedSpec [LibsignalPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) where
  pre := fun (ptr, bs, pk, sret) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = sret ∧ bs.length < 2 ^ 63 ∧
      PublicKey.deserialize bs = .ok pk⌝ ∗
    (ptr ↦ₛ bs) ∗
    memRegion sret 33 ∗
    (lsLogFilterAddr ↦₆₄ 0#64)
  post := fun (ptr, bs, pk, sret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦ₛ bs) ∗
    (sret ↦₈ 0#8) ∗ ((sret + 1#64) ↦ₛ pk.bytes.toList) ∗
    (lsLogFilterAddr ↦₆₄ 0#64)

theorem deserializeMem_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H) (blkPl_201).base
      deserializeMemPlacedSpec := by
  refine subroutine_ok_map (deserialize_placed_ok H) ?_
  rintro ⟨ptr, bs, pk, sret⟩ R s0 hpre
  simp only [deserializeMemPlacedSpec, memRegion_33_eq] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at hpre
  rcases hpre with ⟨tag0, out32, hpre⟩
  rw [satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlt, hdeser⟩, hpre⟩
  rw [sepConj_pure_left_comm (ptr ↦ₛ bs), satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hout32, hpre⟩
  refine ⟨(ptr, bs, pk, sret, tag0, out32), R, ?_, ?_⟩
  · dsimp only [deserializePlacedSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlt, hdeser, hout32⟩, hpre⟩
  · intro sf hpost
    exact hpost

theorem publicKeyEqMem_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqMemSpec) :=
  publicKey_eq_mem_placed_ok h_bb

theorem after_heq_placed_entails [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (theirA : BitVec 64) (their : PublicKey)
    (gc : ChainGhost × ReceiverChain) (rest : List (ChainGhost × ReceiverChain))
    (cur_p : BitVec 64) (P_pre : SepProp) (w0 w1 w2 w3 : BitVec 64)
    (h1 : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
      gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length ∧
      gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = [])
    (h2 : gc.1.srk.bytes.length ≤ gc.1.srk.cap.toNat ∧ gc.1.srk.cap.toNat < 2 ^ 63 ∧ gc.1.srk.ptr ≠ 0)
    (hcap : gc.1.srk.cap ≠ 0)
    (hpk_cells : ∀ a : BitVec 64,
      (a ↦ₛ gc.2.senderRatchetKey.bytes.toList) =
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) :
    ((s0.sp - 208#64) ↦ₛ gc.2.senderRatchetKey.bytes.toList ∗
      theirA ↦ₛ their.bytes.toList ∗
      memRegion (s0.sp - 272#64) 16 ∗
      memRegion (s0.sp - 320#64) 48 ∗
      gc.1.srk.ptr ↦ₛ gc.1.srk.bytes ∗
      (s0.sp - 248#64) ↦₈ 0#8 ∗
      (s0.sp - 247#64) ↦ₛ gc.2.senderRatchetKey.bytes.toList ∗
      lsLogFilterAddr ↦₆₄ 0#64 ∗
      cur_p ↦₆₄ gc.1.srk.cap ∗
      (cur_p + 8#64) ↦₆₄ gc.1.srk.ptr ∗
      (cur_p + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length ∗
      A.live gc.1.srk.ptr gc.1.srk.cap.toNat 1 ∗
      srkRest gc.1.srk ∗
      chainTail A gc cur_p ∗
      arrayAt (chainAt A) 104 (cur_p + 104#64) rest ∗
      P_pre ∗
      memRegion (s0.sp - 1024#64) 704 ∗
      memRegion (s0.sp - 256#64) 8 ∗
      memRegion (s0.sp - 215#64) 7 ∗
      memRegion (s0.sp - 176#64) 80 ∗
      (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
      (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
      (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
      (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
      (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
      (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
      (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
    (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗
      (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      loopStack s0 w0 w1 w2 w3) := by
  have heq_rhs :
      (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗
        (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        loopStack s0 w0 w1 w2 w3) =
      ((s0.sp - 208#64) ↦ₛ gc.2.senderRatchetKey.bytes.toList ∗
        theirA ↦ₛ their.bytes.toList ∗
        memRegion (s0.sp - 272#64) 16 ∗
        memRegion (s0.sp - 320#64) 48 ∗
        gc.1.srk.ptr ↦ₛ gc.1.srk.bytes ∗
        memRegion (s0.sp - 248#64) 33 ∗
        lsLogFilterAddr ↦₆₄ 0#64 ∗
        cur_p ↦₆₄ gc.1.srk.cap ∗
        (cur_p + 8#64) ↦₆₄ gc.1.srk.ptr ∗
        (cur_p + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length ∗
        A.live gc.1.srk.ptr gc.1.srk.cap.toNat 1 ∗
        srkRest gc.1.srk ∗
        chainTail A gc cur_p ∗
        arrayAt (chainAt A) 104 (cur_p + 104#64) rest ∗
        P_pre ∗
        memRegion (s0.sp - 1024#64) 704 ∗
        memRegion (s0.sp - 256#64) 8 ∗
        memRegion (s0.sp - 215#64) 7 ∗
        memRegion (s0.sp - 176#64) 80 ∗
        (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
        (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
        (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
        (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
        (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
        (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
        (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
        (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
        (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
        (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) := by
    dsimp only [arrayAt, loopStack]
    rw [chainAt_eq_of_ok A gc cur_p h1 h2 hcap, pk_208_eq hpk_cells]
    ac_rfl
  rw [heq_rhs]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right ?_))))
  rw [← sepConj_assoc]
  exact sepConj_mono_left (out33_entails_memRegion s0.sp (by simp))

set_option maxHeartbeats 1600000 in
theorem find_loop_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (A : RustAlloc)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (s0 : State) (theirA : BitVec 64) (their : PublicKey) (R : SepProp)
    (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (rest : List (ChainGhost × ReceiverChain))
    (gc : ChainGhost × ReceiverChain)
    (cur_p : BitVec 64) (idx : Nat) (P_pre : SepProp)
    (u0 u1 u2 u3 : BitVec 64) (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_26).base + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = BitVec.ofNat 64 idx)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = theirA)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 1#64)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 ((gc :: rest).length * 104))
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 247#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = cur_p + 16#64)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hidx_len : idx + (gc :: rest).length < 2 ^ 63)
    (hlen_lt : (gc :: rest).length * 104 < 2 ^ 63) :
    SepWP ((blkPC_26).rebase (blkPl_26).base H) (s0.readReg64 .lr) s
      (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗
        (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        loopStack s0 u0 u1 u2 u3)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            ⌜sf.trace = s0.trace ∧
              match Option.map (· + idx)
                ((List.map (·.2) (gc :: rest)).findIdx? (fun c => c.senderRatchetKey == their)) with
              | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
              | none => sf.readReg64 .x0 = 0#64⌝ ∗
            arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗
            (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt s0.sp 1024 ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hdeser0 : subroutine_ok ((blkPC_201).rebase (blkPl_201).base H) (lsmpl.base 201) deserializeMemPlacedSpec :=
    deserializeMem_placed_ok H
  have hdeser := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_26).rebase (blkPl_26).base H) hdeser0
  simp only [withLsCl, deserializeMemPlacedSpec] at hdeser
  have heq0 : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (lsmpl.base 212)
      (withLsCodeLoaded lsmpl publicKeyEqMemSpec) :=
    publicKeyEqMem_placed_ok h_bb
  have heq := ls_subroutine_ok_cl_of_block
    (callerProg := (blkPC_26).rebase (blkPl_26).base H) heq0
  simp only [withLsCl, publicKeyEqMemSpec] at heq
  induction rest using list_length_induction generalizing gc cur_p idx P_pre u0 u1 u2 u3 s with
  | h rest ih =>
    conv =>
      arg 4
      dsimp only [arrayAt]
      simp only [sepConj_assoc]
    apply SepWP_chainAt_info
    intro h1 h2 hcap hlen
    conv =>
      arg 4
      rw [chainAt_eq_of_ok A gc cur_p h1 h2 hcap]
      simp only [sepConj_assoc]
    wp_steps_lscl (lsmpl.base 201)
    wp_apply
    simp only [hsp, hx19, hx20, hx21, hx22, hx23, hx24, htrace.1, htrace.2] at *
    obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
      exists_unpack64_of_length_32 (bs := gc.2.senderRatchetKey.bytes.toList) (by simp)
    rw [← pk_247_eq_sep _ hpk_cells]
    wp_steps_lscl (lsmpl.base 212)
    rw [pk_247_eq_sep _ hpk_cells, pk_208_eq_sep _ hpk_cells]
    wp_apply
    simp only [hsp_sf, h, h_1, h_2, h_3, h_4, h_5, hvregs, hpost] at *
    refine SepWP_entails_pre
      (after_heq_placed_entails A s0 theirA their gc rest cur_p P_pre w0 w1 w2 w3 h1 h2 hcap hpk_cells) ?_
    wp_steps
    wp_if hmatch
    · dsimp only [loopStack]
      wp_steps
      rw [findIdx?_map_cons_pos idx (beq_iff_eq.mpr hmatch)]
      have hidx_toNat : (BitVec.ofNat 64 idx).toNat = idx :=
        toNat_ofNat_of_lt (idx_lt_two_pow_64_of_cons hidx_len)
      refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (loopStack_entails_stackAt s0 w0 w1 w2 w3))))) ?_
      wp_done
    · have hmatch_b : ¬(gc.2.senderRatchetKey == their) = true := by
        rw [beq_iff_eq]; exact hmatch
      rw [findIdx?_map_cons_neg idx hmatch_b]
      rcases rest with _ | ⟨gc', rest'⟩
      · simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul] at *
        dsimp only [loopStack]
        wp_steps
        simp only [List.map_nil, List.findIdx?_nil, Option.map_none]
        refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (loopStack_entails_stackAt s0 w0 w1 w2 w3))))) ?_
        wp_done
      · wp_steps
        rw [list_cons_cons_mul_104_ne_104 gc gc' rest' hlen_lt]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [arrayAt_cons_sep_pre (chainAt A) gc (gc' :: rest') cur_p P_pre]
        conv =>
          arg 5; ext sf P_f
          rw [arrayAt_cons_sep_pre (chainAt A) gc (gc' :: rest') cur_p P_pre]
        refine ih rest' (length_lt_cons gc' rest') gc' (cur_p + 104#64) (idx + 1)
          (chainAt A gc cur_p ∗ P_pre) w0 w1 w2 w3 _ (by assumption) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · rfl
        · exact hrun_sf_1
        · exact hsp_sf_1
        · exact ofNat_idx_add_one idx
        · exact h_12
        · exact h_13
        · exact list_cons_mul_104_sub_104 gc (gc' :: rest')
        · exact h_15
        · exact add_120_eq_add_104_add_16 cur_p
        · exact ⟨hpost_1, hvregs_1⟩
        · exact idx_len_step_of_cons_cons hidx_len
        · exact len_mul_104_step_of_cons_cons hlen_lt

theorem find_loop_placed_ok_zero [LibsignalPlacement] {H : String → Option (State → State)}
    (A : RustAlloc)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (s0 : State) (theirA : BitVec 64) (their : PublicKey) (R : SepProp)
    (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (rest : List (ChainGhost × ReceiverChain))
    (gc : ChainGhost × ReceiverChain)
    (cur_p : BitVec 64)
    {u0 u1 u2 u3 : BitVec 64} {s : State}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_26).base + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = theirA)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 1#64)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 ((gc :: rest).length * 104))
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 247#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = cur_p + 16#64)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlen_lt : (gc :: rest).length * 104 < 2 ^ 63) :
    SepWP ((blkPC_26).rebase (blkPl_26).base H) (s0.readReg64 .lr) s
      (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗
        (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        loopStack s0 u0 u1 u2 u3)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            ⌜sf.trace = s0.trace ∧
              match (List.map (·.2) (gc :: rest)).findIdx? (fun c => c.senderRatchetKey == their) with
              | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
              | none => sf.readReg64 .x0 = 0#64⌝ ∗
            arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗
            (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt s0.sp 1024 ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have h := find_loop_placed_ok A h_bb s0 theirA their R hsp0 rest gc cur_p 0 emp u0 u1 u2 u3 s
    hcl hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 htrace
    (zero_add_len_lt_of_mul_104 hlen_lt) hlen_lt
  simpa only [emp_sepConj, Nat.add_zero, Option.map_id'] using h

def findPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec FindIndexGhost where
  pre := fun (p, cs, theirA, their) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = cs.length ∧ s.readReg64 .x2 = theirA ∧
      cs.length * 104 < 2 ^ 63 ∧ (s.sp &&& 15#64 == 0#64) = true⌝ ∗
    arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s.sp 1024
  post := fun (p, cs, theirA, their) s0 sf =>
    ⌜sf.trace = s0.trace ∧
      match (cs.map (·.2)).findIdx? (fun c => c.senderRatchetKey == their) with
      | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
      | none => sf.readReg64 .x0 = 0#64⌝ ∗
    arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp 1024

theorem find_receiver_chain_index_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (A : RustAlloc)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_26).rebase (blkPl_26).base H) (blkPl_26).base
      (withLsCodeLoaded lsmpl (findPlacedSpec A)) := by
  simp only [withLsCodeLoaded, findPlacedSpec]
  wp_init g s0
  obtain ⟨p, cs, theirA, their⟩ := g
  dsimp only at *
  subst h_2 h_4
  conv =>
    arg 4
    rw [findIdxStack_split s0.sp, cells_208_unfold s0.sp, cells_96_unfold s0.sp]
    simp only [eqStack, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  iterate 16 (apply SepWP_sepExists; intro _)
  wp_steps_lscl ((blkPl_26).base + 32#64)
  wp_steps
  wp_if hcbz
  · wp_steps
    have hcs_nil : cs = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← h_3, hcbz]
      rfl
    subst hcs_nil
    simp only [List.map_nil, List.findIdx?_nil]
    refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (entails_stackAt_1024 s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)))) ?_
    wp_done
  · wp_steps
    rcases cs with _ | ⟨gc, rest⟩
    · exfalso
      apply hcbz
      apply BitVec.eq_of_toNat_eq
      simpa using h_3
    · simp only [sepConj_assoc]
      refine find_loop_placed_ok_zero A h_bb s0 (s0.readReg64 (Reg.gpr 2#5)) their R h_1
        rest gc (s0.readReg64 (Reg.gpr 0#5)) (by assumption) rfl hrun ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h_5
      · rfl
      · rfl
      · rfl
      · rfl
      · exact reg_mul_104_eq_ofNat h_3
      · exact sp_sub_248_orr_1 h_1
      · rfl
      · exact ⟨rfl, rfl⟩

end CryptoVerification.LibsignalSession.FindReceiverChainIndex
