/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey
public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap
public import LibsignalBinary.Proofs.SignalSession.Cli.PublicSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Specifications.AsmConstants

/-!
# Frame Layout and Struct Decompositions for `get_signed_pre_key::{closure#0}`

Relative callee symbol-offset equations, stack-frame and sub-word decompositions, `vecU8Buf`
borrow/dealloc lemmas, and word-level decompositions of `speAt` (6 words) and
`signedPreKeyStructAt` (11 words).
-/

/-!
# Frame Layout and Struct Decompositions for `get_signed_pre_key::{closure#0}`

Relative callee symbol-offset equations, stack-frame and sub-word decompositions, `vecU8Buf`
borrow/dealloc lemmas, and word-level decompositions of `speAt` (6 words) and
`signedPreKeyStructAt` (11 words).
-/

/-!
# Frame Layout and Struct Decompositions for `get_signed_pre_key::{closure#0}`

Relative callee symbol-offset equations, stack-frame and sub-word decompositions, `vecU8Buf`
borrow/dealloc lemmas, and word-level decompositions of `speAt` (6 words) and
`signedPreKeyStructAt` (11 words).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

/-! ## 1. Relative symbol-offset equations -/

theorem spk_fnAddr_rel {b : BitVec 64} {ext : String → Option (State → State)}
    {target : String} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff spkGetPollName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target)) :
    (tripleRatchetProgAtExt b ext).fnAddr spkGetPollName + off =
      (tripleRatchetProgAtExt b ext).fnAddr target := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, BitVec.add_assoc, h]

abbrev decimalRelOff : BitVec 64 :=
  bv% ((2 ^ 64 + ls_off% "libsignal_cli::stores::decimal" -
    ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") % 2 ^ 64)

abbrev dirGetRelOff : BitVec 64 :=
  bv% ((2 ^ 64 + ls_off% "<libsignal_cli::stores::Dir>::get" -
    ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") % 2 ^ 64)

abbrev decodeSpkRelOff : BitVec 64 :=
  bv% ((2 ^ 64 + ls_off% "libsignal_cli::stores::decode_kyber_pre_key" -
    ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") % 2 ^ 64)

abbrev dropSpeRelOff : BitVec 64 :=
  bv% ((2 ^ 64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]" -
    ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") % 2 ^ 64)

abbrev deallocRelOff : BitVec 64 :=
  bv% ((2 ^ 64 + ls_off% "__rustc::__rust_dealloc" -
    ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") % 2 ^ 64)

theorem decimal_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr decimalName =
      (tripleRatchetProgAtExt b ext).fnAddr spkGetPollName + decimalRelOff :=
  (spk_fnAddr_rel (by rw [spkGetPoll_fnOff, decimal_fnOff]; decide)).symm

theorem dirGet_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr dirGetName =
      (tripleRatchetProgAtExt b ext).fnAddr spkGetPollName + dirGetRelOff :=
  (spk_fnAddr_rel (by rw [spkGetPoll_fnOff, dirGet_fnOff]; decide)).symm

theorem decodeSpk_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr decodeKyberPreKeyName =
      (tripleRatchetProgAtExt b ext).fnAddr spkGetPollName + decodeSpkRelOff :=
  (spk_fnAddr_rel (by rw [spkGetPoll_fnOff, decodeKyberPreKey_fnOff]; decide)).symm

theorem cliDropSpe_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr cliDropSpeName =
      (tripleRatchetProgAtExt b ext).fnAddr spkGetPollName + dropSpeRelOff :=
  (spk_fnAddr_rel (by rw [spkGetPoll_fnOff, cliDropSpe_fnOff]; decide)).symm

theorem dealloc_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr deallocName =
      (tripleRatchetProgAtExt b ext).fnAddr spkGetPollName + deallocRelOff :=
  (spk_fnAddr_rel (by rw [spkGetPoll_fnOff, ls_stub% "__rustc::__rust_dealloc"]; decide)).symm

/-! ## 2. Stack and sub-word region decompositions -/

theorem memRegion_bound_of_pointsTo64 {m : Memory} {b a v : BitVec 64} {n : Nat} {R : SepProp}
    (h : m ⊨ memRegion b n ∗ ((a ↦₆₄ v) ∗ R)) : n ≤ 2 ^ 64 := by
  by_cases hn0 : n = 0
  · omega
  · have hd := disjointRegions_of_coversRegion (Nat.pos_of_ne_zero hn0) (by decide)
      (IsBlock.memRegion b n).covers (IsBlock.pointsTo64 a v).covers h
    have h1 := hd.1
    omega

theorem stackAt_sub_split (sp : BitVec 64) {subStk topStk : Nat}
    (hle : subStk ≤ topStk) (hhi : topStk ≤ 2 ^ 64) :
    stackAt sp topStk =
      memRegion (sp - BitVec.ofNat 64 topStk) (topStk - subStk) ∗ stackAt sp subStk := by
  have heq : topStk = subStk + (topStk - subStk) := by omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom sp subStk (topStk - subStk) (by omega), ← heq]

theorem stackAt_spkPoll_frame (sp : BitVec 64) {calleeStk : Nat}
    (hhi : calleeStk + 384 ≤ 2 ^ 64) :
    stackAt sp (calleeStk + 384) =
      stackAt (sp - 384#64) calleeStk ∗ cells (sp - 384#64) 48 :=
  ProofLib.stackAt_split_cells sp calleeStk 48 hhi

theorem memRegion_16_cells (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, (a ↦₆₄ v1) ∗ ((a + 8#64) ↦₆₄ v0)) := by
  rw [show (16 : Nat) = 8 + 8 by rfl, memRegion_split a 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + 16 by rfl, memRegion_split a 8 16 (by decide),
    ProofLib.memRegion_eight, memRegion_16_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_32_cells (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        (a ↦₆₄ v3) ∗ ((a + 8#64) ↦₆₄ v2) ∗ ((a + 16#64) ↦₆₄ v1) ∗ ((a + 24#64) ↦₆₄ v0)) := by
  rw [show (32 : Nat) = 8 + 24 by rfl, memRegion_split a 8 24 (by decide),
    ProofLib.memRegion_eight, memRegion_24_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_40_cells (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64,
        (a ↦₆₄ v4) ∗ ((a + 8#64) ↦₆₄ v3) ∗ ((a + 16#64) ↦₆₄ v2) ∗
        ((a + 24#64) ↦₆₄ v1) ∗ ((a + 32#64) ↦₆₄ v0)) := by
  rw [show (40 : Nat) = 8 + 32 by rfl, memRegion_split a 8 32 (by decide),
    ProofLib.memRegion_eight, memRegion_32_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

def words6At (a : BitVec 64) (u0 u1 u2 u3 u4 u5 : BitVec 64) : SepProp :=
  (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
  ((a + 24#64) ↦₆₄ u3) ∗ ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u5)

def words11At (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
  ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
  ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
  ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10)

theorem memRegion_48_cells (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
       ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        words6At a u5 u4 u3 u2 u1 u0) := by
  dsimp only [words6At]
  rw [show (48 : Nat) = 8 + 40 by rfl, memRegion_split a 8 40 (by decide),
    ProofLib.memRegion_eight, memRegion_40_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_88_cells (a : BitVec 64) :
    memRegion a 88 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
       ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64,
        words11At a w10 w9 w8 w7 w6 w5 w4 w3 w2 w1 w0) := by
  dsimp only [words11At, words6At]
  rw [show (88 : Nat) = 48 + 40 by rfl, memRegion_split a 48 40 (by decide),
    memRegion_48_cells, memRegion_40_cells]
  dsimp only [words6At]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]

theorem pointsTo64_eq_pair32 (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) = (a ↦₃₂ w.extractLsb' 0 32) ∗ ((a + 4#64) ↦₃₂ w.extractLsb' 32 32) := by
  have hsplit : unpack64 w = unpack32 (w.extractLsb' 0 32) ++ unpack32 (w.extractLsb' 32 32) := by
    simp only [unpack64, unpack32, List.cons_append, List.nil_append, List.cons.injEq, and_true]
    exact ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits,
           by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩
  rw [pointsTo64_eq_pointsToBytes, hsplit, pointsToBytes_append,
    ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
  rfl

private theorem pointsTo8_eq_bytes1 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem pointsTo64_eq_8_8_16_32 (a : BitVec 64) (u : BitVec 64) :
    (a ↦₆₄ u) =
      (a ↦₈ u.extractLsb' 0 8) ∗
      ((a + 1#64) ↦₈ u.extractLsb' 8 8) ∗
      ((a + 2#64) ↦₁₆ u.extractLsb' 16 16) ∗
      ((a + 4#64) ↦₃₂ u.extractLsb' 32 32) := by
  have hsplit :
      unpack64 u =
        [u.extractLsb' 0 8] ++ ([u.extractLsb' 8 8] ++
          (unpack16 (u.extractLsb' 16 16) ++ unpack32 (u.extractLsb' 32 32))) := by
    simp only [unpack64, unpack16, unpack32, List.cons_append, List.nil_append,
      List.cons.injEq, and_true]
    exact ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits,
           by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩
  rw [pointsTo64_eq_pointsToBytes, hsplit,
    pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
    ← pointsTo8_eq_bytes1, ← pointsTo8_eq_bytes1,
    ← pointsTo16_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
  simp only [List.length_singleton, unpack16_length, BitVec.add_assoc, BitVec.reduceAdd]

theorem byte_pad7_unpack (a : BitVec 64) (v : BitVec 8) :
    ((a ↦₈ v) ∗ memRegion (a + 1#64) 7) ⊢
      ∃∗ u : BitVec 64, ⌜u.extractLsb' 0 8 = v⌝ ∗ (a ↦₆₄ u) := by
  have ha2 : a + 1#64 + 1#64 = a + 2#64 := by bv_omega
  have ha4 : a + 2#64 + 2#64 = a + 4#64 := by bv_omega
  rw [show (7 : Nat) = 1 + 6 by rfl, memRegion_split (a + 1#64) 1 6 (by decide), ha2,
    show (6 : Nat) = 2 + 4 by rfl, memRegion_split (a + 2#64) 2 4 (by decide), ha4,
    ProofLib.memRegion_one, ProofLib.memRegion_two, ProofLib.memRegion_four]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w4 => Entails.sepExists_elim fun w2 =>
    Entails.sepExists_elim fun w1 => ?_
  refine Entails.sepExists_right (w4 ++ (w2 ++ (w1 ++ v))) ?_
  have h0 : (w4 ++ (w2 ++ (w1 ++ v))).extractLsb' 0 8 = v := by bv_bits
  have h1 : (w4 ++ (w2 ++ (w1 ++ v))).extractLsb' 8 8 = w1 := by bv_bits
  have h2 : (w4 ++ (w2 ++ (w1 ++ v))).extractLsb' 16 16 = w2 := by bv_bits
  have h4 : (w4 ++ (w2 ++ (w1 ++ v))).extractLsb' 32 32 = w4 := by bv_bits
  refine Entails.pure_right h0 ?_
  rw [pointsTo64_eq_8_8_16_32 a (w4 ++ (w2 ++ (w1 ++ v))), h0, h1, h2, h4]
  exact Entails.of_eq (by ac_rfl)

theorem byte_pad7_pack (a : BitVec 64) (u : BitVec 64) (v : BitVec 8)
    (hv : u.extractLsb' 0 8 = v) :
    (a ↦₆₄ u) ⊢ (a ↦₈ v) ∗ memRegion (a + 1#64) 7 := by
  have ha2 : a + 1#64 + 1#64 = a + 2#64 := by bv_omega
  have ha4 : a + 2#64 + 2#64 = a + 4#64 := by bv_omega
  rw [pointsTo64_eq_8_8_16_32 a u, hv,
    show (7 : Nat) = 1 + 6 by rfl, memRegion_split (a + 1#64) 1 6 (by decide), ha2,
    show (6 : Nat) = 2 + 4 by rfl, memRegion_split (a + 2#64) 2 4 (by decide), ha4,
    ProofLib.memRegion_one, ProofLib.memRegion_two, ProofLib.memRegion_four]
  refine sepConj_mono_right (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
      (Entails.sepExists_right _ (Entails.refl _))))

/-! ## 3. `vecU8Buf` borrow/dealloc algebra -/

def vecU8BufRest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8Buf_eq_bytes_sep_rest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    SpqrV1.Alloc.vecU8Buf A cap ptr bs =
      SpqrV1.ChainProofs.bytesAt false ptr bs ∗ vecU8BufRest A cap ptr bs := by
  dsimp only [SpqrV1.Alloc.vecU8Buf, vecU8BufRest, SpqrV1.ChainProofs.bytesAt]
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases hcap : cap = 0
  · subst hcap
    simp only [↓reduceIte, sepConj_emp]
    by_cases hbs : bs = []
    · subst hbs
      rw [pointsToBytes_nil, emp_sepConj]
    · have hfalse : (bs.length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0) = False := by
        have hpos : 0 < bs.length := List.length_pos_iff_ne_nil.mpr hbs
        have hz : (0 : BitVec 64).toNat = 0 := rfl
        exact eq_false (fun h => by omega)
      rw [hfalse, sepConj_comm, pure_false_sepConj]
  · simp only [hcap, ↓reduceIte]
    ac_rfl

theorem vecU8Buf_zero_elim (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    SpqrV1.Alloc.vecU8Buf A 0#64 ptr bs ⊢ emp := by
  dsimp only [SpqrV1.Alloc.vecU8Buf]
  have hz : (0#64 : BitVec 64) = 0 := rfl
  simp only [hz, ↓reduceIte, sepConj_emp]
  rw [← sepConj_emp ⌜_⌝]
  exact Entails.pure_left fun _ => Entails.refl emp

theorem vecU8Buf_ne_zero_dealloc (A : RustAlloc) {cap ptr : BitVec 64} (bs : List (BitVec 8))
    (hcap : cap ≠ 0#64) :
    SpqrV1.Alloc.vecU8Buf A cap ptr bs ⊢
      ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  dsimp only [SpqrV1.Alloc.vecU8Buf]
  have hne : (cap = 0) = False := eq_false hcap
  simp only [hne, ↓reduceIte]
  refine Entails.pure_left fun ⟨hle, hlt, _⟩ => ?_
  have hpos : 0 < cap.toNat := by
    by_contra hz
    have hc0 : cap.toNat = 0 := by omega
    exact hcap (BitVec.eq_of_toNat_eq hc0)
  have hlay : LayoutOk cap.toNat 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  refine Entails.pure_right hlay ?_
  have hreg : ((ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢
      memRegion ptr cap.toNat := by
    rw [memRegion_split_le ptr bs.length cap.toNat hle (by omega)]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)
  exact sepConj_mono_right hreg

/-! ## 4. Detached-heap decompositions of `speAt` (6 words) and `signedPreKeyStructAt` (11 words) -/

def invalidMsgBytesOk : InvalidMessageReason → List (BitVec 8) → Prop
  | .tooFarInFuture, bs => bs = tooFarInFutureStr
  | .macFailed, bs => bs = macFailedStr
  | .pqRatchet, _ => True
  | .badCiphertext, _ => True
  | .decryptionFailed, _ => False

def speDetached (A : RustAlloc) (fnName : List (BitVec 8))
    (u0 u1 u2 u3 u4 u5 : BitVec 64) : SignalProtocolError → SepProp
  | .invalidState =>
    ∃∗ bs : List (BitVec 8),
      ⌜u0 = speWord 1 ∧ u3 = BitVec.ofNat 64 bs.length ∧
        u5 = BitVec.ofNat 64 fnName.length⌝ ∗
      SpqrV1.Alloc.vecU8Buf A u1 u2 bs ∗ (u4 ↦ᵣ fnName)
  | .ciphertextMessageTooShort n =>
    ⌜u0 = speWord 3 ∧ u1 = BitVec.ofNat 64 n⌝
  | .legacyCiphertextVersion v =>
    ⌜u0 = speWord 4 ∧ u1.extractLsb' 0 8 = v⌝
  | .unrecognizedCiphertextVersion v =>
    ⌜u0 = speWord 5 ∧ u1.extractLsb' 0 8 = v⌝
  | .invalidProtobufEncoding =>
    ⌜u0 = speWord 2⌝
  | .noKeyTypeIdentifier =>
    ⌜u0 = speWord 7⌝
  | .badKeyType t =>
    ⌜u0 = speWord 8 ∧ u1.extractLsb' 0 8 = t⌝
  | .badKeyLength n =>
    ⌜u0 = speWord 9 ∧ u1 = BitVec.ofNat 64 n⌝
  | .invalidKeyAgreement =>
    ⌜u0 = speWord 10⌝
  | .invalidSessionStructure r =>
    ⌜u0 = speWord 20 ∧ u2 = BitVec.ofNat 64 (invalidSessionStructureStr r).length⌝ ∗ (u1 ↦ᵣ invalidSessionStructureStr r)
  | .duplicatedMessage i c =>
    ⌜u0 = speWord 23 ∧ u1.extractLsb' 0 32 = i ∧ u1.extractLsb' 32 32 = c⌝
  | .invalidMessage t r =>
    ∃∗ bs : List (BitVec 8),
      ⌜u0 = speWord 24 ∧ invalidMsgBytesOk r bs ∧
        u3 = BitVec.ofNat 64 bs.length ∧ u4.extractLsb' 0 8 = msgTypeByte t⌝ ∗
      SpqrV1.Alloc.vecU8Buf A u1 u2 bs
  | .panic => ⌜False⌝

private theorem vecU8_unpack3 (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ c : BitVec 64, ∃∗ p : BitVec 64,
        (a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        SpqrV1.Alloc.vecU8Buf A c p bs := by
  dsimp only [vecU8]
  refine Entails.sepExists_elim fun c => Entails.sepExists_elim fun p => ?_
  refine Entails.sepExists_right c (Entails.sepExists_right p ?_)
  rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
  dsimp only [vecHeader]
  exact Entails.of_eq (by ac_rfl)

private theorem vecU8_pack3 (A : RustAlloc) (a c p : BitVec 64) (bs : List (BitVec 8)) :
    ((a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      SpqrV1.Alloc.vecU8Buf A c p bs) ⊢ vecU8 A a bs := by
  dsimp only [vecU8]
  refine Entails.sepExists_right c (Entails.sepExists_right p ?_)
  rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
  dsimp only [vecHeader]
  exact Entails.of_eq (by ac_rfl)

private theorem invalidMsgStr_unpack (A : RustAlloc) (a : BitVec 64) (r : InvalidMessageReason) :
    invalidMessageStrAt A a r ⊢
      ∃∗ bs : List (BitVec 8), ⌜invalidMsgBytesOk r bs⌝ ∗ vecU8 A a bs := by
  cases r with
  | tooFarInFuture =>
    exact Entails.sepExists_right tooFarInFutureStr (Entails.pure_right rfl (Entails.refl _))
  | macFailed =>
    exact Entails.sepExists_right macFailedStr (Entails.pure_right rfl (Entails.refl _))
  | pqRatchet =>
    exact Entails.sepExists_elim fun bs =>
      Entails.sepExists_right bs (Entails.pure_right trivial (Entails.refl _))
  | badCiphertext =>
    exact Entails.sepExists_elim fun bs =>
      Entails.sepExists_right bs (Entails.pure_right trivial (Entails.refl _))
  | decryptionFailed =>
    dsimp only [invalidMessageStrAt]
    rw [← sepConj_emp ⌜False⌝]
    exact Entails.pure_left fun hf => False.elim hf

private theorem invalidMsgStr_pack (A : RustAlloc) (a : BitVec 64) (r : InvalidMessageReason)
    (bs : List (BitVec 8)) (hok : invalidMsgBytesOk r bs) :
    vecU8 A a bs ⊢ invalidMessageStrAt A a r := by
  cases r with
  | tooFarInFuture => subst hok; exact Entails.refl _
  | macFailed => subst hok; exact Entails.refl _
  | pqRatchet => exact Entails.sepExists_right bs (Entails.refl _)
  | badCiphertext => exact Entails.sepExists_right bs (Entails.refl _)
  | decryptionFailed => exact False.elim hok

private theorem byte_pad39_unpack (a : BitVec 64) (v : BitVec 8) :
    (((a + 8#64) ↦₈ v) ∗ memRegion (a + 9#64) 39) ⊢
      ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
      ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        ⌜u1.extractLsb' 0 8 = v⌝ ∗
        ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) ∗
        ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u5) := by
  have ha9 : (a + 8#64) + 1#64 = a + 9#64 := by bv_omega
  have ha16 : a + 9#64 + 7#64 = a + 16#64 := by bv_omega
  rw [show (39 : Nat) = 7 + 32 by rfl, memRegion_split (a + 9#64) 7 32 (by decide), ha16,
    ← ha9, memRegion_32_cells (a + 16#64), ← sepConj_assoc]
  refine Entails.trans (sepConj_mono_left (byte_pad7_unpack (a + 8#64) v)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  refine Entails.sepExists_elim fun u5 => Entails.sepExists_elim fun u4 =>
    Entails.sepExists_elim fun u3 => Entails.sepExists_elim fun u2 =>
    Entails.sepExists_elim fun u1 => ?_
  exact Entails.sepExists_right u1 (Entails.sepExists_right u2 (Entails.sepExists_right u3
    (Entails.sepExists_right u4 (Entails.sepExists_right u5 (Entails.of_eq (by ac_rfl))))))

private theorem byte_pad39_pack (a u1 u2 u3 u4 u5 : BitVec 64) (v : BitVec 8)
    (hv : u1.extractLsb' 0 8 = v) :
    (((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) ∗
      ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u5)) ⊢
      ((a + 8#64) ↦₈ v) ∗ memRegion (a + 9#64) 39 := by
  have ha9 : (a + 8#64) + 1#64 = a + 9#64 := by bv_omega
  have ha16 : a + 9#64 + 7#64 = a + 16#64 := by bv_omega
  rw [show (39 : Nat) = 7 + 32 by rfl, memRegion_split (a + 9#64) 7 32 (by decide), ha16,
    ← ha9, memRegion_32_cells (a + 16#64)]
  refine Entails.trans (sepConj_mono_left (byte_pad7_pack (a + 8#64) u1 v hv)) ?_
  rw [sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  exact Entails.sepExists_right u5 (Entails.sepExists_right u4 (Entails.sepExists_right u3
    (Entails.sepExists_right u2
      (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd])))))

theorem speAt_unpack (A : RustAlloc) (fnName : List (BitVec 8)) (a : BitVec 64)
    (e : SignalProtocolError) :
    speAt A fnName a e ⊢
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        words6At a u0 u1 u2 u3 u4 u5 ∗ speDetached A fnName u0 u1 u2 u3 u4 u5 e := by
  cases e with
  | invalidState =>
    dsimp only [speAt, speDetached, strRefAt, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have h32 : asm64% speInvalidStateFnOff = 32#64 := rfl
    have hb8 : asm64% boxSliceLenOff = 8#64 := rfl
    rw [h8, h32, hb8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun p => Entails.sepExists_elim fun bs => ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left (vecU8_unpack3 A (a + 8#64) bs))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_elim fun c => Entails.sepExists_elim fun bp => ?_
    refine Entails.sepExists_right (speWord 1) (Entails.sepExists_right c
      (Entails.sepExists_right bp (Entails.sepExists_right (BitVec.ofNat 64 bs.length)
      (Entails.sepExists_right p (Entails.sepExists_right (BitVec.ofNat 64 fnName.length) ?_)))))
    refine Entails.sepExists_right bs ?_
    rw [show (speWord 1 = speWord 1 ∧ BitVec.ofNat 64 bs.length = BitVec.ofNat 64 bs.length ∧
      BitVec.ofNat 64 fnName.length = BitVec.ofNat 64 fnName.length) = True from
      eq_true ⟨rfl, rfl, rfl⟩, pure_true, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  | ciphertextMessageTooShort n =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have h16 : asm64% (spePayloadOff + 8) = 16#64 := rfl
    have hs : asm% (speSize - (spePayloadOff + 8)) = 32 := rfl
    rw [h8, h16, hs, memRegion_32_cells (a + 16#64)]
    simp only [sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_elim fun u5 => Entails.sepExists_elim fun u4 =>
      Entails.sepExists_elim fun u3 => Entails.sepExists_elim fun u2 => ?_
    refine Entails.sepExists_right (speWord 3) (Entails.sepExists_right (BitVec.ofNat 64 n)
      (Entails.sepExists_right u2 (Entails.sepExists_right u3
      (Entails.sepExists_right u4 (Entails.sepExists_right u5 ?_)))))
    rw [show (speWord 3 = speWord 3 ∧ BitVec.ofNat 64 n = BitVec.ofNat 64 n) = True from
      eq_true ⟨rfl, rfl⟩, pure_true, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  | legacyCiphertextVersion v =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have h9 : asm64% (spePayloadOff + 1) = 9#64 := rfl
    have hs : asm% (speSize - (spePayloadOff + 1)) = 39 := rfl
    rw [h8, h9, hs]
    refine Entails.trans (sepConj_mono_right (byte_pad39_unpack a v)) ?_
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun u1 => Entails.sepExists_elim fun u2 =>
      Entails.sepExists_elim fun u3 => Entails.sepExists_elim fun u4 =>
      Entails.sepExists_elim fun u5 => ?_
    rw [sepConj_comm (a ↦₆₄ speWord 4)]
    simp only [sepConj_assoc]
    refine Entails.pure_left fun hv => ?_
    refine Entails.sepExists_right (speWord 4) (Entails.sepExists_right u1
      (Entails.sepExists_right u2 (Entails.sepExists_right u3
      (Entails.sepExists_right u4 (Entails.sepExists_right u5 ?_)))))
    rw [show (speWord 4 = speWord 4 ∧ u1.extractLsb' 0 8 = v) = True from eq_true ⟨rfl, hv⟩,
      pure_true, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  | unrecognizedCiphertextVersion v =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have h9 : asm64% (spePayloadOff + 1) = 9#64 := rfl
    have hs : asm% (speSize - (spePayloadOff + 1)) = 39 := rfl
    rw [h8, h9, hs]
    refine Entails.trans (sepConj_mono_right (byte_pad39_unpack a v)) ?_
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun u1 => Entails.sepExists_elim fun u2 =>
      Entails.sepExists_elim fun u3 => Entails.sepExists_elim fun u4 =>
      Entails.sepExists_elim fun u5 => ?_
    rw [sepConj_comm (a ↦₆₄ speWord 5)]
    simp only [sepConj_assoc]
    refine Entails.pure_left fun hv => ?_
    refine Entails.sepExists_right (speWord 5) (Entails.sepExists_right u1
      (Entails.sepExists_right u2 (Entails.sepExists_right u3
      (Entails.sepExists_right u4 (Entails.sepExists_right u5 ?_)))))
    rw [show (speWord 5 = speWord 5 ∧ u1.extractLsb' 0 8 = v) = True from eq_true ⟨rfl, hv⟩,
      pure_true, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  | invalidProtobufEncoding =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have hs : asm% (speSize - spePayloadOff) = 40 := rfl
    rw [h8, hs, memRegion_40_cells (a + 8#64)]
    simp only [sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_elim fun u5 => Entails.sepExists_elim fun u4 =>
      Entails.sepExists_elim fun u3 => Entails.sepExists_elim fun u2 =>
      Entails.sepExists_elim fun u1 => ?_
    refine Entails.sepExists_right (speWord 2) (Entails.sepExists_right u1
      (Entails.sepExists_right u2 (Entails.sepExists_right u3
      (Entails.sepExists_right u4 (Entails.sepExists_right u5 ?_)))))
    rw [show (speWord 2 = speWord 2) = True from eq_true rfl, pure_true, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  | noKeyTypeIdentifier =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have hs : asm% (speSize - spePayloadOff) = 40 := rfl
    rw [h8, hs, memRegion_40_cells (a + 8#64)]
    simp only [sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_elim fun u5 => Entails.sepExists_elim fun u4 =>
      Entails.sepExists_elim fun u3 => Entails.sepExists_elim fun u2 =>
      Entails.sepExists_elim fun u1 => ?_
    refine Entails.sepExists_right (speWord 7) (Entails.sepExists_right u1
      (Entails.sepExists_right u2 (Entails.sepExists_right u3
      (Entails.sepExists_right u4 (Entails.sepExists_right u5 ?_)))))
    rw [show (speWord 7 = speWord 7) = True from eq_true rfl, pure_true, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  | badKeyType t =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have h9 : asm64% (spePayloadOff + 1) = 9#64 := rfl
    have hs : asm% (speSize - (spePayloadOff + 1)) = 39 := rfl
    rw [h8, h9, hs]
    refine Entails.trans (sepConj_mono_right (byte_pad39_unpack a t)) ?_
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun u1 => Entails.sepExists_elim fun u2 =>
      Entails.sepExists_elim fun u3 => Entails.sepExists_elim fun u4 =>
      Entails.sepExists_elim fun u5 => ?_
    rw [sepConj_comm (a ↦₆₄ speWord 8)]
    simp only [sepConj_assoc]
    refine Entails.pure_left fun hv => ?_
    refine Entails.sepExists_right (speWord 8) (Entails.sepExists_right u1
      (Entails.sepExists_right u2 (Entails.sepExists_right u3
      (Entails.sepExists_right u4 (Entails.sepExists_right u5 ?_)))))
    rw [show (speWord 8 = speWord 8 ∧ u1.extractLsb' 0 8 = t) = True from eq_true ⟨rfl, hv⟩,
      pure_true, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  | badKeyLength n =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have h16 : asm64% (spePayloadOff + 8) = 16#64 := rfl
    have hs : asm% (speSize - (spePayloadOff + 8)) = 32 := rfl
    rw [h8, h16, hs, memRegion_32_cells (a + 16#64)]
    simp only [sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_elim fun u5 => Entails.sepExists_elim fun u4 =>
      Entails.sepExists_elim fun u3 => Entails.sepExists_elim fun u2 => ?_
    refine Entails.sepExists_right (speWord 9) (Entails.sepExists_right (BitVec.ofNat 64 n)
      (Entails.sepExists_right u2 (Entails.sepExists_right u3
      (Entails.sepExists_right u4 (Entails.sepExists_right u5 ?_)))))
    rw [show (speWord 9 = speWord 9 ∧ BitVec.ofNat 64 n = BitVec.ofNat 64 n) = True from
      eq_true ⟨rfl, rfl⟩, pure_true, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  | invalidKeyAgreement =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have hs : asm% (speSize - spePayloadOff) = 40 := rfl
    rw [h8, hs, memRegion_40_cells (a + 8#64)]
    simp only [sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_elim fun u5 => Entails.sepExists_elim fun u4 =>
      Entails.sepExists_elim fun u3 => Entails.sepExists_elim fun u2 =>
      Entails.sepExists_elim fun u1 => ?_
    refine Entails.sepExists_right (speWord 10) (Entails.sepExists_right u1
      (Entails.sepExists_right u2 (Entails.sepExists_right u3
      (Entails.sepExists_right u4 (Entails.sepExists_right u5 ?_)))))
    rw [show (speWord 10 = speWord 10) = True from eq_true rfl, pure_true, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  | invalidSessionStructure r =>
    dsimp only [speAt, speDetached, strRefAt, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have hb8 : asm64% boxSliceLenOff = 8#64 := rfl
    have h24 : asm64% (spePayloadOff + boxSliceSize) = 24#64 := rfl
    have hs : asm% (speSize - (spePayloadOff + boxSliceSize)) = 24 := rfl
    rw [h8, hb8, h24, hs, memRegion_24_cells (a + 24#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_elim fun u5 => Entails.sepExists_elim fun u4 =>
      Entails.sepExists_elim fun u3 => Entails.sepExists_elim fun p => ?_
    refine Entails.sepExists_right (speWord 20) (Entails.sepExists_right p
      (Entails.sepExists_right (BitVec.ofNat 64 (invalidSessionStructureStr r).length)
      (Entails.sepExists_right u3 (Entails.sepExists_right u4 (Entails.sepExists_right u5 ?_)))))
    rw [show (speWord 20 = speWord 20 ∧
      BitVec.ofNat 64 (invalidSessionStructureStr r).length = BitVec.ofNat 64 (invalidSessionStructureStr r).length) = True from
      eq_true ⟨rfl, rfl⟩, pure_true, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  | duplicatedMessage i c =>
    dsimp only [speAt, speDetached, words6At]
    rw [memRegion_32_cells (a + 16#64)]
    simp only [sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_elim fun u5 => Entails.sepExists_elim fun u4 =>
      Entails.sepExists_elim fun u3 => Entails.sepExists_elim fun u2 => ?_
    refine Entails.sepExists_right (speWord 23) (Entails.sepExists_right (c ++ i)
      (Entails.sepExists_right u2 (Entails.sepExists_right u3
      (Entails.sepExists_right u4 (Entails.sepExists_right u5 ?_)))))
    have hlo : (c ++ i).extractLsb' 0 32 = i := by bv_bits
    have hhi : (c ++ i).extractLsb' 32 32 = c := by bv_bits
    have ha12 : (a + 8#64) + 4#64 = a + 12#64 := by bv_omega
    rw [pointsTo64_eq_pair32 (a + 8#64) (c ++ i), hlo, hhi, ha12,
      show (speWord 23 = speWord 23 ∧ i = i ∧ c = c) = True from eq_true ⟨rfl, rfl, rfl⟩,
      pure_true, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  | invalidMessage t r =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have h32 : asm64% speInvalidMessageTypeOff = 32#64 := rfl
    have h33 : asm64% (speInvalidMessageTypeOff + 1) = 33#64 := rfl
    have hs : asm% (speSize - (speInvalidMessageTypeOff + 1)) = 15 := rfl
    have ha33 : (a + 32#64) + 1#64 = a + 33#64 := by bv_omega
    have ha40 : a + 33#64 + 7#64 = a + 40#64 := by bv_omega
    rw [h8, h32, h33, hs, show (15 : Nat) = 7 + 8 by rfl,
      memRegion_split (a + 33#64) 7 8 (by decide), ha40, ← ha33, ProofLib.memRegion_eight,
      sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right,
      sepExists_sepConj_right]
    refine Entails.sepExists_elim fun u5 => ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left (invalidMsgStr_unpack A (a + 8#64) r))) ?_
    rw [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_right (vecU8_unpack3 A (a + 8#64) bs)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_elim fun u1 => Entails.sepExists_elim fun u2 => ?_
    have hgrp :
        ((a ↦₆₄ speWord 24) ∗
          (⌜invalidMsgBytesOk r bs⌝ ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
            ((a + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ SpqrV1.Alloc.vecU8Buf A u1 u2 bs) ∗
          ((a + 32#64) ↦₈ msgTypeByte t) ∗ memRegion (a + 33#64) 7 ∗
          ((a + 40#64) ↦₆₄ u5)) =
        (⌜invalidMsgBytesOk r bs⌝ ∗
          (((a + 32#64) ↦₈ msgTypeByte t) ∗ memRegion (a + 33#64) 7) ∗
          ((a ↦₆₄ speWord 24) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
            ((a + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((a + 40#64) ↦₆₄ u5) ∗
            SpqrV1.Alloc.vecU8Buf A u1 u2 bs)) := by ac_rfl
    rw [hgrp, ← ha33]
    refine Entails.pure_left fun hok => ?_
    refine Entails.trans (sepConj_mono_left (byte_pad7_unpack (a + 32#64) (msgTypeByte t))) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun u4 => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hu4 => ?_
    refine Entails.sepExists_right (speWord 24) (Entails.sepExists_right u1
      (Entails.sepExists_right u2 (Entails.sepExists_right (BitVec.ofNat 64 bs.length)
      (Entails.sepExists_right u4 (Entails.sepExists_right u5 ?_)))))
    refine Entails.sepExists_right bs ?_
    rw [show (speWord 24 = speWord 24 ∧ invalidMsgBytesOk r bs ∧
      BitVec.ofNat 64 bs.length = BitVec.ofNat 64 bs.length ∧
      u4.extractLsb' 0 8 = msgTypeByte t) = True from eq_true ⟨rfl, hok, rfl, hu4⟩,
      pure_true, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  | panic =>
    dsimp only [speAt]
    rw [← sepConj_emp ⌜False⌝]
    exact Entails.pure_left fun hf => False.elim hf

theorem speAt_pack (A : RustAlloc) (fnName : List (BitVec 8)) (a : BitVec 64)
    (u0 u1 u2 u3 u4 u5 : BitVec 64) (e : SignalProtocolError) :
    words6At a u0 u1 u2 u3 u4 u5 ∗ speDetached A fnName u0 u1 u2 u3 u4 u5 e ⊢
      speAt A fnName a e := by
  cases e with
  | invalidState =>
    dsimp only [speAt, speDetached, strRefAt, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have h32 : asm64% speInvalidStateFnOff = 32#64 := rfl
    have hb8 : asm64% boxSliceLenOff = 8#64 := rfl
    rw [h8, h32, hb8, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    have hpull :
        (((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
          ((a + 24#64) ↦₆₄ u3) ∗ ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u5)) ∗
          ⌜u0 = speWord 1 ∧ u3 = BitVec.ofNat 64 bs.length ∧
            u5 = BitVec.ofNat 64 fnName.length⌝ ∗
          SpqrV1.Alloc.vecU8Buf A u1 u2 bs ∗ (u4 ↦ᵣ fnName)) =
        (⌜u0 = speWord 1 ∧ u3 = BitVec.ofNat 64 bs.length ∧
            u5 = BitVec.ofNat 64 fnName.length⌝ ∗
          ((a ↦₆₄ u0) ∗
            (((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) ∗
              SpqrV1.Alloc.vecU8Buf A u1 u2 bs) ∗
            (((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u5) ∗ (u4 ↦ᵣ fnName)))) := by ac_rfl
    rw [hpull]
    refine Entails.pure_left fun ⟨hu0, hu3, hu5⟩ => ?_
    subst hu0; subst hu3; subst hu5
    have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
    have ha24 : (a + 8#64) + 16#64 = a + 24#64 := by bv_omega
    have ha40 : (a + 32#64) + 8#64 = a + 40#64 := by bv_omega
    rw [← ha16, ← ha24, ← ha40]
    refine sepConj_mono_right (sepConj_mono
      (Entails.trans (vecU8_pack3 A (a + 8#64) u1 u2 bs)
        (Entails.sepExists_right bs (Entails.refl _)))
      (Entails.sepExists_right u4 (Entails.refl _)))
  | ciphertextMessageTooShort n =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have h16 : asm64% (spePayloadOff + 8) = 16#64 := rfl
    have hs : asm% (speSize - (spePayloadOff + 8)) = 32 := rfl
    rw [h8, h16, hs, sepConj_comm]
    refine Entails.pure_left fun ⟨hu0, hu1⟩ => ?_
    subst hu0; subst hu1
    rw [memRegion_32_cells (a + 16#64)]
    refine sepConj_mono_right (sepConj_mono_right ?_)
    exact Entails.sepExists_right u5 (Entails.sepExists_right u4 (Entails.sepExists_right u3
      (Entails.sepExists_right u2
        (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd])))))
  | legacyCiphertextVersion v =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have h9 : asm64% (spePayloadOff + 1) = 9#64 := rfl
    have hs : asm% (speSize - (spePayloadOff + 1)) = 39 := rfl
    rw [h8, h9, hs, sepConj_comm]
    refine Entails.pure_left fun ⟨hu0, hv⟩ => ?_
    subst hu0
    exact sepConj_mono_right (byte_pad39_pack a u1 u2 u3 u4 u5 v hv)
  | unrecognizedCiphertextVersion v =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have h9 : asm64% (spePayloadOff + 1) = 9#64 := rfl
    have hs : asm% (speSize - (spePayloadOff + 1)) = 39 := rfl
    rw [h8, h9, hs, sepConj_comm]
    refine Entails.pure_left fun ⟨hu0, hv⟩ => ?_
    subst hu0
    exact sepConj_mono_right (byte_pad39_pack a u1 u2 u3 u4 u5 v hv)
  | invalidProtobufEncoding =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have hs : asm% (speSize - spePayloadOff) = 40 := rfl
    rw [h8, hs, sepConj_comm]
    refine Entails.pure_left fun hu0 => ?_
    subst hu0
    rw [memRegion_40_cells (a + 8#64)]
    refine sepConj_mono_right ?_
    exact Entails.sepExists_right u5 (Entails.sepExists_right u4 (Entails.sepExists_right u3
      (Entails.sepExists_right u2 (Entails.sepExists_right u1
        (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd]))))))
  | noKeyTypeIdentifier =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have hs : asm% (speSize - spePayloadOff) = 40 := rfl
    rw [h8, hs, sepConj_comm]
    refine Entails.pure_left fun hu0 => ?_
    subst hu0
    rw [memRegion_40_cells (a + 8#64)]
    refine sepConj_mono_right ?_
    exact Entails.sepExists_right u5 (Entails.sepExists_right u4 (Entails.sepExists_right u3
      (Entails.sepExists_right u2 (Entails.sepExists_right u1
        (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd]))))))
  | badKeyType t =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have h9 : asm64% (spePayloadOff + 1) = 9#64 := rfl
    have hs : asm% (speSize - (spePayloadOff + 1)) = 39 := rfl
    rw [h8, h9, hs, sepConj_comm]
    refine Entails.pure_left fun ⟨hu0, hv⟩ => ?_
    subst hu0
    exact sepConj_mono_right (byte_pad39_pack a u1 u2 u3 u4 u5 t hv)
  | badKeyLength n =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have h16 : asm64% (spePayloadOff + 8) = 16#64 := rfl
    have hs : asm% (speSize - (spePayloadOff + 8)) = 32 := rfl
    rw [h8, h16, hs, sepConj_comm]
    refine Entails.pure_left fun ⟨hu0, hu1⟩ => ?_
    subst hu0; subst hu1
    rw [memRegion_32_cells (a + 16#64)]
    refine sepConj_mono_right (sepConj_mono_right ?_)
    exact Entails.sepExists_right u5 (Entails.sepExists_right u4 (Entails.sepExists_right u3
      (Entails.sepExists_right u2
        (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd])))))
  | invalidKeyAgreement =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have hs : asm% (speSize - spePayloadOff) = 40 := rfl
    rw [h8, hs, sepConj_comm]
    refine Entails.pure_left fun hu0 => ?_
    subst hu0
    rw [memRegion_40_cells (a + 8#64)]
    refine sepConj_mono_right ?_
    exact Entails.sepExists_right u5 (Entails.sepExists_right u4 (Entails.sepExists_right u3
      (Entails.sepExists_right u2 (Entails.sepExists_right u1
        (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd]))))))
  | invalidSessionStructure r =>
    dsimp only [speAt, speDetached, strRefAt, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have hb8 : asm64% boxSliceLenOff = 8#64 := rfl
    have h24 : asm64% (spePayloadOff + boxSliceSize) = 24#64 := rfl
    have hs : asm% (speSize - (spePayloadOff + boxSliceSize)) = 24 := rfl
    rw [h8, hb8, h24, hs]
    have hpull :
        (((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
          ((a + 24#64) ↦₆₄ u3) ∗ ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u5)) ∗
          ⌜u0 = speWord 20 ∧ u2 = BitVec.ofNat 64 (invalidSessionStructureStr r).length⌝ ∗ (u1 ↦ᵣ invalidSessionStructureStr r)) =
        (⌜u0 = speWord 20 ∧ u2 = BitVec.ofNat 64 (invalidSessionStructureStr r).length⌝ ∗
          ((a ↦₆₄ u0) ∗
            (((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ (u1 ↦ᵣ invalidSessionStructureStr r)) ∗
            (((a + 24#64) ↦₆₄ u3) ∗ ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u5)))) := by ac_rfl
    rw [hpull]
    refine Entails.pure_left fun ⟨hu0, hu2⟩ => ?_
    subst hu0; subst hu2
    have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
    rw [← ha16, memRegion_24_cells (a + 24#64)]
    refine sepConj_mono_right (sepConj_mono
      (Entails.sepExists_right u1 (Entails.refl _))
      (Entails.sepExists_right u5 (Entails.sepExists_right u4 (Entails.sepExists_right u3
        (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd]))))))
  | duplicatedMessage i c =>
    dsimp only [speAt, speDetached, words6At]
    rw [sepConj_comm]
    refine Entails.pure_left fun ⟨hu0, hi, hc⟩ => ?_
    subst hu0
    have ha12 : (a + 8#64) + 4#64 = a + 12#64 := by bv_omega
    rw [pointsTo64_eq_pair32 (a + 8#64) u1, hi, hc, ha12, memRegion_32_cells (a + 16#64),
      sepConj_assoc]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
    exact Entails.sepExists_right u5 (Entails.sepExists_right u4 (Entails.sepExists_right u3
      (Entails.sepExists_right u2
        (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd])))))
  | invalidMessage t r =>
    dsimp only [speAt, speDetached, words6At]
    have h8 : asm64% spePayloadOff = 8#64 := rfl
    have h32 : asm64% speInvalidMessageTypeOff = 32#64 := rfl
    have h33 : asm64% (speInvalidMessageTypeOff + 1) = 33#64 := rfl
    have hs : asm% (speSize - (speInvalidMessageTypeOff + 1)) = 15 := rfl
    have ha33 : (a + 32#64) + 1#64 = a + 33#64 := by bv_omega
    have ha40 : a + 33#64 + 7#64 = a + 40#64 := by bv_omega
    rw [h8, h32, h33, hs, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    have hpull :
        (((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
          ((a + 24#64) ↦₆₄ u3) ∗ ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u5)) ∗
          ⌜u0 = speWord 24 ∧ invalidMsgBytesOk r bs ∧
            u3 = BitVec.ofNat 64 bs.length ∧ u4.extractLsb' 0 8 = msgTypeByte t⌝ ∗
          SpqrV1.Alloc.vecU8Buf A u1 u2 bs) =
        (⌜u0 = speWord 24 ∧ invalidMsgBytesOk r bs ∧
            u3 = BitVec.ofNat 64 bs.length ∧ u4.extractLsb' 0 8 = msgTypeByte t⌝ ∗
          ((a ↦₆₄ u0) ∗
            (((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) ∗
              SpqrV1.Alloc.vecU8Buf A u1 u2 bs) ∗
            (((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u5)))) := by ac_rfl
    rw [hpull]
    refine Entails.pure_left fun ⟨hu0, hok, hu3, hu4⟩ => ?_
    subst hu0; subst hu3
    have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
    have ha24 : (a + 8#64) + 16#64 = a + 24#64 := by bv_omega
    rw [← ha16, ← ha24, show (15 : Nat) = 7 + 8 by rfl,
      memRegion_split (a + 33#64) 7 8 (by decide), ha40, ← ha33, ProofLib.memRegion_eight]
    refine sepConj_mono_right (sepConj_mono
      (Entails.trans (vecU8_pack3 A (a + 8#64) u1 u2 bs) (invalidMsgStr_pack A (a + 8#64) r bs hok))
      (Entails.trans (sepConj_mono_left (byte_pad7_pack (a + 32#64) u4 (msgTypeByte t) hu4)) ?_))
    rw [sepConj_assoc]
    exact sepConj_mono_right (sepConj_mono_right (Entails.sepExists_right u5 (Entails.refl _)))
  | panic =>
    dsimp only [speDetached]
    rw [sepConj_comm]
    exact Entails.pure_left fun hf => False.elim hf

def spkStructDetached (A : RustAlloc) (m : SignedPreKeyRecordStructure)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) : SepProp :=
  ⌜w2 = BitVec.ofNat 64 m.publicKey.length ∧
    w5 = BitVec.ofNat 64 m.privateKey.length ∧
    w8 = BitVec.ofNat 64 m.signature.length ∧
    w9 = m.timestamp ∧
    w10.extractLsb' 0 32 = m.id ∧
    w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
  SpqrV1.Alloc.vecU8Buf A w0 w1 m.publicKey ∗
  SpqrV1.Alloc.vecU8Buf A w3 w4 m.privateKey ∗
  SpqrV1.Alloc.vecU8Buf A w6 w7 m.signature

theorem spkStruct_unpack (A : RustAlloc) (a : BitVec 64) (m : SignedPreKeyRecordStructure) :
    signedPreKeyStructAt A a m ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64,
        words11At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
        spkStructDetached A m w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 := by
  dsimp only [signedPreKeyStructAt]
  rw [ProofLib.memRegion_four]
  refine Entails.trans (sepConj_mono (vecU8_unpack3 A a m.publicKey)
    (sepConj_mono (vecU8_unpack3 A (a + 0x18#64) m.privateKey)
      (sepConj_mono_left (vecU8_unpack3 A (a + 0x30#64) m.signature)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  refine Entails.sepExists_elim fun pad => Entails.sepExists_elim fun w6 =>
    Entails.sepExists_elim fun w7 => Entails.sepExists_elim fun w3 =>
    Entails.sepExists_elim fun w4 => Entails.sepExists_elim fun w0 =>
    Entails.sepExists_elim fun w1 => ?_
  have hw0_lt : SpqrV1.Alloc.vecU8Buf A w0 w1 m.publicKey ⊢
      ⌜w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗ SpqrV1.Alloc.vecU8Buf A w0 w1 m.publicKey := by
    dsimp only [SpqrV1.Alloc.vecU8Buf]
    refine Entails.pure_left fun ⟨hle, hlt, hp⟩ => ?_
    have hne : w0 ≠ 0xFFFFFFFFFFFFFFFF#64 := by
      intro heq; subst heq
      have : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
      omega
    exact Entails.pure_right hne (Entails.pure_right ⟨hle, hlt, hp⟩ (Entails.refl _))
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right (BitVec.ofNat 64 m.publicKey.length)
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
    (Entails.sepExists_right (BitVec.ofNat 64 m.privateKey.length)
    (Entails.sepExists_right w6 (Entails.sepExists_right w7
    (Entails.sepExists_right (BitVec.ofNat 64 m.signature.length)
    (Entails.sepExists_right m.timestamp (Entails.sepExists_right (pad ++ m.id) ?_))))))))))
  have hlo : (pad ++ m.id).extractLsb' 0 32 = m.id := by bv_bits
  have hhi : (pad ++ m.id).extractLsb' 32 32 = pad := by bv_bits
  have ha84 : (a + 80#64) + 4#64 = a + 84#64 := by bv_omega
  dsimp only [words11At, spkStructDetached]
  rw [pointsTo64_eq_pair32 (a + 80#64) (pad ++ m.id), hlo, hhi, ha84]
  have hpull1 :
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
        SpqrV1.Alloc.vecU8Buf A w0 w1 m.publicKey ∗
        ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
        SpqrV1.Alloc.vecU8Buf A w3 w4 m.privateKey ∗
        ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
        SpqrV1.Alloc.vecU8Buf A w6 w7 m.signature ∗
        ((a + 72#64) ↦₆₄ m.timestamp) ∗ ((a + 80#64) ↦₃₂ m.id) ∗ ((a + 84#64) ↦₃₂ pad)) =
      (SpqrV1.Alloc.vecU8Buf A w0 w1 m.publicKey ∗
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
          ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
          ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
          ((a + 72#64) ↦₆₄ m.timestamp) ∗ ((a + 80#64) ↦₃₂ m.id) ∗ ((a + 84#64) ↦₃₂ pad) ∗
          SpqrV1.Alloc.vecU8Buf A w3 w4 m.privateKey ∗
          SpqrV1.Alloc.vecU8Buf A w6 w7 m.signature)) := by ac_rfl
  rw [hpull1]
  refine Entails.trans (sepConj_mono_left hw0_lt) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hne => ?_
  rw [show (BitVec.ofNat 64 m.publicKey.length = BitVec.ofNat 64 m.publicKey.length ∧
      BitVec.ofNat 64 m.privateKey.length = BitVec.ofNat 64 m.privateKey.length ∧
      BitVec.ofNat 64 m.signature.length = BitVec.ofNat 64 m.signature.length ∧
      m.timestamp = m.timestamp ∧ m.id = m.id ∧ w0 ≠ 0xFFFFFFFFFFFFFFFF#64) = True from
      eq_true ⟨rfl, rfl, rfl, rfl, rfl, hne⟩, pure_true, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem spkStruct_pack (A : RustAlloc) (a : BitVec 64) (m : SignedPreKeyRecordStructure)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) :
    words11At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
      spkStructDetached A m w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ⊢
      signedPreKeyStructAt A a m := by
  dsimp only [signedPreKeyStructAt, words11At, spkStructDetached]
  have hpull :
      (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
        ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
        ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10)) ∗
        ⌜w2 = BitVec.ofNat 64 m.publicKey.length ∧
          w5 = BitVec.ofNat 64 m.privateKey.length ∧
          w8 = BitVec.ofNat 64 m.signature.length ∧
          w9 = m.timestamp ∧
          w10.extractLsb' 0 32 = m.id ∧
          w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
        SpqrV1.Alloc.vecU8Buf A w0 w1 m.publicKey ∗
        SpqrV1.Alloc.vecU8Buf A w3 w4 m.privateKey ∗
        SpqrV1.Alloc.vecU8Buf A w6 w7 m.signature) =
      (⌜w2 = BitVec.ofNat 64 m.publicKey.length ∧
          w5 = BitVec.ofNat 64 m.privateKey.length ∧
          w8 = BitVec.ofNat 64 m.signature.length ∧
          w9 = m.timestamp ∧
          w10.extractLsb' 0 32 = m.id ∧
          w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
        (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
            SpqrV1.Alloc.vecU8Buf A w0 w1 m.publicKey) ∗
          (((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
            SpqrV1.Alloc.vecU8Buf A w3 w4 m.privateKey) ∗
          (((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
            SpqrV1.Alloc.vecU8Buf A w6 w7 m.signature) ∗
          ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10))) := by ac_rfl
  rw [hpull]
  refine Entails.pure_left fun ⟨hw2, hw5, hw8, hw9, hw10, _⟩ => ?_
  subst hw2; subst hw5; subst hw8; subst hw9
  have ha32 : (a + 0x18#64) + 8#64 = a + 32#64 := by bv_omega
  have ha40 : (a + 0x18#64) + 16#64 = a + 40#64 := by bv_omega
  have ha56 : (a + 0x30#64) + 8#64 = a + 56#64 := by bv_omega
  have ha64 : (a + 0x30#64) + 16#64 = a + 64#64 := by bv_omega
  have ha84 : (a + 80#64) + 4#64 = a + 0x54#64 := by bv_omega
  rw [← ha32, ← ha40, ← ha56, ← ha64, pointsTo64_eq_pair32 (a + 80#64) w10, hw10, ha84,
    ProofLib.memRegion_four]
  exact sepConj_mono (vecU8_pack3 A a w0 w1 m.publicKey)
    (sepConj_mono (vecU8_pack3 A (a + 0x18#64) w3 w4 m.privateKey)
      (sepConj_mono (vecU8_pack3 A (a + 0x30#64) w6 w7 m.signature)
        (sepConj_mono_right (sepConj_mono_right
          (Entails.sepExists_right (w10.extractLsb' 32 32) (Entails.refl _))))))

theorem errResult88_pack (A : RustAlloc) (fnName : List (BitVec 8)) (out : BitVec 64)
    (u0 u1 u2 u3 u4 u5 w7 w8 w9 w10 : BitVec 64) (e : SignalProtocolError) :
    words11At out 0xFFFFFFFFFFFFFFFF#64 u0 u1 u2 u3 u4 u5 w7 w8 w9 w10 ∗
      speDetached A fnName u0 u1 u2 u3 u4 u5 e ⊢
      errResultAt A fnName 88 out e := by
  dsimp only [errResultAt, words11At]
  have htag : errTag = 0xFFFFFFFFFFFFFFFF#64 := rfl
  have hoff8 : asm64% resultErrSpeOff = 8#64 := rfl
  have hoff56 : asm64% (resultErrSpeOff + speSize) = 56#64 := rfl
  have hsz : 88 - asm% (resultErrSpeOff + speSize) = 32 := rfl
  rw [htag, hoff8, hoff56, hsz, memRegion_32_cells (out + 56#64)]
  have hw6 :
      (((out + 8#64) ↦₆₄ u0) ∗ ((out + 16#64) ↦₆₄ u1) ∗ ((out + 24#64) ↦₆₄ u2) ∗
        ((out + 32#64) ↦₆₄ u3) ∗ ((out + 40#64) ↦₆₄ u4) ∗ ((out + 48#64) ↦₆₄ u5)) =
      words6At (out + 8#64) u0 u1 u2 u3 u4 u5 := by
    dsimp only [words6At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hgroup :
      ((out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((out + 8#64) ↦₆₄ u0) ∗ ((out + 16#64) ↦₆₄ u1) ∗
        ((out + 24#64) ↦₆₄ u2) ∗ ((out + 32#64) ↦₆₄ u3) ∗ ((out + 40#64) ↦₆₄ u4) ∗
        ((out + 48#64) ↦₆₄ u5) ∗ ((out + 56#64) ↦₆₄ w7) ∗ ((out + 64#64) ↦₆₄ w8) ∗
        ((out + 72#64) ↦₆₄ w9) ∗ ((out + 80#64) ↦₆₄ w10)) ∗
        speDetached A fnName u0 u1 u2 u3 u4 u5 e =
      (out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((((out + 8#64) ↦₆₄ u0) ∗ ((out + 16#64) ↦₆₄ u1) ∗ ((out + 24#64) ↦₆₄ u2) ∗
            ((out + 32#64) ↦₆₄ u3) ∗ ((out + 40#64) ↦₆₄ u4) ∗ ((out + 48#64) ↦₆₄ u5)) ∗
          speDetached A fnName u0 u1 u2 u3 u4 u5 e) ∗
        (((out + 56#64) ↦₆₄ w7) ∗ ((out + 64#64) ↦₆₄ w8) ∗
          ((out + 72#64) ↦₆₄ w9) ∗ ((out + 80#64) ↦₆₄ w10)) := by ac_rfl
  rw [hgroup, hw6]
  refine sepConj_mono_right (sepConj_mono (speAt_pack A fnName (out + 8#64) u0 u1 u2 u3 u4 u5 e) ?_)
  exact Entails.sepExists_right w10 (Entails.sepExists_right w9 (Entails.sepExists_right w8
    (Entails.sepExists_right w7
      (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd])))))

theorem missing88_pack (A : RustAlloc) (out : BitVec 64)
    (w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) :
    words11At out 0xFFFFFFFFFFFFFFFF#64 (speWord 14) w2 w3 w4 w5 w6 w7 w8 w9 w10 ⊢
      spkAnsAt A out .missing := by
  dsimp only [spkAnsAt, pkAnsAt, words11At]
  have ha48 : (out + 0x10#64) + 32#64 = out + 48#64 := by bv_omega
  have hgroup :
      ((out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((out + 8#64) ↦₆₄ speWord 14) ∗
        ((out + 16#64) ↦₆₄ w2) ∗ ((out + 24#64) ↦₆₄ w3) ∗ ((out + 32#64) ↦₆₄ w4) ∗
        ((out + 40#64) ↦₆₄ w5) ∗ ((out + 48#64) ↦₆₄ w6) ∗ ((out + 56#64) ↦₆₄ w7) ∗
        ((out + 64#64) ↦₆₄ w8) ∗ ((out + 72#64) ↦₆₄ w9) ∗ ((out + 80#64) ↦₆₄ w10)) =
      (out ↦₆₄ errTag) ∗ ((out + 0x08#64) ↦₆₄ speWord 14) ∗
        (((out + 16#64) ↦₆₄ w2) ∗ ((out + 24#64) ↦₆₄ w3) ∗ ((out + 32#64) ↦₆₄ w4) ∗
          ((out + 40#64) ↦₆₄ w5)) ∗
        (((out + 48#64) ↦₆₄ w6) ∗ ((out + 56#64) ↦₆₄ w7) ∗ ((out + 64#64) ↦₆₄ w8) ∗
          ((out + 72#64) ↦₆₄ w9) ∗ ((out + 80#64) ↦₆₄ w10)) := by
    have htag : errTag = 0xFFFFFFFFFFFFFFFF#64 := rfl
    rw [htag]
    ac_rfl
  rw [hgroup, show 88 - 16 = 32 + 40 from rfl,
    memRegion_split (out + 0x10#64) 32 40 (by decide), ha48,
    memRegion_32_cells (out + 0x10#64), memRegion_40_cells (out + 48#64)]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono ?_ ?_))
  · exact Entails.sepExists_right w5 (Entails.sepExists_right w4 (Entails.sepExists_right w3
      (Entails.sepExists_right w2
        (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd])))))
  · exact Entails.sepExists_right w10 (Entails.sepExists_right w9 (Entails.sepExists_right w8
      (Entails.sepExists_right w7 (Entails.sepExists_right w6
        (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd]))))))

end CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers
