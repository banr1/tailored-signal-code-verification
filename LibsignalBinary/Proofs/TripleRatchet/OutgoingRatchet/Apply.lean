/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.Defs
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.OutgoingRatchetCodeSym
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `OutgoingTripleRatchet::apply_to_session_state`

Verifies `<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state`
against `otrApplyRawSpec`, `otrApplySpec`, and `otrApplyPlacedSpec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Byte and region helpers -/

theorem keyToBytes32_length (k : BitVec 256) : (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

/-- Pack a byte list into a `w`-bit word in little-endian order. -/
def packBV (w : Nat) (bs : List (BitVec 8)) : BitVec w :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.zeroExtend w) 0

/-- Pack 8 bytes into a 64-bit little-endian word. -/
def pack64 (bs : List (BitVec 8)) : BitVec 64 := packBV 64 bs

theorem unpack64_pack64 (bs : List (BitVec 8)) (h : bs.length = 8) :
    unpack64 (pack64 bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try cases h
  simp only [unpack64, pack64, packBV, List.foldr, List.cons.injEq, and_true]
  refine ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
          by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem pointsToBytes_8_eq_pointsTo64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ pack64 bs) := by
  rw [pointsTo64_eq_pointsToBytes, unpack64_pack64 bs h]

theorem pointsToBytes_32_eq_pointsTo64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₆₄ pack64 (bs.take 8)) ∗
       ((a + 8#64) ↦₆₄ pack64 ((bs.drop 8).take 8)) ∗
       ((a + 16#64) ↦₆₄ pack64 ((bs.drop 16).take 8)) ∗
       ((a + 24#64) ↦₆₄ pack64 (bs.drop 24))) := by
  have hsplit :
      bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ bs.drop 24)) := by
    have h24 : bs.drop 24 = (bs.drop 16).drop 8 := by simp [List.drop_drop]
    have h16 : bs.drop 16 = (bs.drop 8).drop 8 := by simp [List.drop_drop]
    rw [h24, List.take_append_drop, h16, List.take_append_drop, List.take_append_drop]
  have h0 : (bs.take 8).length = 8 := by simp [h]
  have h1 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have h2 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have h3 : (bs.drop 24).length = 8 := by simp [h]
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      h0, h1, h2,
      pointsToBytes_8_eq_pointsTo64 a (bs.take 8) h0,
      pointsToBytes_8_eq_pointsTo64 _ ((bs.drop 8).take 8) h1,
      pointsToBytes_8_eq_pointsTo64 _ ((bs.drop 16).take 8) h2,
      pointsToBytes_8_eq_pointsTo64 _ (bs.drop 24) h3]
  have ha8 : a + BitVec.ofNat 64 8 = a + 8#64 := rfl
  have ha16 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 16#64 := by bv_omega
  have ha24 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 24#64 := by bv_omega
  rw [ha24, ha16, ha8]

theorem leBytes_four_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  unfold leBytes unpack32 BitVec.extractLsb'
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map, Nat.shiftRight_eq_div_pow]
  rfl

theorem chainKeyBytes_pointsTo (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) =
      (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ ck.index) := by
  unfold chainKeyBytes
  have hlen : (keyToBytes32 ck.key).length = 32 := keyToBytes32_length ck.key
  rw [pointsToBytes_append, hlen, leBytes_four_eq_unpack32, ← pointsTo32_eq_pointsToBytes]

theorem mr_cut' (sp : BitVec 64) (c c' n k N : Nat) (hN : n + k = N) (hc' : c - n = c')
    (hn : n ≤ c) (hc : c < 2 ^ 64) (h : N ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 c) N =
      memRegion (sp - BitVec.ofNat 64 c) n ∗ memRegion (sp - BitVec.ofNat 64 c') k := by
  subst hN hc'
  refine memRegion_split' rfl ?_ h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt hc
  have h2 : (c - n) % 2 ^ 64 = c - n := Nat.mod_eq_of_lt (by omega)
  have h3 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, h3]
  omega

/-- Stack layout for `OTR::apply_to_session_state` (`otrApplyInternalStack = 128 + allocHookStack`). -/
theorem stackAt_otrApply (sp : BitVec 64) :
    stackAt sp otrApplyInternalStack =
      stackAt (sp - 128#64) allocHookStack ∗
      memRegion (sp - 128#64) 8 ∗
      (∃∗ s1 : BitVec 64, (sp - 120#64) ↦₆₄ s1) ∗
      (∃∗ s2 : BitVec 64, (sp - 112#64) ↦₆₄ s2) ∗
      memRegion (sp - 104#64) 4 ∗
      (∃∗ s3 : BitVec 32, (sp - 100#64) ↦₃₂ s3) ∗
      (∃∗ s4 : BitVec 64, (sp - 96#64) ↦₆₄ s4) ∗
      (∃∗ s5 : BitVec 64, (sp - 88#64) ↦₆₄ s5) ∗
      (∃∗ s6 : BitVec 64, (sp - 80#64) ↦₆₄ s6) ∗
      (∃∗ s7 : BitVec 64, (sp - 72#64) ↦₆₄ s7) ∗
      (∃∗ s8 : BitVec 64, (sp - 64#64) ↦₆₄ s8) ∗
      (∃∗ s9 : BitVec 64, (sp - 56#64) ↦₆₄ s9) ∗
      (∃∗ s10 : BitVec 64, (sp - 48#64) ↦₆₄ s10) ∗
      (∃∗ s11 : BitVec 64, (sp - 40#64) ↦₆₄ s11) ∗
      (∃∗ s12 : BitVec 64, (sp - 32#64) ↦₆₄ s12) ∗
      (∃∗ s13 : BitVec 64, (sp - 24#64) ↦₆₄ s13) ∗
      (∃∗ s14 : BitVec 64, (sp - 16#64) ↦₆₄ s14) ∗
      (∃∗ s15 : BitVec 64, (sp - 8#64) ↦₆₄ s15) := by
  show memRegion (sp - BitVec.ofNat 64 4224) 4224 = _
  rw [mr_cut' sp 4224 128 4096 128 4224 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 128 120 8 120 128 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 120 112 8 112 120 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 112 104 8 104 112 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 104 100 4 100 104 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 100 96 4 96 100 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 96 88 8 88 96 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 88 80 8 80 88 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 80 72 8 72 80 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 72 64 8 64 72 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 64 56 8 56 64 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 56 48 8 48 56 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 48 40 8 40 48 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 40 32 8 32 40 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 32 24 8 24 32 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 24 16 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 16 8 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  have hstk : memRegion (sp - BitVec.ofNat 64 4224) 4096 = stackAt (sp - 128#64) allocHookStack := by
    simp only [stackAt, allocHookStack]; congr 1; bv_omega
  rw [hstk, memRegion_four (sp - BitVec.ofNat 64 100)]
  simp only [memRegion_eight]

theorem stackAt_otrApply_fold (sp s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 : BitVec 64)
    (s3 : BitVec 32) :
    stackAt (sp - 128#64) allocHookStack ∗
      memRegion (sp - 128#64) 8 ∗
      ((sp - 120#64) ↦₆₄ s1) ∗
      ((sp - 112#64) ↦₆₄ s2) ∗
      memRegion (sp - 104#64) 4 ∗
      ((sp - 100#64) ↦₃₂ s3) ∗
      ((sp - 96#64) ↦₆₄ s4) ∗
      ((sp - 88#64) ↦₆₄ s5) ∗
      ((sp - 80#64) ↦₆₄ s6) ∗
      ((sp - 72#64) ↦₆₄ s7) ∗
      ((sp - 64#64) ↦₆₄ s8) ∗
      ((sp - 56#64) ↦₆₄ s9) ∗
      ((sp - 48#64) ↦₆₄ s10) ∗
      ((sp - 40#64) ↦₆₄ s11) ∗
      ((sp - 32#64) ↦₆₄ s12) ∗
      ((sp - 24#64) ↦₆₄ s13) ∗
      ((sp - 16#64) ↦₆₄ s14) ∗
      ((sp - 8#64) ↦₆₄ s15) ⊢
    stackAt sp otrApplyInternalStack := by
  rw [stackAt_otrApply sp]
  refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) ?_)
  refine sepConj_mono (Entails.sepExists_intro s1) (sepConj_mono (Entails.sepExists_intro s2) ?_)
  refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.sepExists_intro s3) ?_)
  refine sepConj_mono (Entails.sepExists_intro s4) (sepConj_mono (Entails.sepExists_intro s5) ?_)
  refine sepConj_mono (Entails.sepExists_intro s6) (sepConj_mono (Entails.sepExists_intro s7) ?_)
  refine sepConj_mono (Entails.sepExists_intro s8) (sepConj_mono (Entails.sepExists_intro s9) ?_)
  refine sepConj_mono (Entails.sepExists_intro s10) (sepConj_mono (Entails.sepExists_intro s11) ?_)
  refine sepConj_mono (Entails.sepExists_intro s12) (sepConj_mono (Entails.sepExists_intro s13) ?_)
  exact sepConj_mono (Entails.sepExists_intro s14) (Entails.sepExists_intro s15)

/-! ## Decomposition of `otrAt` and `sessionStateAt` for `OTR::apply_to_session_state` -/

/-- The heap part of `vecU8At A v cap ptr bs` without the 24-byte header at `v`. -/
def vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_cells_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs := by
  simp only [vecU8At, vecHeader, vecU8Buf, sepConj_assoc]

theorem vecU8Buf_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold vecU8Buf
  refine Entails.pure_left fun h => Entails.pure_right h ?_
  split
  · exact Entails.refl _
  · refine sepConj_mono_right ?_
    refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)) ?_
    rw [← memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega),
      Nat.add_sub_of_le h.1]
    exact Entails.refl _

theorem memRegion_32_cells (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) ∗ (∃∗ w3 : BitVec 64, (a + 24#64) ↦₆₄ w3) := by
  have hs : ∀ (b : BitVec 64) (k : Nat), k ≤ 24 →
      memRegion b (8 + k) = memRegion b 8 ∗ memRegion (b + 8#64) k :=
    fun b k hk => memRegion_split' rfl rfl (by omega)
  rw [hs a 24 (by decide), hs _ 16 (by decide), hs _ 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, memRegion_eight]

theorem cells_32_entails_memRegion (a w0 w1 w2 w3 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) ⊢
      memRegion a 32 := by
  rw [memRegion_32_cells a]
  exact sepConj_mono (Entails.sepExists_intro w0) (sepConj_mono (Entails.sepExists_intro w1)
    (sepConj_mono (Entails.sepExists_intro w2) (Entails.sepExists_intro w3)))

theorem mr_cut_add (a : BitVec 64) (c n k : Nat) (h : n + k ≤ 2 ^ 64) :
    memRegion (a + BitVec.ofNat 64 c) (n + k) =
      memRegion (a + BitVec.ofNat 64 c) n ∗ memRegion (a + BitVec.ofNat 64 (c + n)) k := by
  refine memRegion_split' rfl ?_ h
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Decompose `otrAt A o pqCap pqPtr ot` into the fields read by `OTR::apply_to_session_state`
and the rest as `memRegion`. -/
theorem otrAt_apply_split (A : RustAlloc) (o pqCap pqPtr : BitVec 64)
    (ot : OutgoingTripleRatchet (List (BitVec 8))) :
    let kbs := keyToBytes32 ot.senderChainKey.key
    otrAt A o pqCap pqPtr ot ⊢
      (o ↦₆₄ pqCap) ∗ ((o + 8#64) ↦₆₄ pqPtr) ∗
      ((o + 16#64) ↦₆₄ BitVec.ofNat 64 ot.pqrState.length) ∗
      vecU8Buf A pqCap pqPtr ot.pqrState ∗
      memRegion (o + 0x18#64) 128 ∗
      ((o + 0x98#64) ↦₆₄ pack64 (kbs.take 8)) ∗
      ((o + 0xa0#64) ↦₆₄ pack64 ((kbs.drop 8).take 8)) ∗
      ((o + 0xa8#64) ↦₆₄ pack64 ((kbs.drop 16).take 8)) ∗
      ((o + 0xb0#64) ↦₆₄ pack64 (kbs.drop 24)) ∗
      ((o + 0xb8#64) ↦₃₂ ot.senderChainKey.index) ∗
      memRegion (o + 0xbc#64) 12 := by
  intro kbs
  unfold otrAt
  rw [vecU8At_eq_cells_buf A o pqCap pqPtr ot.pqrState,
      chainKeyBytes_pointsTo (o + 0x98#64) ot.senderChainKey,
      pointsToBytes_32_eq_pointsTo64 (o + 0x98#64) kbs (keyToBytes32_length _)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  have h1 := pointsToBytes_entails_memRegion (o + 0x18#64) ot.senderRatchetKey.publicKey.bytes.toList
  have h2 := pointsToBytes_entails_memRegion (o + 0x38#64) ot.senderRatchetKey.privateKey.bytes.toList
  have h3 := pointsToBytes_entails_memRegion (o + 0x58#64) ot.localIdentityKey.publicKey.bytes.toList
  have h4 := pointsToBytes_entails_memRegion (o + 0x78#64) ot.remoteIdentityKey.publicKey.bytes.toList
  rw [List.Vector.toList_length] at h1 h2 h3 h4
  have h128 :
      memRegion (o + 0x18#64) 128 =
        memRegion (o + 0x18#64) 32 ∗ memRegion (o + 0x38#64) 32 ∗
          memRegion (o + 0x58#64) 32 ∗ memRegion (o + 0x78#64) 32 := by
    rw [show (128 : Nat) = 32 + (32 + (32 + 32)) from rfl,
        mr_cut_add o 24 32 (32 + (32 + 32)) (by decide),
        mr_cut_add o 56 32 (32 + 32) (by decide),
        mr_cut_add o 88 32 32 (by decide)]
  have h5 := pointsTo32_entails_memRegion (o + 0xbc#64) ot.previousCounter
  have h6 := pointsTo8_entails_memRegion (o + 0xc0#64) ot.sessionVersion
  have h12 :
      memRegion (o + 0xbc#64) 12 =
        memRegion (o + 0xbc#64) 4 ∗ memRegion (o + 0xc0#64) 1 ∗ memRegion (o + 0xc1#64) 7 := by
    rw [show (12 : Nat) = 4 + (1 + 7) from rfl,
        mr_cut_add o 188 4 (1 + 7) (by decide),
        mr_cut_add o 192 1 7 (by decide)]
  rw [h128, h12]
  simp only [sepConj_assoc]
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono h5 (sepConj_mono h6 (Entails.refl _)))))))))))

/-- Fold the remaining fields of `o` into `memRegion o 200`. -/
theorem otr_fold_memRegion (o w0 w1 w2 ck0 ck1 ck2 ck3 : BitVec 64) (idx : BitVec 32) :
    ((o ↦₆₄ w0) ∗ ((o + 8#64) ↦₆₄ w1) ∗ ((o + 16#64) ↦₆₄ w2) ∗
      memRegion (o + 0x18#64) 128 ∗
      ((o + 0x98#64) ↦₆₄ ck0) ∗ ((o + 0xa0#64) ↦₆₄ ck1) ∗
      ((o + 0xa8#64) ↦₆₄ ck2) ∗ ((o + 0xb0#64) ↦₆₄ ck3) ∗
      ((o + 0xb8#64) ↦₃₂ idx) ∗ memRegion (o + 0xbc#64) 12) ⊢
    memRegion o 200 := by
  have h0 := pointsTo64_entails_memRegion o w0
  have h1 := pointsTo64_entails_memRegion (o + 8#64) w1
  have h2 := pointsTo64_entails_memRegion (o + 16#64) w2
  have hck := cells_32_entails_memRegion (o + 0x98#64) ck0 ck1 ck2 ck3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hck
  have hidx := pointsTo32_entails_memRegion (o + 0xb8#64) idx
  have hm :
      memRegion o 200 =
        memRegion o 8 ∗ (memRegion (o + 8#64) 8 ∗ (memRegion (o + 16#64) 8 ∗
          (memRegion (o + 0x18#64) 128 ∗ (memRegion (o + 0x98#64) 32 ∗
            (memRegion (o + 0xb8#64) 4 ∗ memRegion (o + 0xbc#64) 12))))) := by
    rw [memRegion_split o 8 192 (by decide),
        mr_cut_add o 8 8 184 (by decide),
        mr_cut_add o 16 8 176 (by decide),
        mr_cut_add o 24 128 48 (by decide),
        mr_cut_add o 152 32 16 (by decide),
        mr_cut_add o 184 4 12 (by decide)]
  rw [hm]
  have hassoc :
      ((o ↦₆₄ w0) ∗ ((o + 8#64) ↦₆₄ w1) ∗ ((o + 16#64) ↦₆₄ w2) ∗
        memRegion (o + 0x18#64) 128 ∗
        ((o + 0x98#64) ↦₆₄ ck0) ∗ ((o + 0xa0#64) ↦₆₄ ck1) ∗
        ((o + 0xa8#64) ↦₆₄ ck2) ∗ ((o + 0xb0#64) ↦₆₄ ck3) ∗
        ((o + 0xb8#64) ↦₃₂ idx) ∗ memRegion (o + 0xbc#64) 12) =
      ((o ↦₆₄ w0) ∗ (((o + 8#64) ↦₆₄ w1) ∗ (((o + 16#64) ↦₆₄ w2) ∗
        (memRegion (o + 0x18#64) 128 ∗
          ((((o + 0x98#64) ↦₆₄ ck0) ∗ ((o + 0xa0#64) ↦₆₄ ck1) ∗
            ((o + 0xa8#64) ↦₆₄ ck2) ∗ ((o + 0xb0#64) ↦₆₄ ck3)) ∗
            (((o + 0xb8#64) ↦₃₂ idx) ∗ memRegion (o + 0xbc#64) 12)))))) := by
    simp only [sepConj_assoc]
  rw [hassoc]
  exact sepConj_mono h0 (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono (Entails.refl _)
    (sepConj_mono hck (sepConj_mono hidx (Entails.refl _))))))

/-- The untouched fields of `sessionStateAt A ss G st` during `OTR::apply_to_session_state`. -/
def sessionApplyFrame (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (sg : SenderChainGhost) (sc : SenderChain) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  ⌜PublicKey.deserialize sg.srk.bytes = .ok sc.ratchetKey.publicKey ∧
    sg.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
    sg.srk.bytes.length = 33⌝ ∗
    vecGhostAt A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
    vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
      (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (ss + 0x60#64) ∗
    vecU8Buf A sg.priv.cap sg.priv.ptr sg.priv.bytes ∗
    vecBuf A 104 8 (messageKeyAt A) sg.mkCap sg.mkPtr [] ∗
    memRegion (ss + 0xf4#64) 4 ∗
    optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
    optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
    ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗ ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
    ((ss + 0x150#64) ↦ₛ G.regIds)

theorem vecU8Buf_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  exact Entails.pure_left fun h => Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))

theorem vecU8Buf_dealloc_32 (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hbs : bs.length = 32) :
    vecU8Buf A cap ptr bs ⊢
      ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  refine Entails.trans (vecU8Buf_dealloc A cap ptr bs) ?_
  rw [hbs]
  refine Entails.pure_left fun h => Entails.pure_right h ?_
  have hne : cap ≠ 0 := by
    intro hc; subst hc; simp at h
  rw [ite_eq_right_iff.mpr (fun hc => absurd hc hne)]
  exact Entails.refl _

/-- Bidirectional decomposition of `sessionStateAt` exposing the `pq_ratchet_state` and
`sender_chain` cells touched by `OTR::apply_to_session_state` while framing the untouched fields
in `sessionApplyFrame`. -/
theorem sessionStateAt_eq_apply (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (sg : SenderChainGhost) (sc : SenderChain)
    (pqPin : VecPin) (pqBs : List (BitVec 8)) (ckPin : VecPin) (ck : ChainKey) :
    sessionStateAt A ss
      { G with sender := some ({ sg with ck := ckPin }), pq := pqPin }
      { st with senderChain := some ({ sc with chainKey := ck }), pqRatchetState := pqBs } =
      (((ss + 0x78#64) ↦₆₄ pqPin.cap) ∗ ((ss + 0x80#64) ↦₆₄ pqPin.ptr) ∗
        ((ss + 0x88#64) ↦₆₄ BitVec.ofNat 64 pqBs.length) ∗
        vecU8Buf A pqPin.cap pqPin.ptr pqBs ∗
        ((ss + 0x90#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 0x98#64) ↦₆₄ sg.srk.ptr) ∗
        ((ss + 0xa0#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
        vecU8Buf A sg.srk.cap sg.srk.ptr sg.srk.bytes ∗
        ((ss + 0xa8#64) ↦₆₄ sg.priv.cap) ∗ ((ss + 0xb0#64) ↦₆₄ sg.priv.ptr) ∗
        ((ss + 0xb8#64) ↦₆₄ BitVec.ofNat 64 sg.priv.bytes.length) ∗
        ((ss + 0xc0#64) ↦₆₄ sg.mkCap) ∗ ((ss + 0xc8#64) ↦₆₄ sg.mkPtr) ∗
        ((ss + 0xd0#64) ↦₆₄ 0#64) ∗
        ((ss + 0xd8#64) ↦₆₄ ckPin.cap) ∗ ((ss + 0xe0#64) ↦₆₄ ckPin.ptr) ∗
        ((ss + 0xe8#64) ↦₆₄ 32#64) ∗
        ((ss + 0xf0#64) ↦₃₂ ck.index) ∗
        vecU8Buf A ckPin.cap ckPin.ptr (keyToBytes32 ck.key) ∗
        sessionApplyFrame A ss G st sg sc) := by
  unfold sessionStateAt sessionApplyFrame optSenderChainAt vecGhostAt optChainKeyAt vecAt vecHeader
  simp only [vecU8At_eq_cells_buf, keyToBytes32_length, List.length_nil,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  ac_rfl

/-- Extract `G.sender = some sg` from `sessionStateAt A ss G st` when `st.senderChain = some sc`. -/
theorem sessionStateAt_sender_some (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (sc : SenderChain) (hsc : st.senderChain = some sc) :
    sessionStateAt A ss G st ⊢ ∃∗ sg : SenderChainGhost, ⌜G.sender = some sg⌝ ∗ sessionStateAt A ss G st := by
  cases hGs : G.sender with
  | none =>
    have hpull : sessionStateAt A ss G st = (⌜False⌝ ∗
        (⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
          (match st.remoteIdentity with
           | none => G.remoteIk.bytes = []
           | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
          G.chains.length = st.receiverChains.length ∧
          G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
          G.localIk.bytes.length = 33 ∧
          (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
        vecGhostAt A G.localIk ss ∗
        vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
        vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        vecGhostAt A G.alice (ss + 0x60#64) ∗
        vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
        optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
        optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
        ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
        ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
        ((ss + 0x150#64) ↦ₛ G.regIds))) := by
      unfold sessionStateAt
      rw [hsc, hGs]
      simp only [optSenderChainAt]
      ac_rfl
    rw [hpull]
    exact Entails.pure_left fun h => False.elim h
  | some sg =>
    refine Entails.trans ?_ (Entails.sepExists_intro sg)
    exact Entails.pure_right rfl (Entails.refl _)

/-- Fold a freshly allocated 32-byte block with the four 64-bit words of `keyToBytes32 k` into
`vecU8Buf A 32#64 p' (keyToBytes32 k)`. -/
theorem vecU8Buf_of_cells_32 (A : RustAlloc) (p' : BitVec 64) (k : BitVec 256) (hp' : p' ≠ 0#64) :
    let kbs := keyToBytes32 k
    A.live p' 32 1 ∗
      ((p' ↦₆₄ pack64 (kbs.take 8)) ∗
       ((p' + 8#64) ↦₆₄ pack64 ((kbs.drop 8).take 8)) ∗
       ((p' + 16#64) ↦₆₄ pack64 ((kbs.drop 16).take 8)) ∗
       ((p' + 24#64) ↦₆₄ pack64 (kbs.drop 24))) ⊢
    vecU8Buf A 32#64 p' (keyToBytes32 k) := by
  intro kbs
  rw [← pointsToBytes_32_eq_pointsTo64 p' kbs (keyToBytes32_length k)]
  unfold vecU8Buf
  have hne : (32#64 : BitVec 64) ≠ 0 := by decide
  rw [ite_eq_right_iff.mpr (fun hc => absurd hc hne)]
  simp only [keyToBytes32_length, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.sub_self, memRegion_zero, sepConj_emp]
  exact Entails.pure_right ⟨by decide, by decide, hp'⟩ (Entails.refl _)

theorem applyRel_afterOtrApply (G : SessionGhost) (sg : SenderChainGhost)
    (hGs : G.sender = some sg) (ckPtr pqCap pqPtr : BitVec 64) :
    G.AfterOutgoingRatchetApply (afterOtrApply G sg ckPtr pqCap pqPtr) ∧
      (afterOtrApply G sg ckPtr pqCap pqPtr).pq = ⟨pqCap, pqPtr⟩ := by
  refine ⟨⟨sg, { sg with ck := ⟨32#64, ckPtr⟩ }, hGs, rfl, rfl, rfl⟩, rfl⟩

@[local simp, local arm64_norm, local wp_norm]
private theorem int64_toBitVec_ofUInt64 (u : UInt64) : (Int64.ofUInt64 u).toBitVec = u.toBitVec := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem uint64_toBitVec_ofBitVec (b : BitVec 64) : (UInt64.ofBitVec b).toBitVec = b := rfl

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state") → (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state" + 312)]

private theorem addsPState64_hi_false_aux {cap : BitVec 64}
    (h1 : (32#64).ule cap = true) (h2 : cap.ult 0x8000000000000000#64 = true) :
    ConditionHolds CondCode.HI (addsPState64 (cap - 1#64) 3#64) = false := by
  unfold ConditionHolds addsPState64 AddWithCarry64
  dsimp only
  bv_kernel

private theorem addsPState64_hi_false {cap ptr : BitVec 64}
    (h : 32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) :
    ConditionHolds CondCode.HI (addsPState64 (cap - 1#64) 3#64) = false := by
  apply addsPState64_hi_false_aux
  · rw [BitVec.ule_eq_decide, decide_eq_true_eq]; exact h.1
  · rw [BitVec.ult_eq_decide, decide_eq_true_eq]; exact h.2.1

namespace ApplyFrameFacts

theorem elim_ex {α : Sort _} {prog : Program} {pc : BitVec 64} {s : State}
    {C : α → SepProp} {R : SepProp} {post : State → SepProp → Prop}
    (h : ∀ x, SepWP prog pc s (R ∗ C x) post) :
    SepWP prog pc s ((∃∗ x, C x) ∗ R) post := by
  rw [sepExists_sepConj_left]
  exact SepWP.exists_elim fun x => by rw [sepConj_comm]; exact h x

theorem skip_atom {prog : Program} {pc : BitVec 64} {s : State}
    {A R : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog pc s (R ∗ A) post) :
    SepWP prog pc s (A ∗ R) post := by
  rw [sepConj_comm]
  exact h

theorem sepWP_unpack_stackAt_otrApply {prog : Program} {pc : BitVec 64} {s : State}
    (sp : BitVec 64) {P F : SepProp} {post : State → SepProp → Prop}
    (hf : P = stackAt sp otrApplyInternalStack ∗ F)
    (h : ∀ (s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 : BitVec 64) (s3 : BitVec 32),
      SepWP prog pc s
        ((stackAt (sp - 128#64) allocHookStack ∗
          memRegion (sp - 128#64) 8 ∗
          ((sp - 120#64) ↦₆₄ s1) ∗
          ((sp - 112#64) ↦₆₄ s2) ∗
          memRegion (sp - 104#64) 4 ∗
          ((sp - 100#64) ↦₃₂ s3) ∗
          ((sp - 96#64) ↦₆₄ s4) ∗
          ((sp - 88#64) ↦₆₄ s5) ∗
          ((sp - 80#64) ↦₆₄ s6) ∗
          ((sp - 72#64) ↦₆₄ s7) ∗
          ((sp - 64#64) ↦₆₄ s8) ∗
          ((sp - 56#64) ↦₆₄ s9) ∗
          ((sp - 48#64) ↦₆₄ s10) ∗
          ((sp - 40#64) ↦₆₄ s11) ∗
          ((sp - 32#64) ↦₆₄ s12) ∗
          ((sp - 24#64) ↦₆₄ s13) ∗
          ((sp - 16#64) ↦₆₄ s14) ∗
          ((sp - 8#64) ↦₆₄ s15)) ∗ F) post) :
    SepWP prog pc s P post := by
  rw [hf, stackAt_otrApply sp]
  simp only [sepConj_assoc]
  apply skip_atom; simp only [sepConj_assoc]
  apply skip_atom; simp only [sepConj_assoc]
  apply elim_ex; intro s1; simp only [sepConj_assoc]
  apply elim_ex; intro s2; simp only [sepConj_assoc]
  apply skip_atom; simp only [sepConj_assoc]
  apply elim_ex; intro s3; simp only [sepConj_assoc]
  apply elim_ex; intro s4; simp only [sepConj_assoc]
  apply elim_ex; intro s5; simp only [sepConj_assoc]
  apply elim_ex; intro s6; simp only [sepConj_assoc]
  apply elim_ex; intro s7; simp only [sepConj_assoc]
  apply elim_ex; intro s8; simp only [sepConj_assoc]
  apply elim_ex; intro s9; simp only [sepConj_assoc]
  apply elim_ex; intro s10; simp only [sepConj_assoc]
  apply elim_ex; intro s11; simp only [sepConj_assoc]
  apply elim_ex; intro s12; simp only [sepConj_assoc]
  apply elim_ex; intro s13; simp only [sepConj_assoc]
  apply elim_ex; intro s14; simp only [sepConj_assoc]
  apply elim_ex; intro s15; simp only [sepConj_assoc]
  apply skip_atom; simp only [sepConj_assoc]
  have h' := h s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s3
  simpa only [sepConj_assoc] using h'

end ApplyFrameFacts

theorem otrApplyRaw_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) :
    OtrApplyRawExtOk b A ext := by
  unfold OtrApplyRawExtOk otrApplyRawSpec
  have hshim := hA.shim_ok_at
    "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state"
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state")) (by rw [(ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state"), (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := hA.alloc_ok_at
    "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state"
    (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state")) (by rw [(ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state"), (ls_stub% "__rustc::__rust_alloc")])
  have hdealloc := hA.dealloc_ok_at
    "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state"
    (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state")) (by rw [(ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state"), (ls_stub% "__rustc::__rust_dealloc")])
  have hpanic := panic_at_handle_error_ext b ext
    "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state"
    (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state")) (by rw [(ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state"), (ls_stub% "alloc::raw_vec::handle_error")])
  code_fetches libsignalSessionCode libsignalSessionBin b
    (Rust.withPanics ext) (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state") (num% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state")) 316
  have htripleRatchetProgAt : tripleRatchetProgAtExt b ext =
      libsignalSessionCode.rebase b (Rust.withPanics ext) := rfl
  have hName : otrApplyName =
      "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state" := rfl
  rw [htripleRatchetProgAt] at hshim halloc hdealloc hpanic ⊢
  rw [hName]
  clear htripleRatchetProgAt hName
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state" = entry
  conv => arg 3; arg 2; ext x s0 sf; rw [sepExists_sepConj_left, sepExists_sepConj_right]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨o, pqCap, pqPtr, ot, ss, G, st⟩ := x
  dsimp only at *
  have hsc_some : ∃ sc, st.senderChain = some sc := Option.isSome_iff_exists.mp h
  obtain ⟨sc, hsc⟩ := hsc_some
  apply SepWPp.of_sepWP (mid := entry + bv% (60))
  refine ApplyFrameFacts.sepWP_unpack_stackAt_otrApply s0.sp (by sep_focus)
    fun s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s3 => ?_
  refine SepWP.fold (otrAt_apply_split A o pqCap pqPtr ot) (by sep_focus) ?_
  refine SepWP.fold (sessionStateAt_sender_some A ss G st sc hsc) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro sg
  refine SepWP.focus_pure (by sep_focus) fun hGs => ?_
  let sg_id : SenderChainGhost := { sg with ck := sg.ck }
  have hG_eq : G = { G with sender := some sg_id, pq := G.pq } := by
    cases G; dsimp only at hGs; subst hGs; rfl
  let sc_id : SenderChain := { sc with chainKey := sc.chainKey }
  have hst_eq : st = { st with senderChain := some sc_id, pqRatchetState := st.pqRatchetState } := by
    cases st; dsimp only at hsc; subst hsc; rfl
  conv =>
    arg 4
    rw [hG_eq, hst_eq,
      sessionStateAt_eq_apply A ss G st sg sc G.pq st.pqRatchetState sg.ck sc.chainKey]
  clear hG_eq hst_eq sg_id sc_id
  refine SepWP.fold (vecU8Buf_cap_lt A sg.srk.cap sg.srk.ptr sg.srk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hsrk_cap => ?_
  refine SepWP.fold (vecU8Buf_dealloc_32 A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key)
    (keyToBytes32_length _)) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hck_bounds => ?_
  refine SepWP.fold (vecU8Buf_dealloc A G.pq.cap G.pq.ptr st.pqRatchetState) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpq_bounds => ?_
  wp_steps
  wp_call hshim ()
  wp_steps
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  wp_call halloc (32, 1)
  apply SepWP.done (by exact hpc_sf_1) (by exact hrun_sf_1)
  by_cases hck_null : sf_1.readReg64 Reg.x0 = 0#64
  · -- Allocation failed (`x0 = 0`): branch to `+0x130` (`handle_error` panic)
    have hck_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := beq_iff_eq.mpr hck_null
    have hck_eq0 : sf_1.readReg64 Reg.x0 = 0 := hck_null
    rw [ite_eq_left_iff.mpr (fun h => absurd hck_eq0 h)]
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state"))
    refine SepWP.focus_pure (by sep_focus) fun htr => ?_
    wp_steps
    apply SepWP.done (by rfl) (by simp only [State.status_setPC, State.status_writeReg64, hrun_sf_1])
    refine SepWPp.panic (by simp only [State.status_setPC, State.status_writeReg64, hrun_sf_1])
      (by simpa only [State.pc_setPC, BitVec.ofNat_eq_ofNat] using hpanic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, State.trace_setPC, State.trace_writeReg64, htr, h_3])) hm
  · -- Allocation succeeded (`x0 ≠ 0`)
    have hck_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hck_null
    have hck_ne0 : sf_1.readReg64 Reg.x0 ≠ 0 := hck_null
    rw [ite_eq_right_iff.mpr (fun h => absurd h hck_ne0)]
    apply SepWPp.of_sepWP_ret
    refine SepWP.focus_pure (by sep_focus) fun htr1 => ?_
    rcases htr1 with ⟨_, htr1⟩
    wp_simp_pre only [memRegion_32_cells,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w2
    apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w0
    have hsrk_ne : (sg.srk.cap + 1#64 == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; bv_omega
    have hck_hi : ConditionHolds CondCode.HI (addsPState64 (sg.ck.cap - 1#64) 3#64) = false :=
      addsPState64_hi_false hck_bounds
    wp_steps
    wp_call hdealloc (sg.ck.ptr, sg.ck.cap.toNat, 1)
    wp_steps
    let sc' : SenderChain := { sc with chainKey := ot.senderChainKey }
    wp_if hpq_beq
    · -- Old `G.pq.cap = 0`: skip `__rust_dealloc`
      have hpq0 : G.pq.cap = (0 : BitVec 64) := hpq_beq
      rw [ite_eq_left_iff.mpr (fun h => absurd hpq0 h)]
      wp_steps
      rw [hsp_sf, h_4]
      refine SepWP.fold (vecU8Buf_of_cells_32 A (sf_1.readReg64 Reg.x0) ot.senderChainKey.key hck_null)
        (by sep_focus) ?_
      refine SepWP.fold (otr_fold_memRegion o pqCap pqPtr
        (BitVec.ofNat 64 ot.pqrState.length)
        (pack64 ((keyToBytes32 ot.senderChainKey.key).take 8))
        (pack64 (((keyToBytes32 ot.senderChainKey.key).drop 8).take 8))
        (pack64 (((keyToBytes32 ot.senderChainKey.key).drop 16).take 8))
        (pack64 ((keyToBytes32 ot.senderChainKey.key).drop 24))
        ot.senderChainKey.index) (by sep_focus) ?_
      refine SepWP.fold (stackAt_otrApply_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        (by sep_focus) ?_
      apply SepWP.instantiate_post_exists (afterOtrApply G sg (sf_1.readReg64 Reg.x0) pqCap pqPtr)
      have hpost_ss :
          sessionStateAt A ss (afterOtrApply G sg (sf_1.readReg64 Reg.x0) pqCap pqPtr)
            (ot.applyToSessionState st) =
          sessionStateAt A ss
            { G with sender := some ({ sg with ck := ⟨32#64, sf_1.readReg64 Reg.x0⟩ }), pq := ⟨pqCap, pqPtr⟩ }
            { st with senderChain := some sc', pqRatchetState := ot.pqrState } := by
        simp [afterOtrApply, OutgoingTripleRatchet.applyToSessionState, hsc, sc']
      rw [hpost_ss, sessionStateAt_eq_apply A ss G st sg sc ⟨pqCap, pqPtr⟩ ot.pqrState
        ⟨32#64, sf_1.readReg64 Reg.x0⟩ ot.senderChainKey]
      have hrel := applyRel_afterOtrApply G sg hGs (sf_1.readReg64 Reg.x0) pqCap pqPtr
      wp_done
    · -- Old `G.pq.cap ≠ 0`: call `__rust_dealloc`
      have hpq0 : G.pq.cap ≠ (0 : BitVec 64) := hpq_beq
      rw [ite_eq_right_iff.mpr (fun h => absurd h hpq0)]
      wp_steps
      wp_call hdealloc (G.pq.ptr, G.pq.cap.toNat, 1)
      wp_steps
      rw [hsp_sf_1, hsp_sf, h_4]
      refine SepWP.fold (vecU8Buf_of_cells_32 A (sf_1.readReg64 Reg.x0) ot.senderChainKey.key hck_null)
        (by sep_focus) ?_
      refine SepWP.fold (otr_fold_memRegion o pqCap pqPtr
        (BitVec.ofNat 64 ot.pqrState.length)
        (pack64 ((keyToBytes32 ot.senderChainKey.key).take 8))
        (pack64 (((keyToBytes32 ot.senderChainKey.key).drop 8).take 8))
        (pack64 (((keyToBytes32 ot.senderChainKey.key).drop 16).take 8))
        (pack64 ((keyToBytes32 ot.senderChainKey.key).drop 24))
        ot.senderChainKey.index) (by sep_focus) ?_
      refine SepWP.fold (stackAt_otrApply_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        (by sep_focus) ?_
      apply SepWP.instantiate_post_exists (afterOtrApply G sg (sf_1.readReg64 Reg.x0) pqCap pqPtr)
      have hpost_ss :
          sessionStateAt A ss (afterOtrApply G sg (sf_1.readReg64 Reg.x0) pqCap pqPtr)
            (ot.applyToSessionState st) =
          sessionStateAt A ss
            { G with sender := some ({ sg with ck := ⟨32#64, sf_1.readReg64 Reg.x0⟩ }), pq := ⟨pqCap, pqPtr⟩ }
            { st with senderChain := some sc', pqRatchetState := ot.pqrState } := by
        simp [afterOtrApply, OutgoingTripleRatchet.applyToSessionState, hsc, sc']
      rw [hpost_ss, sessionStateAt_eq_apply A ss G st sg sc ⟨pqCap, pqPtr⟩ ot.pqrState
        ⟨32#64, sf_1.readReg64 Reg.x0⟩ ot.senderChainKey]
      have hrel := applyRel_afterOtrApply G sg hGs (sf_1.readReg64 Reg.x0) pqCap pqPtr
      wp_done

theorem otrApplyRaw_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) :
    OtrApplyRawOk b C A ctl abs :=
  otrApplyRaw_ok_ext b A (tripleRatchetExterns C ctl abs)
    (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA)

/-- Split the 64 KiB `smallRootStack` into the 61312-byte unused prefix and the 4224-byte
`otrApplyInternalStack` frame. -/
theorem smallRootStack_split_otrApply (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 smallRootStack) smallRootStack =
      (memRegion (sp - 65536#64) 61312 ∗
       memRegion (sp - BitVec.ofNat 64 otrApplyInternalStack) otrApplyInternalStack) := by
  change memRegion (sp - 65536#64) (61312 + 4224) =
    (memRegion (sp - 65536#64) 61312 ∗ memRegion (sp - 4224#64) 4224)
  rw [memRegion_split (sp - 65536#64) 61312 4224 (by decide)]
  have h1 : sp - 65536#64 + BitVec.ofNat 64 61312 = sp - 4224#64 := by bv_arith
  rw [h1]

theorem otrApply_ok_ext (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext) : OtrApplyExtOk img A ext := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  rw [otrApplySpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_, hpre⟩
  have hpre_eq :
      ((⌜s0.readReg64 .x0 = x.o ∧ s0.readReg64 .x1 = x.ss ∧ x.st.senderChain.isSome⌝ ∗
          otrAt A x.o x.pqCap x.pqPtr x.ot ∗ sessionStateAt A x.ss x.G x.st ∗ logOff img ∗
          stackAt s0.sp smallRootStack ∗ A.pool) ∗ R) =
      ((otrApplyRawSpec A).pre x s0 ∗
        ((logOff img ∗ memRegion (s0.sp - 65536#64) 61312) ∗ R)) := by
    dsimp only [otrApplyRawSpec, stackAt]
    rw [smallRootStack_split_otrApply]
    ac_rfl
  refine (otrApplyRaw_ok_ext img.base A ext hA).mono_outcome x
    ((logOff img ∗ memRegion (s0.sp - 65536#64) 61312) ∗ R)
    s0 hpc hrun (hpre_eq ▸ hpre) hsp fun sf hout => ?_
  rcases hout with ⟨h1, h2, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · have hpost_eq :
        ((otrApplyRawSpec A).post x s0 sf ∗
          ((logOff img ∗ memRegion (s0.sp - 65536#64) 61312) ∗ R)) =
        ((otrApplySpec A img).post x s0 sf ∗ R) := by
      dsimp only [otrApplyRawSpec, otrApplySpec, Spec.inImage, stackAt]
      rw [smallRootStack_split_otrApply]
      ac_rfl
    exact Or.inl ⟨h1, h2, hpost_eq ▸ hpost⟩
  · rw [← sepConj_assoc] at hpost
    exact Or.inr (Or.inl ⟨hpan, allowPanic_frame id hpost⟩)
  · exact (allowPanic_not_exited hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

theorem otrApply_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (h : TripleRatchetHooks C A S abs) : OtrApplyOk img C A ctl abs :=
  otrApply_ok_ext img A (tripleRatchetExterns C ctl abs)
    (AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs h.alloc)

/-! ## `AllocContractsX` (`extHookStack` = 16 KiB) variant -/

abbrev otrApplyInternalStackX : Nat := 0x80 + extHookStack

def otrApplyRawSpecX (A : RustAlloc) : Spec OtrApplyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.o ∧ s.readReg64 .x1 = x.ss ∧ x.st.senderChain.isSome⌝ ∗
      otrAt A x.o x.pqCap x.pqPtr x.ot ∗ sessionStateAt A x.ss x.G x.st ∗
      stackAt s.sp otrApplyInternalStackX ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ G' : SessionGhost, ⌜x.G.AfterOutgoingRatchetApply G' ∧ G'.pq = ⟨x.pqCap, x.pqPtr⟩⌝ ∗
        sessionStateAt A x.ss G' (x.ot.applyToSessionState x.st)) ∗
      memRegion x.o 200 ∗ stackAt s0.sp otrApplyInternalStackX ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem stackAt_otrApplyX (sp : BitVec 64) :
    stackAt sp otrApplyInternalStackX =
      stackAt (sp - 128#64) extHookStack ∗
      memRegion (sp - 128#64) 8 ∗
      (∃∗ s1 : BitVec 64, (sp - 120#64) ↦₆₄ s1) ∗
      (∃∗ s2 : BitVec 64, (sp - 112#64) ↦₆₄ s2) ∗
      memRegion (sp - 104#64) 4 ∗
      (∃∗ s3 : BitVec 32, (sp - 100#64) ↦₃₂ s3) ∗
      (∃∗ s4 : BitVec 64, (sp - 96#64) ↦₆₄ s4) ∗
      (∃∗ s5 : BitVec 64, (sp - 88#64) ↦₆₄ s5) ∗
      (∃∗ s6 : BitVec 64, (sp - 80#64) ↦₆₄ s6) ∗
      (∃∗ s7 : BitVec 64, (sp - 72#64) ↦₆₄ s7) ∗
      (∃∗ s8 : BitVec 64, (sp - 64#64) ↦₆₄ s8) ∗
      (∃∗ s9 : BitVec 64, (sp - 56#64) ↦₆₄ s9) ∗
      (∃∗ s10 : BitVec 64, (sp - 48#64) ↦₆₄ s10) ∗
      (∃∗ s11 : BitVec 64, (sp - 40#64) ↦₆₄ s11) ∗
      (∃∗ s12 : BitVec 64, (sp - 32#64) ↦₆₄ s12) ∗
      (∃∗ s13 : BitVec 64, (sp - 24#64) ↦₆₄ s13) ∗
      (∃∗ s14 : BitVec 64, (sp - 16#64) ↦₆₄ s14) ∗
      (∃∗ s15 : BitVec 64, (sp - 8#64) ↦₆₄ s15) := by
  show memRegion (sp - BitVec.ofNat 64 16512) 16512 = _
  rw [mr_cut' sp 16512 128 16384 128 16512 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 128 120 8 120 128 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 120 112 8 112 120 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 112 104 8 104 112 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 104 100 4 100 104 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 100 96 4 96 100 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 96 88 8 88 96 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 88 80 8 80 88 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 80 72 8 72 80 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 72 64 8 64 72 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 64 56 8 56 64 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 56 48 8 48 56 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 48 40 8 40 48 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 40 32 8 32 40 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 32 24 8 24 32 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 24 16 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 16 8 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  have hstk : memRegion (sp - BitVec.ofNat 64 16512) 16384 = stackAt (sp - 128#64) extHookStack := by
    simp only [stackAt, extHookStack]; congr 1; bv_omega
  rw [hstk, memRegion_four (sp - BitVec.ofNat 64 100)]
  simp only [memRegion_eight]

theorem stackAt_otrApplyX_fold (sp s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 : BitVec 64)
    (s3 : BitVec 32) :
    stackAt (sp - 128#64) extHookStack ∗
      memRegion (sp - 128#64) 8 ∗
      ((sp - 120#64) ↦₆₄ s1) ∗
      ((sp - 112#64) ↦₆₄ s2) ∗
      memRegion (sp - 104#64) 4 ∗
      ((sp - 100#64) ↦₃₂ s3) ∗
      ((sp - 96#64) ↦₆₄ s4) ∗
      ((sp - 88#64) ↦₆₄ s5) ∗
      ((sp - 80#64) ↦₆₄ s6) ∗
      ((sp - 72#64) ↦₆₄ s7) ∗
      ((sp - 64#64) ↦₆₄ s8) ∗
      ((sp - 56#64) ↦₆₄ s9) ∗
      ((sp - 48#64) ↦₆₄ s10) ∗
      ((sp - 40#64) ↦₆₄ s11) ∗
      ((sp - 32#64) ↦₆₄ s12) ∗
      ((sp - 24#64) ↦₆₄ s13) ∗
      ((sp - 16#64) ↦₆₄ s14) ∗
      ((sp - 8#64) ↦₆₄ s15) ⊢
    stackAt sp otrApplyInternalStackX := by
  rw [stackAt_otrApplyX sp]
  refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) ?_)
  refine sepConj_mono (Entails.sepExists_intro s1) (sepConj_mono (Entails.sepExists_intro s2) ?_)
  refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.sepExists_intro s3) ?_)
  refine sepConj_mono (Entails.sepExists_intro s4) (sepConj_mono (Entails.sepExists_intro s5) ?_)
  refine sepConj_mono (Entails.sepExists_intro s6) (sepConj_mono (Entails.sepExists_intro s7) ?_)
  refine sepConj_mono (Entails.sepExists_intro s8) (sepConj_mono (Entails.sepExists_intro s9) ?_)
  refine sepConj_mono (Entails.sepExists_intro s10) (sepConj_mono (Entails.sepExists_intro s11) ?_)
  refine sepConj_mono (Entails.sepExists_intro s12) (sepConj_mono (Entails.sepExists_intro s13) ?_)
  exact sepConj_mono (Entails.sepExists_intro s14) (Entails.sepExists_intro s15)

namespace ApplyFrameFacts

theorem sepWP_unpack_stackAt_otrApplyX {prog : Program} {pc : BitVec 64} {s : State}
    (sp : BitVec 64) {P F : SepProp} {post : State → SepProp → Prop}
    (hf : P = stackAt sp otrApplyInternalStackX ∗ F)
    (h : ∀ (s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 : BitVec 64) (s3 : BitVec 32),
      SepWP prog pc s
        ((stackAt (sp - 128#64) extHookStack ∗
          memRegion (sp - 128#64) 8 ∗
          ((sp - 120#64) ↦₆₄ s1) ∗
          ((sp - 112#64) ↦₆₄ s2) ∗
          memRegion (sp - 104#64) 4 ∗
          ((sp - 100#64) ↦₃₂ s3) ∗
          ((sp - 96#64) ↦₆₄ s4) ∗
          ((sp - 88#64) ↦₆₄ s5) ∗
          ((sp - 80#64) ↦₆₄ s6) ∗
          ((sp - 72#64) ↦₆₄ s7) ∗
          ((sp - 64#64) ↦₆₄ s8) ∗
          ((sp - 56#64) ↦₆₄ s9) ∗
          ((sp - 48#64) ↦₆₄ s10) ∗
          ((sp - 40#64) ↦₆₄ s11) ∗
          ((sp - 32#64) ↦₆₄ s12) ∗
          ((sp - 24#64) ↦₆₄ s13) ∗
          ((sp - 16#64) ↦₆₄ s14) ∗
          ((sp - 8#64) ↦₆₄ s15)) ∗ F) post) :
    SepWP prog pc s P post := by
  rw [hf, stackAt_otrApplyX sp]
  simp only [sepConj_assoc]
  apply skip_atom; simp only [sepConj_assoc]
  apply skip_atom; simp only [sepConj_assoc]
  apply elim_ex; intro s1; simp only [sepConj_assoc]
  apply elim_ex; intro s2; simp only [sepConj_assoc]
  apply skip_atom; simp only [sepConj_assoc]
  apply elim_ex; intro s3; simp only [sepConj_assoc]
  apply elim_ex; intro s4; simp only [sepConj_assoc]
  apply elim_ex; intro s5; simp only [sepConj_assoc]
  apply elim_ex; intro s6; simp only [sepConj_assoc]
  apply elim_ex; intro s7; simp only [sepConj_assoc]
  apply elim_ex; intro s8; simp only [sepConj_assoc]
  apply elim_ex; intro s9; simp only [sepConj_assoc]
  apply elim_ex; intro s10; simp only [sepConj_assoc]
  apply elim_ex; intro s11; simp only [sepConj_assoc]
  apply elim_ex; intro s12; simp only [sepConj_assoc]
  apply elim_ex; intro s13; simp only [sepConj_assoc]
  apply elim_ex; intro s14; simp only [sepConj_assoc]
  apply elim_ex; intro s15; simp only [sepConj_assoc]
  apply skip_atom; simp only [sepConj_assoc]
  have h' := h s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s3
  simpa only [sepConj_assoc] using h'

end ApplyFrameFacts

theorem smallRootStack_split_otrApplyX (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 smallRootStack) smallRootStack =
      (memRegion (sp - 65536#64) 49024 ∗
       memRegion (sp - BitVec.ofNat 64 otrApplyInternalStackX) otrApplyInternalStackX) := by
  change memRegion (sp - 65536#64) (49024 + 16512) =
    (memRegion (sp - 65536#64) 49024 ∗ memRegion (sp - 16512#64) 16512)
  rw [memRegion_split (sp - 65536#64) 49024 16512 (by decide)]
  have h1 : sp - 65536#64 + BitVec.ofNat 64 49024 = sp - 16512#64 := by bv_arith
  rw [h1]

/-! ## Relocatable `[LibsignalPlacement]` contracts -/

/-- Relocatable root-level specification of `OTR::apply_to_session_state`. -/
def otrApplyPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec OtrApplyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.o ∧ s.readReg64 .x1 = x.ss ∧ x.st.senderChain.isSome⌝ ∗
      otrAt A x.o x.pqCap x.pqPtr x.ot ∗ sessionStateAt A x.ss x.G x.st ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s.sp smallRootStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ G' : SessionGhost, ⌜x.G.AfterOutgoingRatchetApply G' ∧ G'.pq = ⟨x.pqCap, x.pqPtr⟩⌝ ∗
        sessionStateAt A x.ss G' (x.ot.applyToSessionState x.st)) ∗
      memRegion x.o 200 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp smallRootStack ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable `OTR::apply_to_session_state` meets `otrApplyRawSpec A` from hook
`subroutine_ok` contracts. -/
theorem otrApplyRaw_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_20).rebase (blkPl_20).base H)
      (lsρ lsRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_20).rebase (blkPl_20).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_20).rebase (blkPl_20).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hpanic : ((blkPC_20).rebase (blkPl_20).base H).externAt?
      (lsρ lsHandleErrorSym) = some Rust.panicked) :
    subroutine_ok ((blkPC_20).rebase (blkPl_20).base H) (blkPl_20).base
      (otrApplyRawSpec A) := by
  unfold otrApplyRawSpec
  conv => arg 3; arg 2; ext x s0 sf; rw [sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  obtain ⟨o, pqCap, pqPtr, ot, ss, G, st⟩ := x
  dsimp only at *
  have hsc_some : ∃ sc, st.senderChain = some sc := Option.isSome_iff_exists.mp h
  obtain ⟨sc, hsc⟩ := hsc_some
  apply SepWPp.of_sepWP (mid := (blkPl_20).base + 60#64)
  refine ApplyFrameFacts.sepWP_unpack_stackAt_otrApply s0.sp (by sep_focus)
    fun s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s3 => ?_
  refine SepWP.fold (otrAt_apply_split A o pqCap pqPtr ot) (by sep_focus) ?_
  refine SepWP.fold (sessionStateAt_sender_some A ss G st sc hsc) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro sg
  refine SepWP.focus_pure (by sep_focus) fun hGs => ?_
  let sg_id : SenderChainGhost := { sg with ck := sg.ck }
  have hG_eq : G = { G with sender := some sg_id, pq := G.pq } := by
    cases G; dsimp only at hGs; subst hGs; rfl
  let sc_id : SenderChain := { sc with chainKey := sc.chainKey }
  have hst_eq : st = { st with senderChain := some sc_id, pqRatchetState := st.pqRatchetState } := by
    cases st; dsimp only at hsc; subst hsc; rfl
  conv =>
    arg 4
    rw [hG_eq, hst_eq,
      sessionStateAt_eq_apply A ss G st sg sc G.pq st.pqRatchetState sg.ck sc.chainKey]
  clear hG_eq hst_eq sg_id sc_id
  refine SepWP.fold (vecU8Buf_cap_lt A sg.srk.cap sg.srk.ptr sg.srk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hsrk_cap => ?_
  refine SepWP.fold (vecU8Buf_dealloc_32 A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key)
    (keyToBytes32_length _)) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hck_bounds => ?_
  refine SepWP.fold (vecU8Buf_dealloc A G.pq.cap G.pq.ptr st.pqRatchetState) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpq_bounds => ?_
  wp_steps
  wp_call hshim ()
  wp_steps
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  wp_call halloc (32, 1)
  apply SepWP.done (by exact hpc_sf_1) (by exact hrun_sf_1)
  by_cases hck_null : sf_1.readReg64 Reg.x0 = 0#64
  · have hck_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := beq_iff_eq.mpr hck_null
    have hck_eq0 : sf_1.readReg64 Reg.x0 = 0 := hck_null
    rw [ite_eq_left_iff.mpr (fun h => absurd hck_eq0 h)]
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    refine SepWP.focus_pure (by sep_focus) fun htr => ?_
    wp_steps
    apply SepWP.done (by rfl) (by simp only [State.status_setPC, State.status_writeReg64, hrun_sf_1])
    refine SepWPp.panic (by simp only [State.status_setPC, State.status_writeReg64, hrun_sf_1])
      (by simpa only [State.pc_setPC] using hpanic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, State.trace_setPC, State.trace_writeReg64, htr, h_3])) hm
  · have hck_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hck_null
    have hck_ne0 : sf_1.readReg64 Reg.x0 ≠ 0 := hck_null
    rw [ite_eq_right_iff.mpr (fun h => absurd h hck_ne0)]
    apply SepWPp.of_sepWP_ret
    refine SepWP.focus_pure (by sep_focus) fun htr1 => ?_
    rcases htr1 with ⟨_, htr1⟩
    wp_simp_pre only [memRegion_32_cells,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w2
    apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w0
    have hsrk_ne : (sg.srk.cap + 1#64 == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; bv_omega
    have hck_hi : ConditionHolds CondCode.HI (addsPState64 (sg.ck.cap - 1#64) 3#64) = false :=
      addsPState64_hi_false hck_bounds
    wp_steps
    wp_call hdealloc (sg.ck.ptr, sg.ck.cap.toNat, 1)
    wp_steps
    let sc' : SenderChain := { sc with chainKey := ot.senderChainKey }
    wp_if hpq_beq
    · have hpq0 : G.pq.cap = (0 : BitVec 64) := hpq_beq
      rw [ite_eq_left_iff.mpr (fun h => absurd hpq0 h)]
      wp_steps
      rw [hsp_sf, h_4]
      refine SepWP.fold (vecU8Buf_of_cells_32 A (sf_1.readReg64 Reg.x0) ot.senderChainKey.key hck_null)
        (by sep_focus) ?_
      refine SepWP.fold (otr_fold_memRegion o pqCap pqPtr
        (BitVec.ofNat 64 ot.pqrState.length)
        (pack64 ((keyToBytes32 ot.senderChainKey.key).take 8))
        (pack64 (((keyToBytes32 ot.senderChainKey.key).drop 8).take 8))
        (pack64 (((keyToBytes32 ot.senderChainKey.key).drop 16).take 8))
        (pack64 ((keyToBytes32 ot.senderChainKey.key).drop 24))
        ot.senderChainKey.index) (by sep_focus) ?_
      refine SepWP.fold (stackAt_otrApply_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        (by sep_focus) ?_
      apply SepWP.instantiate_post_exists (afterOtrApply G sg (sf_1.readReg64 Reg.x0) pqCap pqPtr)
      have hpost_ss :
          sessionStateAt A ss (afterOtrApply G sg (sf_1.readReg64 Reg.x0) pqCap pqPtr)
            (ot.applyToSessionState st) =
          sessionStateAt A ss
            { G with sender := some ({ sg with ck := ⟨32#64, sf_1.readReg64 Reg.x0⟩ }), pq := ⟨pqCap, pqPtr⟩ }
            { st with senderChain := some sc', pqRatchetState := ot.pqrState } := by
        simp [afterOtrApply, OutgoingTripleRatchet.applyToSessionState, hsc, sc']
      rw [hpost_ss, sessionStateAt_eq_apply A ss G st sg sc ⟨pqCap, pqPtr⟩ ot.pqrState
        ⟨32#64, sf_1.readReg64 Reg.x0⟩ ot.senderChainKey]
      have hrel := applyRel_afterOtrApply G sg hGs (sf_1.readReg64 Reg.x0) pqCap pqPtr
      wp_done
    · have hpq0 : G.pq.cap ≠ (0 : BitVec 64) := hpq_beq
      rw [ite_eq_right_iff.mpr (fun h => absurd h hpq0)]
      wp_steps
      wp_call hdealloc (G.pq.ptr, G.pq.cap.toNat, 1)
      wp_steps
      rw [hsp_sf_1, hsp_sf, h_4]
      refine SepWP.fold (vecU8Buf_of_cells_32 A (sf_1.readReg64 Reg.x0) ot.senderChainKey.key hck_null)
        (by sep_focus) ?_
      refine SepWP.fold (otr_fold_memRegion o pqCap pqPtr
        (BitVec.ofNat 64 ot.pqrState.length)
        (pack64 ((keyToBytes32 ot.senderChainKey.key).take 8))
        (pack64 (((keyToBytes32 ot.senderChainKey.key).drop 8).take 8))
        (pack64 (((keyToBytes32 ot.senderChainKey.key).drop 16).take 8))
        (pack64 ((keyToBytes32 ot.senderChainKey.key).drop 24))
        ot.senderChainKey.index) (by sep_focus) ?_
      refine SepWP.fold (stackAt_otrApply_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        (by sep_focus) ?_
      apply SepWP.instantiate_post_exists (afterOtrApply G sg (sf_1.readReg64 Reg.x0) pqCap pqPtr)
      have hpost_ss :
          sessionStateAt A ss (afterOtrApply G sg (sf_1.readReg64 Reg.x0) pqCap pqPtr)
            (ot.applyToSessionState st) =
          sessionStateAt A ss
            { G with sender := some ({ sg with ck := ⟨32#64, sf_1.readReg64 Reg.x0⟩ }), pq := ⟨pqCap, pqPtr⟩ }
            { st with senderChain := some sc', pqRatchetState := ot.pqrState } := by
        simp [afterOtrApply, OutgoingTripleRatchet.applyToSessionState, hsc, sc']
      rw [hpost_ss, sessionStateAt_eq_apply A ss G st sg sc ⟨pqCap, pqPtr⟩ ot.pqrState
        ⟨32#64, sf_1.readReg64 Reg.x0⟩ ot.senderChainKey]
      have hrel := applyRel_afterOtrApply G sg hGs (sf_1.readReg64 Reg.x0) pqCap pqPtr
      wp_done

theorem otrApplyRaw_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (h_panic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_20).rebase (blkPl_20).base H) (blkPl_20).base
      (otrApplyRawSpec A) := by
  have hpanic : ((blkPC_20).rebase (blkPl_20).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked := by
    rw [ls_externAt?_of_mem (prog := (blkPC_20).rebase (blkPl_20).base H) (sym := lsHandleErrorSym)]
    exact h_panic
  exact otrApplyRaw_placed_ok_of_contracts
    (ls_hook_ok_of_mem h_shim) (ls_hook_ok_of_mem h_alloc)
    (ls_hook_ok_of_mem h_dealloc) hpanic

theorem otrApply_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (h_panic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_20).rebase (blkPl_20).base H) (blkPl_20).base
      (otrApplyPlacedSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre_eq :
      (otrApplyPlacedSpec A).pre x s0 ∗ R =
      (otrApplyRawSpec A).pre x s0 ∗
        (((lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 65536#64) 61312) ∗ R) := by
    dsimp only [otrApplyPlacedSpec, otrApplyRawSpec, stackAt]
    rw [smallRootStack_split_otrApply]
    ac_rfl
  refine (otrApplyRaw_placed_ok h_shim h_alloc h_dealloc h_panic).mono_outcome x
    (((lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 65536#64) 61312) ∗ R)
    s0 hpc hrun (hpre_eq ▸ hpre) hsp fun sf hout => ?_
  rcases hout with ⟨h1, h2, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · have hpost_eq :
        ((otrApplyRawSpec A).post x s0 sf ∗
          (((lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 65536#64) 61312) ∗ R)) =
        ((otrApplyPlacedSpec A).post x s0 sf ∗ R) := by
      dsimp only [otrApplyRawSpec, otrApplyPlacedSpec, stackAt]
      rw [smallRootStack_split_otrApply]
      ac_rfl
    exact Or.inl ⟨h1, h2, hpost_eq ▸ hpost⟩
  · rw [← sepConj_assoc] at hpost
    exact Or.inr (Or.inl ⟨hpan, allowPanic_frame id hpost⟩)
  · exact (allowPanic_not_exited hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

end CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
