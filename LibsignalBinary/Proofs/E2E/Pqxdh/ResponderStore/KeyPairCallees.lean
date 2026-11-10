/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.BV.ReflectROBDD -- shake: keep
import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.Fetch
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Frame -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonical
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PrivateKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WPp

/-!
# `KeyPair`, `PreKeyRecord`, and `KeySerde` Callee Proofs

Proves `subroutine_ok` contracts on `tripleRatchetProgAt` and under `[LibsignalPlacement]` for the
curve and ML-KEM key-pair constructors, `KeySerde::serialize` implementations, `PreKeyRecord::new` /
`key_pair`, and tail-call `__rust_dealloc` helpers used by the PQXDH responder store.
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.ResponderStore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetApply

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem bv_sub_add_lit' (x a b : BitVec 64) :
    x - a + b = x - (a - b) := by bv_omega

theorem stackAt_split_top (sp : BitVec 64) (m n : Nat) (h : m + n ≤ 2 ^ 64) :
    stackAt sp (m + n) =
      memRegion (sp - BitVec.ofNat 64 (m + n)) m ∗ stackAt sp n := by
  simp only [stackAt]
  rw [memRegion_split _ m n h]
  have e : sp - BitVec.ofNat 64 (m + n) + BitVec.ofNat 64 m = sp - BitVec.ofNat 64 n := by
    rw [Nat.add_comm, BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [e]

theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem pointsToBytes_cons_fold (a : BitVec 64) (b0 : BitVec 8) (bs : List (BitVec 8)) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ bs)) ⊢ (a ↦ₛ (b0 :: bs)) :=
  Entails.of_eq (pointsToBytes_cons a b0 bs).symm

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_add_lit' BitVec.toNat_zero

set_option maxHeartbeats 200000 in
theorem subroutine_ok_rel2_trap {α : Type} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {spec : Spec α} {callee name : String} {offc off k : Nat}
    (h : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr callee) spec)
    (hc : libsignalSessionCode.fnOff callee = offc) (hfn : libsignalSessionCode.fnOff name = off)
    (hk : (off + k) % 2 ^ 64 = offc) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) spec := by
  have hrel : (trTrapProgAt b C abs).fnAddr callee =
      (trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, hc, BitVec.add_assoc,
      ← BitVec.ofNat_add]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, hk, ← hk, Nat.mod_mod]
  rwa [hrel] at h

theorem subroutine_ok_rel2 {α : Type} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {spec : Spec α} {callee name : String} {offc off k : Nat}
    (h : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr callee) spec)
    (hc : libsignalSessionCode.fnOff callee = offc) (hfn : libsignalSessionCode.fnOff name = off)
    (hk : (off + k) % 2 ^ 64 = offc) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) spec := by
  have hrel : (tripleRatchetProgAt b C ctl abs).fnAddr callee =
      (tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, hc, BitVec.add_assoc,
      ← BitVec.ofNat_add]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, hk, ← hk, Nat.mod_mod]
  rwa [hrel] at h

/-! ## Byte-Level Normalization Helpers for `curve::KeyPair` -/

def clampBv8List (l : List (BitVec 8)) : List (BitVec 8) :=
  (l.take 1).map (fun b => b &&& 0xf8#8) ++
    (l.drop 1).take 30 ++
    ((l.drop 31).take 1).map (fun b => (b &&& 0x7f#8) ||| 0x40#8)

theorem clampBv8List_length {l : List (BitVec 8)} (hl : l.length = 32) :
    (clampBv8List l).length = 32 := by
  simp [clampBv8List, hl]

open CryptoVerification.E2E.Pqxdh.Shared (zext64_bv8_setWidth_8)
private abbrev vecU8 := @CryptoVerification.RustHeap.vecU8
attribute [local simp, local arm64_norm, local wp_norm]
  CryptoVerification.E2E.Pqxdh.Shared.zext64_bv16_setWidth_8 zext64_bv8_setWidth_8
@[local simp, local arm64_norm, local wp_norm]
theorem zext64_bv16_setWidth_16 (w : BitVec 16) :
    (w.zeroExtend 64).setWidth 16 = w := by bv_slice
@[local simp, local arm64_norm, local wp_norm]
theorem zext64_bv16_setWidth_32 (w : BitVec 16) :
    (w.zeroExtend 64).setWidth 32 = w.zeroExtend 32 := by bv_slice
@[local simp, local arm64_norm, local wp_norm]
theorem zext32_bv16_setWidth_8 (b0 b1 : BitVec 8) :
    ((b1 ++ b0).zeroExtend 32).setWidth 8 = b0 := by bv_slice
@[local simp, local arm64_norm, local wp_norm]
theorem zext32_bv16_setWidth_16 (w : BitVec 16) :
    (w.zeroExtend 32).setWidth 16 = w := by bv_slice

@[local simp, local arm64_norm, local wp_norm]
theorem clamp_lo_byte_norm (b0 : BitVec 8) :
    (((b0.zeroExtend 32 &&& 4294967288#32).zeroExtend 64).setWidth 8) = b0 &&& 0xf8#8 := by
  bv_slice

@[local simp, local arm64_norm, local wp_norm]
theorem clamp_lo_byte_norm' (b0 : BitVec 8) :
    (((b0.zeroExtend 64).setWidth 32 &&& 4294967288#32).zeroExtend 64).setWidth 8 =
      b0 &&& 0xf8#8 := by
  bv_slice

@[local simp, local arm64_norm, local wp_norm]
theorem clamp_hi_byte_norm (b31 : BitVec 8) :
    ((((0x40#32 &&& 4294967232#32) ||| (b31.zeroExtend 32 &&& 0x3f#32)).zeroExtend 64).setWidth 8) =
      (b31 &&& 0x7f#8) ||| 0x40#8 := by
  bv_slice

@[local simp, local arm64_norm, local wp_norm]
theorem clamp_hi_byte_norm' (b31 : BitVec 8) :
    ((((64#32 &&& 4294967232#32) |||
      (((b31.zeroExtend 64).setWidth 32) &&& 63#32)).zeroExtend 64).setWidth 8) =
      (b31 &&& 0x7f#8) ||| 0x40#8 := by
  bv_slice

@[local simp, local arm64_norm, local wp_norm]
theorem clamp_hi_byte_norm'' (b31 : BitVec 8) :
    ((64#32 ||| (b31.zeroExtend 32 &&& 63#32)).zeroExtend 64).setWidth 8 =
      (b31 &&& 0x7f#8) ||| 0x40#8 := by
  bv_slice

@[local simp, local arm64_norm, local wp_norm]
theorem clamp_hi_bfm_norm (b31 : BitVec 8) :
    ((64#64 ||| (b31.zeroExtend 64 >>> 0 &&& 63#64)).setWidth 32).zeroExtend 64 =
      ((b31 &&& 0x7f#8) ||| 0x40#8).zeroExtend 64 := by
  bv_slice

private theorem bv64_mask_low32_orr_zext32_32 (w_hi w_lo u : BitVec 32) :
    ((w_hi ++ w_lo) &&& 18446744069414584320#64) ||| u.zeroExtend 64 = w_hi ++ u := by
  bv_slice

@[local simp, local arm64_norm, local wp_norm]
theorem bv64_mask_low32_orr_zext32
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 : BitVec 8) :
    ((a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0) &&& 18446744069414584320#64) |||
      (b3 ++ b2 ++ b1 ++ b0).zeroExtend 64 =
      a7 ++ a6 ++ a5 ++ a4 ++ b3 ++ b2 ++ b1 ++ b0 := by
  have h1 : a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0 =
      (a7 ++ a6 ++ a5 ++ a4) ++ (a3 ++ a2 ++ a1 ++ a0) := by bv_slice
  have h2 : a7 ++ a6 ++ a5 ++ a4 ++ b3 ++ b2 ++ b1 ++ b0 =
      (a7 ++ a6 ++ a5 ++ a4) ++ (b3 ++ b2 ++ b1 ++ b0) := by bv_slice
  rw [h1, h2]
  exact bv64_mask_low32_orr_zext32_32
    (a7 ++ a6 ++ a5 ++ a4) (a3 ++ a2 ++ a1 ++ a0) (b3 ++ b2 ++ b1 ++ b0)

private theorem bv64_mask_high32_orr_lsl32_32 (w_hi w_lo u : BitVec 32) :
    ((w_hi ++ w_lo) &&& 4294967295#64) ||| (u.zeroExtend 64 <<< 32) = u ++ w_lo := by
  bv_slice

@[local simp, local arm64_norm, local wp_norm]
theorem bv64_mask_high32_orr_lsl32
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 : BitVec 8) :
    ((a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0) &&& 4294967295#64) |||
      ((b3 ++ b2 ++ b1 ++ b0).zeroExtend 64 <<< 32) =
      b3 ++ b2 ++ b1 ++ b0 ++ a3 ++ a2 ++ a1 ++ a0 := by
  have h1 : a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0 =
      (a7 ++ a6 ++ a5 ++ a4) ++ (a3 ++ a2 ++ a1 ++ a0) := by bv_slice
  have h2 : b3 ++ b2 ++ b1 ++ b0 ++ a3 ++ a2 ++ a1 ++ a0 =
      (b3 ++ b2 ++ b1 ++ b0) ++ (a3 ++ a2 ++ a1 ++ a0) := by bv_slice
  rw [h1, h2]
  exact bv64_mask_high32_orr_lsl32_32
    (a7 ++ a6 ++ a5 ++ a4) (a3 ++ a2 ++ a1 ++ a0) (b3 ++ b2 ++ b1 ++ b0)

private theorem bv64_mask_low16_orr_zext16_16 (w_hi : BitVec 48) (w_lo u : BitVec 16) :
    ((w_hi ++ w_lo) &&& 18446744073709486080#64) ||| u.zeroExtend 64 = w_hi ++ u := by
  bv_slice

@[local simp, local arm64_norm, local wp_norm]
theorem bv64_mask_low16_orr_zext16
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 : BitVec 8) :
    ((a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0) &&& 18446744073709486080#64) |||
      (b1 ++ b0).zeroExtend 64 =
      a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ b1 ++ b0 := by
  have h1 : a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0 =
      (a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2) ++ (a1 ++ a0) := by bv_slice
  have h2 : a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ b1 ++ b0 =
      (a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2) ++ (b1 ++ b0) := by bv_slice
  rw [h1, h2]
  exact bv64_mask_low16_orr_zext16_16 (a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2) (a1 ++ a0) (b1 ++ b0)

def bytes32At (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
     b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8) : SepProp :=
  (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
  ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7) ∗
  ((a + 8#64) ↦₈ b8) ∗ ((a + 9#64) ↦₈ b9) ∗ ((a + 10#64) ↦₈ b10) ∗ ((a + 11#64) ↦₈ b11) ∗
  ((a + 12#64) ↦₈ b12) ∗ ((a + 13#64) ↦₈ b13) ∗ ((a + 14#64) ↦₈ b14) ∗ ((a + 15#64) ↦₈ b15) ∗
  ((a + 16#64) ↦₈ b16) ∗ ((a + 17#64) ↦₈ b17) ∗ ((a + 18#64) ↦₈ b18) ∗ ((a + 19#64) ↦₈ b19) ∗
  ((a + 20#64) ↦₈ b20) ∗ ((a + 21#64) ↦₈ b21) ∗ ((a + 22#64) ↦₈ b22) ∗ ((a + 23#64) ↦₈ b23) ∗
  ((a + 24#64) ↦₈ b24) ∗ ((a + 25#64) ↦₈ b25) ∗ ((a + 26#64) ↦₈ b26) ∗ ((a + 27#64) ↦₈ b27) ∗
  ((a + 28#64) ↦₈ b28) ∗ ((a + 29#64) ↦₈ b29) ∗ ((a + 30#64) ↦₈ b30) ∗ ((a + 31#64) ↦₈ b31)

theorem exists_bytes32_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
       b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8),
      (∀ a : BitVec 64, (a ↦ₛ bs) =
        bytes32At a b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
          b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31) ∧
      (∀ a : BitVec 64, (a ↦ₛ clampBv8List bs) =
        bytes32At a (b0 &&& 0xf8#8) b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
          b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30
          ((b31 &&& 0x7f#8) ||| 0x40#8)) := by
  obtain ⟨u0, u1, u2, u3, hbs, hp⟩ := exists_unpack64_of_length_32 h
  rcases exists_bytes_of_bv64 u0 with ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩
  rcases exists_bytes_of_bv64 u1 with ⟨b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩
  rcases exists_bytes_of_bv64 u2 with ⟨b16, b17, b18, b19, b20, b21, b22, b23, rfl⟩
  rcases exists_bytes_of_bv64 u3 with ⟨b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
    b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31,
    fun a => ?_, fun a => ?_⟩
  · rw [hp]
    simp only [pointsTo64_eq_bytes8, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, bytes32At]
  · rw [hbs, unpack64_append_eq_list8, unpack64_append_eq_list8,
      unpack64_append_eq_list8, unpack64_append_eq_list8]
    dsimp only [clampBv8List, List.append_assoc, List.cons_append, List.nil_append,
      List.take, List.drop, List.map]
    simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
      BitVec.add_assoc, BitVec.reduceAdd, bytes32At]

theorem pointsTo64_eq_extract_bytes8 (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦₈ w.extractLsb' 0 8) ∗ ((a + 1#64) ↦₈ w.extractLsb' 8 8) ∗
      ((a + 2#64) ↦₈ w.extractLsb' 16 8) ∗ ((a + 3#64) ↦₈ w.extractLsb' 24 8) ∗
      ((a + 4#64) ↦₈ w.extractLsb' 32 8) ∗ ((a + 5#64) ↦₈ w.extractLsb' 40 8) ∗
      ((a + 6#64) ↦₈ w.extractLsb' 48 8) ∗ ((a + 7#64) ↦₈ w.extractLsb' 56 8) := by
  have hw : w = w.extractLsb' 56 8 ++ w.extractLsb' 48 8 ++ w.extractLsb' 40 8 ++
      w.extractLsb' 32 8 ++ w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++
      w.extractLsb' 8 8 ++ w.extractLsb' 0 8 := by bv_slice
  conv => lhs; rw [hw]
  exact pointsTo64_eq_bytes8 a _ _ _ _ _ _ _ _

theorem memRegion_65_cells (a : BitVec 64) :
    memRegion a 65 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ cells (a + 1#64) 8 := by
  rw [memRegion_split a 1 64 (by decide), ProofLib.memRegion_one,
    ProofLib.memRegion_cells (a + 1#64) 8 (by decide)]

/-! ## `curveKeyPairFromPubPriv_ok` (`0x3e738`) -/

abbrev curveKeyPairFromPubPrivName : String :=
  "<libsignal_core::curve::KeyPair>::from_public_and_private"

def curveKeyPairFromPubPrivOkSpec :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (pubPtr, pk, privPtr, sk, outPtr) s =>
    ⌜s.readReg64 .x0 = pubPtr ∧ s.readReg64 .x1 = 33#64 ∧
      s.readReg64 .x2 = privPtr ∧ s.readReg64 .x3 = 32#64 ∧
      s.readReg64 .x8 = outPtr ∧ pk.length = 32 ∧ sk.length = 32⌝ ∗
    (pubPtr ↦ₛ (5#8 :: pk)) ∗
    (privPtr ↦ₛ sk) ∗
    memRegion outPtr 65 ∗
    cells (s.sp - 64#64) 8
  post := fun (pubPtr, pk, privPtr, sk, outPtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (pubPtr ↦ₛ (5#8 :: pk)) ∗
    (privPtr ↦ₛ sk) ∗
    (outPtr ↦₈ 0#8) ∗
    ((outPtr + 1#64) ↦ₛ pk) ∗
    ((outPtr + 33#64) ↦ₛ clampBv8List sk) ∗
    cells (s0.sp - 64#64) 8

set_option maxHeartbeats 1200000 in
theorem curveKeyPairFromPubPriv_ok_trap {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr curveKeyPairFromPubPrivName)
      curveKeyPairFromPubPrivOkSpec := by
  unfold curveKeyPairFromPubPrivOkSpec
  simp only [memRegion_65_cells, cells, sepConj_emp, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]
  have hfn : libsignalSessionCode.fnOff curveKeyPairFromPubPrivName =
      num% (ls_off% "<libsignal_core::curve::KeyPair>::from_public_and_private") :=
    (ls_lemma% fnOff "<libsignal_core::curve::KeyPair>::from_public_and_private")
  responder_fetches_from b (Rust.withPanics (trTrapExterns C abs)) hfn 256028 0 424
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨pubPtr, pk, privPtr, sk, outPtr⟩ := x
  dsimp only at *
  subst h_1 h_3 h_5
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk, _⟩ := exists_bytes32_of_length_32 h_6
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13, sk14, sk15,
    sk16, sk17, sk18, sk19, sk20, sk21, sk22, sk23, sk24, sk25, sk26, sk27, sk28, sk29, sk30, sk31,
    hsk, hsk_clamp⟩ := exists_bytes32_of_length_32 h
  wp_pull_exists
  rw [pointsToBytes_cons, hpk (s0.readReg64 (.gpr 0#5) + 1#64),
    hsk (s0.readReg64 (.gpr 2#5)),
    hpk (s0.readReg64 (.gpr 8#5) + 1#64),
    hsk_clamp (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 1#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 9#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 17#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 25#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 41#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 49#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 57#64)]
  dsimp only [bytes32At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

theorem curveKeyPairFromPubPriv_ok {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr curveKeyPairFromPubPrivName)
      curveKeyPairFromPubPrivOkSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr curveKeyPairFromPubPrivName]
  exact subroutine_ok_kit_of_trTrap curveKeyPairFromPubPriv_ok_trap

/-! ## `curveKeyPairSerde_ok` (`0x2a930`) and `preKeyRecordKeyPair_ok` (`0x1e9f8`) -/

abbrev curveKeyPairSerdeName : String :=
  "<libsignal_core::curve::KeyPair as \
libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private"

abbrev preKeyRecordKeyPairName : String :=
  "<libsignal_protocol::state::prekey::PreKeyRecord>::key_pair"

theorem cells_8_sub176 (sp : BitVec 64) :
    cells (sp - 176#64) 8 =
      (∃∗ v0 : BitVec 64, (sp - 176#64) ↦₆₄ v0) ∗
      (∃∗ v1 : BitVec 64, (sp - 168#64) ↦₆₄ v1) ∗
      (∃∗ v2 : BitVec 64, (sp - 160#64) ↦₆₄ v2) ∗
      (∃∗ v3 : BitVec 64, (sp - 152#64) ↦₆₄ v3) ∗
      (∃∗ v4 : BitVec 64, (sp - 144#64) ↦₆₄ v4) ∗
      (∃∗ v5 : BitVec 64, (sp - 136#64) ↦₆₄ v5) ∗
      (∃∗ v6 : BitVec 64, (sp - 128#64) ↦₆₄ v6) ∗
      (∃∗ v7 : BitVec 64, (sp - 120#64) ↦₆₄ v7) := by
  simp only [cells, sepConj_emp, ← sepExists_sepConj_left, bv_sub_add_lit', BitVec.reduceSub]

theorem memRegion_8_bytes (a : BitVec 64) :
    memRegion a 8 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗
      (∃∗ b1 : BitVec 8, (a + 1#64) ↦₈ b1) ∗
      (∃∗ b2 : BitVec 8, (a + 2#64) ↦₈ b2) ∗
      (∃∗ b3 : BitVec 8, (a + 3#64) ↦₈ b3) ∗
      (∃∗ b4 : BitVec 8, (a + 4#64) ↦₈ b4) ∗
      (∃∗ b5 : BitVec 8, (a + 5#64) ↦₈ b5) ∗
      (∃∗ b6 : BitVec 8, (a + 6#64) ↦₈ b6) ∗
      (∃∗ b7 : BitVec 8, (a + 7#64) ↦₈ b7) := by
  rw [memRegion_split a 1 7 (by decide),
    memRegion_split (a + 1#64) 1 6 (by decide),
    memRegion_split (a + 1#64 + 1#64) 1 5 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64) 1 4 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64 + 1#64) 1 3 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) 1 2 (by decide),
    memRegion_split (a + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) 1 1 (by decide)]
  simp only [ProofLib.memRegion_one, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_65_bytes8 (a : BitVec 64) :
    memRegion a 65 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗
      memRegion (a + 1#64) 8 ∗
      memRegion (a + 9#64) 8 ∗
      memRegion (a + 17#64) 8 ∗
      memRegion (a + 25#64) 8 ∗
      memRegion (a + 33#64) 8 ∗
      memRegion (a + 41#64) 8 ∗
      memRegion (a + 49#64) 8 ∗
      memRegion (a + 57#64) 8 := by
  rw [memRegion_split a 1 64 (by decide),
    memRegion_split (a + 1#64) 8 56 (by decide),
    memRegion_split (a + 1#64 + 8#64) 8 48 (by decide),
    memRegion_split (a + 1#64 + 8#64 + 8#64) 8 40 (by decide),
    memRegion_split (a + 1#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    memRegion_split (a + 1#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (a + 1#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 1#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [ProofLib.memRegion_one, BitVec.add_assoc, BitVec.reduceAdd]

theorem cells_14_curveKeyPairSerde (sp : BitVec 64) :
    cells (sp - 112#64) 14 =
      (∃∗ d_112 : BitVec 32, (sp - 112#64) ↦₃₂ d_112) ∗
      (∃∗ b_108 : BitVec 8, (sp - 108#64) ↦₈ b_108) ∗
      (∃∗ b_107 : BitVec 8, (sp - 107#64) ↦₈ b_107) ∗
      (∃∗ b_106 : BitVec 8, (sp - 106#64) ↦₈ b_106) ∗
      (∃∗ b_105 : BitVec 8, (sp - 105#64) ↦₈ b_105) ∗
      memRegion (sp - 104#64) 65 ∗
      (∃∗ b_39 : BitVec 8, (sp - 39#64) ↦₈ b_39) ∗
      (∃∗ b_38 : BitVec 8, (sp - 38#64) ↦₈ b_38) ∗
      (∃∗ b_37 : BitVec 8, (sp - 37#64) ↦₈ b_37) ∗
      (∃∗ b_36 : BitVec 8, (sp - 36#64) ↦₈ b_36) ∗
      (∃∗ b_35 : BitVec 8, (sp - 35#64) ↦₈ b_35) ∗
      (∃∗ b_34 : BitVec 8, (sp - 34#64) ↦₈ b_34) ∗
      (∃∗ b_33 : BitVec 8, (sp - 33#64) ↦₈ b_33) ∗
      (∃∗ w_32 : BitVec 64, (sp - 32#64) ↦₆₄ w_32) ∗
      (∃∗ w_24 : BitVec 64, (sp - 24#64) ↦₆₄ w_24) ∗
      (∃∗ w_16 : BitVec 64, (sp - 16#64) ↦₆₄ w_16) ∗
      memRegion (sp - 8#64) 8 := by
  rw [← ProofLib.memRegion_cells (sp - 112#64) 14 (by decide)]
  rw [memRegion_split (sp - 112#64) 4 108 (by decide),
    memRegion_split (sp - 112#64 + 4#64) 4 104 (by decide),
    memRegion_split (sp - 112#64 + 4#64 + 4#64) 65 39 (by decide),
    memRegion_split (sp - 112#64 + 4#64 + 4#64 + 65#64) 7 32 (by decide),
    memRegion_split (sp - 112#64 + 4#64 + 4#64 + 65#64 + 7#64) 8 24 (by decide),
    memRegion_split (sp - 112#64 + 4#64 + 4#64 + 65#64 + 7#64 + 8#64) 8 16 (by decide),
    memRegion_split (sp - 112#64 + 4#64 + 4#64 + 65#64 + 7#64 + 8#64 + 8#64) 8 8 (by decide)]
  rw [memRegion_split (sp - 112#64 + 4#64) 1 3 (by decide),
    memRegion_split (sp - 112#64 + 4#64 + 1#64) 1 2 (by decide),
    memRegion_split (sp - 112#64 + 4#64 + 1#64 + 1#64) 1 1 (by decide)]
  rw [memRegion_split (sp - 112#64 + 4#64 + 4#64 + 65#64) 1 6 (by decide),
    memRegion_split (sp - 112#64 + 4#64 + 4#64 + 65#64 + 1#64) 1 5 (by decide),
    memRegion_split (sp - 112#64 + 4#64 + 4#64 + 65#64 + 1#64 + 1#64) 1 4 (by decide),
    memRegion_split (sp - 112#64 + 4#64 + 4#64 + 65#64 + 1#64 + 1#64 + 1#64) 1 3 (by decide),
    memRegion_split (sp - 112#64 + 4#64 + 4#64 + 65#64 + 1#64 + 1#64 + 1#64 + 1#64) 1 2 (by decide),
    memRegion_split
      (sp - 112#64 + 4#64 + 4#64 + 65#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64) 1 1 (by decide)]
  simp only [ProofLib.memRegion_eight, ProofLib.memRegion_four, ProofLib.memRegion_one,
    bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]

def curveKeyPairSerdeOkSpec :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (pubPtr, pk, privPtr, sk, outPtr) s =>
    ⌜s.readReg64 .x0 = pubPtr ∧ s.readReg64 .x1 = 33#64 ∧
      s.readReg64 .x2 = privPtr ∧ s.readReg64 .x3 = 32#64 ∧
      s.readReg64 .x8 = outPtr ∧ pk.length = 32 ∧ sk.length = 32⌝ ∗
    (pubPtr ↦ₛ (5#8 :: pk)) ∗
    (privPtr ↦ₛ sk) ∗
    memRegion outPtr 65 ∗
    cells (s.sp - 176#64) 8 ∗
    cells (s.sp - 112#64) 14
  post := fun (pubPtr, pk, privPtr, sk, outPtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (pubPtr ↦ₛ (5#8 :: pk)) ∗
    (privPtr ↦ₛ sk) ∗
    (outPtr ↦₈ 0#8) ∗
    ((outPtr + 1#64) ↦ₛ pk) ∗
    ((outPtr + 33#64) ↦ₛ clampBv8List sk) ∗
    cells (s0.sp - 176#64) 8 ∗
    cells (s0.sp - 112#64) 14

theorem cells_8_sub176_mr (sp : BitVec 64) :
    cells (sp - 176#64) 8 =
      memRegion (sp - 176#64) 8 ∗
      memRegion (sp - 168#64) 8 ∗
      memRegion (sp - 160#64) 8 ∗
      memRegion (sp - 152#64) 8 ∗
      memRegion (sp - 144#64) 8 ∗
      memRegion (sp - 136#64) 8 ∗
      memRegion (sp - 128#64) 8 ∗
      memRegion (sp - 120#64) 8 := by
  rw [cells_8_sub176 sp]
  simp only [← ProofLib.memRegion_eight]

abbrev memRegion_8_bytes_mr_rhs (a : BitVec 64) : SepProp :=
  memRegion a 1 ∗
  memRegion (a + 1#64) 1 ∗
  memRegion (a + 2#64) 1 ∗
  memRegion (a + 3#64) 1 ∗
  memRegion (a + 4#64) 1 ∗
  memRegion (a + 5#64) 1 ∗
  memRegion (a + 6#64) 1 ∗
  memRegion (a + 7#64) 1

theorem memRegion_8_bytes_mr (a : BitVec 64) :
    memRegion a 8 =
      memRegion a 1 ∗
      memRegion (a + 1#64) 1 ∗
      memRegion (a + 2#64) 1 ∗
      memRegion (a + 3#64) 1 ∗
      memRegion (a + 4#64) 1 ∗
      memRegion (a + 5#64) 1 ∗
      memRegion (a + 6#64) 1 ∗
      memRegion (a + 7#64) 1 := by
  rw [memRegion_8_bytes a]
  simp only [← ProofLib.memRegion_one]

theorem cells_14_curveKeyPairSerde_mr (sp : BitVec 64) :
    cells (sp - 112#64) 14 =
      memRegion (sp - 112#64) 4 ∗
      memRegion (sp - 108#64) 1 ∗
      memRegion (sp - 107#64) 1 ∗
      memRegion (sp - 106#64) 1 ∗
      memRegion (sp - 105#64) 1 ∗
      memRegion (sp - 104#64) 1 ∗
      memRegion_8_bytes_mr_rhs (sp - 103#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 95#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 87#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 79#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 71#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 63#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 55#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 47#64) ∗
      memRegion (sp - 39#64) 1 ∗
      memRegion (sp - 38#64) 1 ∗
      memRegion (sp - 37#64) 1 ∗
      memRegion (sp - 36#64) 1 ∗
      memRegion (sp - 35#64) 1 ∗
      memRegion (sp - 34#64) 1 ∗
      memRegion (sp - 33#64) 1 ∗
      memRegion (sp - 32#64) 8 ∗
      memRegion (sp - 24#64) 8 ∗
      memRegion (sp - 16#64) 8 ∗
      memRegion_8_bytes_mr_rhs (sp - 8#64) := by
  rw [cells_14_curveKeyPairSerde sp, memRegion_65_bytes8 (sp - 104#64)]
  simp only [← ProofLib.memRegion_four, ← ProofLib.memRegion_one, ← ProofLib.memRegion_eight,
    bv_sub_add_lit', BitVec.reduceSub]
  rw [memRegion_8_bytes_mr (sp - 103#64),
    memRegion_8_bytes_mr (sp - 95#64),
    memRegion_8_bytes_mr (sp - 87#64),
    memRegion_8_bytes_mr (sp - 79#64),
    memRegion_8_bytes_mr (sp - 71#64),
    memRegion_8_bytes_mr (sp - 63#64),
    memRegion_8_bytes_mr (sp - 55#64),
    memRegion_8_bytes_mr (sp - 47#64),
    memRegion_8_bytes_mr (sp - 8#64)]
  simp only [memRegion_8_bytes_mr_rhs, sepConj_assoc]

set_option maxHeartbeats 1200000 in
theorem curveKeyPairSerde_ok_trap {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr curveKeyPairSerdeName)
      curveKeyPairSerdeOkSpec := by
  unfold curveKeyPairSerdeOkSpec
  have hfn : libsignalSessionCode.fnOff curveKeyPairSerdeName =
      num% (ls_off% "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private") :=
    (ls_lemma% fnOff "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private")
  have hinner := subroutine_ok_rel2_trap
    (curveKeyPairFromPubPriv_ok_trap (b := b) (C := C) (abs := abs))
    (ls_lemma% fnOff "<libsignal_core::curve::KeyPair>::from_public_and_private") hfn (k := 81416) (by decide)
  simp only [curveKeyPairFromPubPrivOkSpec, cells, sepExists_sepConj_right,
    sepConj_emp, bv_sub_add_lit', BitVec.reduceSub] at hinner
  responder_fetches_from b (Rust.withPanics (trTrapExterns C abs)) hfn 174612 0 288
  wp_init x s0
  dsimp only [trTrapProgAt] at hinner ⊢
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨pubPtr, pk, privPtr, sk, outPtr⟩ := x
  dsimp only at *
  subst h_1 h_3 h_5
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk, _⟩ := exists_bytes32_of_length_32 h_6
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13, sk14, sk15,
    sk16, sk17, sk18, sk19, sk20, sk21, sk22, sk23, sk24, sk25, sk26, sk27, sk28, sk29, sk30, sk31,
    _, hsk_clamp⟩ := exists_bytes32_of_length_32 h
  rw (occs := .pos [1]) [cells_8_sub176 s0.sp]
  rw (occs := .pos [1]) [cells_14_curveKeyPairSerde s0.sp]
  rw [memRegion_8_bytes (s0.sp - 8#64)]
  simp only [bv_sub_add_lit', BitVec.reduceSub]
  wp_pull_exists
  wp_steps
  wp_call hinner (s0.readReg64 (.gpr 0#5), pk, s0.readReg64 (.gpr 2#5), sk, s0.sp - 104#64)
  rw [memRegion_65_bytes8 (s0.readReg64 (.gpr 8#5))]
  simp only [ProofLib.memRegion_eight]
  wp_pull_exists
  rw [hpk (s0.sp - 103#64),
    hsk_clamp (s0.sp - 71#64),
    hpk (s0.readReg64 (.gpr 8#5) + 1#64),
    hsk_clamp (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 1#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 9#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 17#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 25#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 41#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 49#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 57#64)]
  rw [cells_8_sub176_mr s0.sp, cells_14_curveKeyPairSerde_mr s0.sp]
  dsimp only [memRegion_8_bytes_mr_rhs, bytes32At]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_steps
  wp_done

theorem curveKeyPairSerde_ok {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr curveKeyPairSerdeName)
      curveKeyPairSerdeOkSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr curveKeyPairSerdeName]
  exact subroutine_ok_kit_of_trTrap curveKeyPairSerde_ok_trap

def preKeyRecordKeyPairOkSpec :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (recPtr, pubPtr, pk, privPtr, sk, outPtr) s =>
    ⌜s.readReg64 .x0 = recPtr ∧
      s.readReg64 .x8 = outPtr ∧ pk.length = 32 ∧ sk.length = 32⌝ ∗
    ((recPtr + 8#64) ↦₆₄ pubPtr) ∗
    ((recPtr + 16#64) ↦₆₄ 33#64) ∗
    ((recPtr + 32#64) ↦₆₄ privPtr) ∗
    ((recPtr + 40#64) ↦₆₄ 32#64) ∗
    (pubPtr ↦ₛ (5#8 :: pk)) ∗
    (privPtr ↦ₛ sk) ∗
    memRegion outPtr 65 ∗
    cells (s.sp - 176#64) 8 ∗
    cells (s.sp - 112#64) 14
  post := fun (recPtr, pubPtr, pk, privPtr, sk, outPtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ((recPtr + 8#64) ↦₆₄ pubPtr) ∗
    ((recPtr + 16#64) ↦₆₄ 33#64) ∗
    ((recPtr + 32#64) ↦₆₄ privPtr) ∗
    ((recPtr + 40#64) ↦₆₄ 32#64) ∗
    (pubPtr ↦ₛ (5#8 :: pk)) ∗
    (privPtr ↦ₛ sk) ∗
    (outPtr ↦₈ 0#8) ∗
    ((outPtr + 1#64) ↦ₛ pk) ∗
    ((outPtr + 33#64) ↦ₛ clampBv8List sk) ∗
    cells (s0.sp - 176#64) 8 ∗
    cells (s0.sp - 112#64) 14

set_option maxHeartbeats 1200000 in
theorem preKeyRecordKeyPair_ok_trap {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr preKeyRecordKeyPairName)
      preKeyRecordKeyPairOkSpec := by
  unfold preKeyRecordKeyPairOkSpec
  have hfn : libsignalSessionCode.fnOff preKeyRecordKeyPairName =
      num% (ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::key_pair") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::prekey::PreKeyRecord>::key_pair")
  have hinner := subroutine_ok_rel2_trap
    (curveKeyPairFromPubPriv_ok_trap (b := b) (C := C) (abs := abs))
    (ls_lemma% fnOff "<libsignal_core::curve::KeyPair>::from_public_and_private") hfn (k := 130596) (by decide)
  simp only [curveKeyPairFromPubPrivOkSpec, cells, sepExists_sepConj_right,
    sepConj_emp, bv_sub_add_lit', BitVec.reduceSub] at hinner
  responder_fetches_from b (Rust.withPanics (trTrapExterns C abs)) hfn 125432 0 300
  wp_init x s0
  dsimp only [trTrapProgAt] at hinner ⊢
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨recPtr, pubPtr, pk, privPtr, sk, outPtr⟩ := x
  dsimp only at *
  subst h_1 h_2
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk, _⟩ := exists_bytes32_of_length_32 h_3
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13, sk14, sk15,
    sk16, sk17, sk18, sk19, sk20, sk21, sk22, sk23, sk24, sk25, sk26, sk27, sk28, sk29, sk30, sk31,
    _, hsk_clamp⟩ := exists_bytes32_of_length_32 h
  rw (occs := .pos [1]) [cells_8_sub176 s0.sp]
  rw (occs := .pos [1]) [cells_14_curveKeyPairSerde s0.sp]
  rw [memRegion_8_bytes (s0.sp - 8#64)]
  simp only [bv_sub_add_lit', BitVec.reduceSub]
  wp_pull_exists
  wp_steps
  wp_call hinner (pubPtr, pk, privPtr, sk, s0.sp - 104#64)
  rw [memRegion_65_bytes8 (s0.readReg64 (.gpr 8#5))]
  simp only [ProofLib.memRegion_eight]
  wp_pull_exists
  rw [hpk (s0.sp - 103#64),
    hsk_clamp (s0.sp - 71#64),
    hpk (s0.readReg64 (.gpr 8#5) + 1#64),
    hsk_clamp (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 1#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 9#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 17#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 25#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 41#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 49#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 57#64)]
  rw [cells_8_sub176_mr s0.sp, cells_14_curveKeyPairSerde_mr s0.sp]
  dsimp only [memRegion_8_bytes_mr_rhs, bytes32At]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_steps
  wp_done

theorem preKeyRecordKeyPair_ok {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyRecordKeyPairName)
      preKeyRecordKeyPairOkSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr preKeyRecordKeyPairName]
  exact subroutine_ok_kit_of_trTrap preKeyRecordKeyPair_ok_trap

/-! ## `kemKeyPairFromPubPriv_ok` (`0x1f908`) and `kemKeyPairSerde_ok` (`0x2ae08`) -/

abbrev kemKeyPairFromPubPrivName : String :=
  "<libsignal_protocol::kem::KeyPair>::from_public_and_private"

abbrev kemKeyPairSerdeName : String :=
  "<libsignal_protocol::kem::KeyPair as \
libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private"

private theorem stackAt_kemKeyPairFromPubPriv (sp : BitVec 64) :
    memRegion (sp - 4160#64) 64 ∗ stackAt sp allocHookStack =
      stackAt (sp - 64#64) allocHookStack ∗ cells (sp - 64#64) 8 := by
  have h1 := stackAt_split_top sp 64 allocHookStack (by decide)
  have h2 := ProofLib.stackAt_split_cells sp allocHookStack 8 (by decide)
  have h3 : (64 + allocHookStack : Nat) = allocHookStack + 8 * 8 := by decide
  have h4 : BitVec.ofNat 64 (64 + allocHookStack) = 4160#64 := rfl
  have h5 : BitVec.ofNat 64 (8 * 8) = 64#64 := rfl
  rw [h4] at h1
  rw [h5] at h2
  rw [← h1, h3, h2]

def kemKeyPairFromPubPrivOkSpec (A : RustAlloc) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (pubPtr, pk, privPtr, sk, outPtr) s =>
    ⌜s.readReg64 .x0 = pubPtr ∧ s.readReg64 .x1 = 0x621#64 ∧
      s.readReg64 .x2 = privPtr ∧ s.readReg64 .x3 = 0xc61#64 ∧
      s.readReg64 .x8 = outPtr ∧ pk.length = 1568 ∧ sk.length = 3168⌝ ∗
    (pubPtr ↦ₛ (8#8 :: pk)) ∗
    (privPtr ↦ₛ (8#8 :: sk)) ∗
    cells outPtr 5 ∗
    (memRegion (s.sp - 4160#64) 64 ∗ stackAt s.sp allocHookStack) ∗
    A.pool
  post := fun (pubPtr, pk, privPtr, sk, outPtr) s0 sf =>
    ∃∗ pkBuf : BitVec 64, ∃∗ skBuf : BitVec 64,
      ⌜sf.trace = s0.trace ∧ pkBuf ≠ 0 ∧ skBuf ≠ 0⌝ ∗
      (pubPtr ↦ₛ (8#8 :: pk)) ∗
      (privPtr ↦ₛ (8#8 :: sk)) ∗
      (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
      ((outPtr + 8#64) ↦₆₄ pkBuf) ∗
      ((outPtr + 16#64) ↦₆₄ 0x620#64) ∗
      ((outPtr + 24#64) ↦₆₄ skBuf) ∗
      ((outPtr + 32#64) ↦₆₄ 0xc60#64) ∗
      (pkBuf ↦ₛ pk) ∗ A.live pkBuf 1568 1 ∗
      (skBuf ↦ₛ sk) ∗ A.live skBuf 3168 1 ∗
      (memRegion (s0.sp - 4160#64) 64 ∗ stackAt s0.sp allocHookStack) ∗
      A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

set_option maxHeartbeats 1200000 in
theorem kemKeyPairFromPubPriv_ok_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr kemKeyPairFromPubPrivName)
      (kemKeyPairFromPubPrivOkSpec A) := by
  unfold kemKeyPairFromPubPrivOkSpec
  simp only [stackAt_kemKeyPairFromPubPriv]
  simp only [cells, sepConj_emp, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hshim := session_shim_ok_at_trap b C abs kemKeyPairFromPubPrivName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private"))
    (by simp only [arm64_norm])
  have halloc := alloc_ok_at_trap b C A abs hA kemKeyPairFromPubPrivName
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private"))
    (by simp only [arm64_norm])
  have hmemcpy := session_memcpy_region_ok_at_trap b C abs kemKeyPairFromPubPrivName
    (num% (ls_off% "memcpy" -
      ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private"))
    (by simp only [arm64_norm])
  have hpanic := panic_at_handle_alloc_error_trap b C abs kemKeyPairFromPubPrivName
    (num% (ls_off% "alloc::alloc::handle_alloc_error" -
      ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private"))
    (by simp only [arm64_norm])
  clear hA
  wpp_init g s0
  simp only [sepConj_assoc]
  have hfn : libsignalSessionCode.fnOff kemKeyPairFromPubPrivName =
      num% (ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private") :=
    (ls_lemma% fnOff "<libsignal_protocol::kem::KeyPair>::from_public_and_private")
  responder_fetches_from b (Rust.withPanics (trTrapExterns C abs)) hfn 129288 0 364
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase b
        (Rust.withPanics (trTrapExterns C abs))).fnAddr kemKeyPairFromPubPrivName := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [trTrapProgAt] at hshim halloc hmemcpy hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr kemKeyPairFromPubPrivName = entry
  examples_hide_fetches
  obtain ⟨pubPtr, pk, privPtr, sk, outPtr⟩ := g
  dsimp only at *
  subst h_1 h_3 h_5
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay1 : LayoutOk 1568 1 := ⟨by decide, hpow2, by decide⟩
  have hlay2 : LayoutOk 3168 1 := ⟨by decide, hpow2, by decide⟩
  rw [pointsToBytes_cons (s0.readReg64 (.gpr 0#5)),
    pointsToBytes_cons (s0.readReg64 (.gpr 2#5))]
  apply SepWPp.of_sepWP (mid := entry + 76#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (1568, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace1 => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" -
      ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hpanic (by simp only [arm64_norm, *])
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    simp only [hoom1, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + 140#64)
    wp_steps
    rw [← h_6]
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 0#5) + 1#64, pk)
    simp only [h_6] at *
    wp_steps
    wp_call hshim ()
    wp_steps
    wp_call halloc (3168, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom2 : sf_4.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      simp only [hoom2, ite_true]
      refine sepWPp_pure_mid fun htrace2 => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" -
        ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private"))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hpanic (by simp only [arm64_norm, *])
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      simp only [hoom2, ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod2, htrace2⟩ => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      rw [← h]
      wp_call hmemcpy (sf_4.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 2#5) + 1#64, sk)
      simp only [h] at *
      wp_steps
      wp_done

theorem kemKeyPairFromPubPriv_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr kemKeyPairFromPubPrivName)
      (kemKeyPairFromPubPrivOkSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr kemKeyPairFromPubPrivName]
  exact subroutine_ok_kit_of_trTrap (kemKeyPairFromPubPriv_ok_trap hA)

set_option maxHeartbeats 1200000 in
theorem kemKeyPairSerde_ok_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr kemKeyPairSerdeName)
      (kemKeyPairFromPubPrivOkSpec A) := by
  have hfn : libsignalSessionCode.fnOff kemKeyPairSerdeName =
      num% (ls_off% "<libsignal_protocol::kem::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private") :=
    (ls_lemma% fnOff "<libsignal_protocol::kem::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private")
  responder_fetches_from b (Rust.withPanics (trTrapExterns C abs)) hfn 175852 0 4
  have hinner := kemKeyPairFromPubPriv_ok_trap (b := b) (C := C) (A := A)
    (abs := abs) hA
  exact subroutine_ok_of_b ‹_›
    (by simp only [trTrapProgAt, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::kem::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private"),
      (ls_lemma% fnOff "<libsignal_protocol::kem::KeyPair>::from_public_and_private"), arm64_norm])
    rfl (by intros; rfl) hinner (by intros; rfl) (by intros; rfl) (by intros; rfl)

theorem kemKeyPairSerde_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr kemKeyPairSerdeName)
      (kemKeyPairFromPubPrivOkSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr kemKeyPairSerdeName]
  exact subroutine_ok_kit_of_trTrap (kemKeyPairSerde_ok_trap hA)

/-! ## `privKeySerdeSerialize_ok` (`0x28eb8`) -/

abbrev privKeySerdeSerializeName : String :=
  "<libsignal_core::curve::PrivateKey as \
libsignal_protocol::state::signed_prekey::KeySerde>::serialize"

theorem privKeySerdeSerialize_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr privKeySerdeSerializeName)
      (privSerializeSpec A) := by
  have hfn : libsignalSessionCode.fnOff privKeySerdeSerializeName = 0x28f9c :=
    libsignalSessionCode_fnOff_0x28f9c
  responder_fetches_from b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x28f9c 0 4
  have hinner := privSerialize_ok b C A ctl abs hA
  exact subroutine_ok_of_b ‹_›
    (by simp only [tripleRatchetProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x28f9c,
      libsignalSessionCode_fnOff_0x3e7c0, arm64_norm])
    rfl (by intros; rfl) hinner (by intros; rfl) (by intros; rfl) (by intros; rfl)


/-! ## Tail-Call `__rust_dealloc` and `SepWPp` Call Helpers -/

private theorem stackAt_add_48 (sp : BitVec 64) :
    stackAt sp (allocHookStack + 48) =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 := by
  simpa using ProofLib.stackAt_split_cells sp allocHookStack 6 (by decide)

private theorem stackAt_add_48_comm (sp : BitVec 64) :
    stackAt sp (allocHookStack + 48) =
      stackAt (sp - BitVec.ofNat 64 allocHookStack) 48 ∗ stackAt sp allocHookStack := by
  unfold stackAt
  have hsplit :=
    memRegion_split (sp - BitVec.ofNat 64 (48 + allocHookStack)) 48 allocHookStack (by decide)
  have h0 : allocHookStack + 48 = 48 + allocHookStack := rfl
  have h1 : sp - BitVec.ofNat 64 (48 + allocHookStack) =
      sp - BitVec.ofNat 64 allocHookStack - 48#64 := by bv_lin
  have h2 : sp - BitVec.ofNat 64 (48 + allocHookStack) + 48#64 =
      sp - BitVec.ofNat 64 allocHookStack := by bv_lin
  rw [h0, hsplit, h2, h1]

private theorem stackAt_add_64 (sp : BitVec 64) :
    stackAt sp (allocHookStack + 64) =
      stackAt (sp - 64#64) allocHookStack ∗ cells (sp - 64#64) 8 := by
  simpa using ProofLib.stackAt_split_cells sp allocHookStack 8 (by decide)

private theorem stackAt_add_64_comm (sp : BitVec 64) :
    stackAt sp (allocHookStack + 64) =
      stackAt (sp - BitVec.ofNat 64 allocHookStack) 64 ∗ stackAt sp allocHookStack := by
  unfold stackAt
  have hsplit :=
    memRegion_split (sp - BitVec.ofNat 64 (64 + allocHookStack)) 64 allocHookStack (by decide)
  have h0 : allocHookStack + 64 = 64 + allocHookStack := rfl
  have h1 : sp - BitVec.ofNat 64 (64 + allocHookStack) =
      sp - BitVec.ofNat 64 allocHookStack - 64#64 := by bv_lin
  have h2 : sp - BitVec.ofNat 64 (64 + allocHookStack) + 64#64 =
      sp - BitVec.ofNat 64 allocHookStack := by bv_lin
  rw [h0, hsplit, h2, h1]

private theorem pointsTo64_entails_exists (a v : BitVec 64) {R Q : SepProp}
    (h : R ⊢ Q) : ((a ↦₆₄ v) ∗ R) ⊢ ∃∗ x, (a ↦₆₄ x) ∗ Q :=
  Entails.trans (sepConj_mono_right h) (Entails.sepExists_intro (P := fun x => (a ↦₆₄ x) ∗ Q) v)

private theorem pointsTo64_entails_exists_single (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ ∃∗ x, (a ↦₆₄ x) :=
  Entails.sepExists_intro (P := fun x => a ↦₆₄ x) v

private theorem pointsTo64_6_entails_cells (base : BitVec 64)
    (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    ((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗
      ((base + 16#64) ↦₆₄ v2) ∗ ((base + 24#64) ↦₆₄ v3) ∗
      ((base + 32#64) ↦₆₄ v4) ∗ ((base + 40#64) ↦₆₄ v5)) ⊢ cells base 6 := by
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  exact pointsTo64_entails_exists _ v0
    (pointsTo64_entails_exists _ v1
      (pointsTo64_entails_exists _ v2
        (pointsTo64_entails_exists _ v3
          (pointsTo64_entails_exists _ v4
            (pointsTo64_entails_exists_single _ v5)))))

private theorem pointsTo64_8_entails_cells (base : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64) :
    ((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗
      ((base + 16#64) ↦₆₄ v2) ∗ ((base + 24#64) ↦₆₄ v3) ∗
      ((base + 32#64) ↦₆₄ v4) ∗ ((base + 40#64) ↦₆₄ v5) ∗
      ((base + 48#64) ↦₆₄ v6) ∗ ((base + 56#64) ↦₆₄ v7)) ⊢ cells base 8 := by
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  exact pointsTo64_entails_exists _ v0
    (pointsTo64_entails_exists _ v1
      (pointsTo64_entails_exists _ v2
        (pointsTo64_entails_exists _ v3
          (pointsTo64_entails_exists _ v4
            (pointsTo64_entails_exists _ v5
              (pointsTo64_entails_exists _ v6
                (pointsTo64_entails_exists_single _ v7)))))))

private abbrev DeallocTail48Ghost :=
  BitVec 64 × List (BitVec 8) × Nat ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def rustDeallocTail48Spec (A : RustAlloc) : Spec DeallocTail48Ghost where
  pre := fun (p, bs, align, v0, v1, v2, v3, v4, v5) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ (s.readReg64 .x2).toNat = align⌝ ∗
      A.pool ∗ A.live p bs.length align ∗ (p ↦ₛ bs) ∗
      stackAt (s.sp - 48#64) allocHookStack ∗
      ((s.sp - 48#64) ↦₆₄ v0) ∗ ((s.sp - 40#64) ↦₆₄ v1) ∗
      ((s.sp - 32#64) ↦₆₄ v2) ∗ ((s.sp - 24#64) ↦₆₄ v3) ∗
      ((s.sp - 16#64) ↦₆₄ v4) ∗ ((s.sp - 8#64) ↦₆₄ v5)
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗
      stackAt (s0.sp - 48#64) allocHookStack ∗ cells (s0.sp - 48#64) 6

private theorem dealloc_tail48_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (rustDeallocTail48Spec A) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨p, bs, align, v0, v1, v2, v3, v4, v5⟩ R s0 hpc hrun hpre hsp
  have hcells :
      (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
        ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
        ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ⊢ cells (s0.sp - 48#64) 6 := by
    have h := pointsTo64_6_entails_cells (s0.sp - 48#64) v0 v1 v2 v3 v4 v5
    have ha1 : s0.sp - 48#64 + 8#64 = s0.sp - 40#64 := by bv_lin
    have ha2 : s0.sp - 48#64 + 16#64 = s0.sp - 32#64 := by bv_lin
    have ha3 : s0.sp - 48#64 + 24#64 = s0.sp - 24#64 := by bv_lin
    have ha4 : s0.sp - 48#64 + 32#64 = s0.sp - 16#64 := by bv_lin
    have ha5 : s0.sp - 48#64 + 40#64 = s0.sp - 8#64 := by bv_lin
    rwa [ha1, ha2, ha3, ha4, ha5] at h
  have hbs_mem := pointsToBytes_entails_memRegion p bs
  have hpre2 : s0.mem ⊨ (rustDeallocSpec A).pre (p, bs.length, align) s0 ∗
      (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗ R) := by
    unfold rustDeallocTail48Spec at hpre
    unfold rustDeallocSpec
    dsimp only at hpre ⊢
    have h1 : s0.mem ⊨
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align⌝ ∗
          A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
          (stackAt (s0.sp - 48#64) allocHookStack ∗ cells (s0.sp - 48#64) 6)) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hpre
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hbs_mem (sepConj_mono_right hcells))))
    rw [← stackAt_add_48, stackAt_add_48_comm] at h1
    exact (by ac_rfl :
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align⌝ ∗
        A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗ stackAt s0.sp allocHookStack)) ∗ R) =
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align⌝ ∗
        A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗ stackAt s0.sp allocHookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗ R))) ▸ h1
  refine ((dealloc_ok_at b C A ctl abs hA name k hk).to_outcome
    (p, bs.length, align)
    (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗ R) s0 hpc hrun hpre2 hsp).mono_outcome
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    unfold rustDeallocTail48Spec
    unfold rustDeallocSpec at hpost
    dsimp only at hpost ⊢
    rw [← stackAt_add_48, stackAt_add_48_comm]
    exact (by ac_rfl :
      ((⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp allocHookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗ R)) =
      ((⌜sf.trace = s0.trace⌝ ∗ A.pool ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗
          stackAt s0.sp allocHookStack)) ∗ R)) ▸ hpost
  · exact False.elim (not_satisfies_false_sepConj hpost)
  · exact False.elim (not_satisfies_false_sepConj hpost)
  · exact False.elim (not_satisfies_false_sepConj hpost)

private abbrev DeallocTail64Ghost :=
  BitVec 64 × List (BitVec 8) × Nat ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def rustDeallocTail64Spec (A : RustAlloc) : Spec DeallocTail64Ghost where
  pre := fun (p, bs, align, v0, v1, v2, v3, v4, v5, v6, v7) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ (s.readReg64 .x2).toNat = align⌝ ∗
      A.pool ∗ A.live p bs.length align ∗ (p ↦ₛ bs) ∗
      stackAt (s.sp - 64#64) allocHookStack ∗
      ((s.sp - 64#64) ↦₆₄ v0) ∗ ((s.sp - 56#64) ↦₆₄ v1) ∗
      ((s.sp - 48#64) ↦₆₄ v2) ∗ ((s.sp - 40#64) ↦₆₄ v3) ∗
      ((s.sp - 32#64) ↦₆₄ v4) ∗ ((s.sp - 24#64) ↦₆₄ v5) ∗
      ((s.sp - 16#64) ↦₆₄ v6) ∗ ((s.sp - 8#64) ↦₆₄ v7)
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗
      stackAt (s0.sp - 64#64) allocHookStack ∗ cells (s0.sp - 64#64) 8

private theorem dealloc_tail64_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (rustDeallocTail64Spec A) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨p, bs, align, v0, v1, v2, v3, v4, v5, v6, v7⟩ R s0 hpc hrun hpre hsp
  have hcells :
      (((s0.sp - 64#64) ↦₆₄ v0) ∗ ((s0.sp - 56#64) ↦₆₄ v1) ∗
        ((s0.sp - 48#64) ↦₆₄ v2) ∗ ((s0.sp - 40#64) ↦₆₄ v3) ∗
        ((s0.sp - 32#64) ↦₆₄ v4) ∗ ((s0.sp - 24#64) ↦₆₄ v5) ∗
        ((s0.sp - 16#64) ↦₆₄ v6) ∗ ((s0.sp - 8#64) ↦₆₄ v7)) ⊢ cells (s0.sp - 64#64) 8 := by
    have h := pointsTo64_8_entails_cells (s0.sp - 64#64) v0 v1 v2 v3 v4 v5 v6 v7
    have ha1 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_lin
    have ha2 : s0.sp - 64#64 + 16#64 = s0.sp - 48#64 := by bv_lin
    have ha3 : s0.sp - 64#64 + 24#64 = s0.sp - 40#64 := by bv_lin
    have ha4 : s0.sp - 64#64 + 32#64 = s0.sp - 32#64 := by bv_lin
    have ha5 : s0.sp - 64#64 + 40#64 = s0.sp - 24#64 := by bv_lin
    have ha6 : s0.sp - 64#64 + 48#64 = s0.sp - 16#64 := by bv_lin
    have ha7 : s0.sp - 64#64 + 56#64 = s0.sp - 8#64 := by bv_lin
    rwa [ha1, ha2, ha3, ha4, ha5, ha6, ha7] at h
  have hbs_mem := pointsToBytes_entails_memRegion p bs
  have hpre2 : s0.mem ⊨ (rustDeallocSpec A).pre (p, bs.length, align) s0 ∗
      (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗ R) := by
    unfold rustDeallocTail64Spec at hpre
    unfold rustDeallocSpec
    dsimp only at hpre ⊢
    have h1 : s0.mem ⊨
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align⌝ ∗
          A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
          (stackAt (s0.sp - 64#64) allocHookStack ∗ cells (s0.sp - 64#64) 8)) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hpre
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hbs_mem (sepConj_mono_right hcells))))
    rw [← stackAt_add_64, stackAt_add_64_comm] at h1
    exact (by ac_rfl :
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align⌝ ∗
        A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗ stackAt s0.sp allocHookStack)) ∗ R) =
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align⌝ ∗
        A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗ stackAt s0.sp allocHookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗ R))) ▸ h1
  refine ((dealloc_ok_at b C A ctl abs hA name k hk).to_outcome
    (p, bs.length, align)
    (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗ R) s0 hpc hrun hpre2 hsp).mono_outcome
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    unfold rustDeallocTail64Spec
    unfold rustDeallocSpec at hpost
    dsimp only at hpost ⊢
    rw [← stackAt_add_64, stackAt_add_64_comm]
    exact (by ac_rfl :
      ((⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp allocHookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗ R)) =
      ((⌜sf.trace = s0.trace⌝ ∗ A.pool ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗
          stackAt s0.sp allocHookStack)) ∗ R)) ▸ hpost
  · exact False.elim (not_satisfies_false_sepConj hpost)
  · exact False.elim (not_satisfies_false_sepConj hpost)
  · exact False.elim (not_satisfies_false_sepConj hpost)

private theorem spAligned_sub_48 {sp sp' : BitVec 64} (halign : (sp &&& 15#64 == 0#64) = true)
    (hsp : sp' = sp - 48#64) : (sp' &&& 15#64 == 0#64) = true := by
  subst hsp; simp only [beq_iff_eq] at halign ⊢; bv_bits

private theorem spAligned_sub_112 {sp sp' : BitVec 64} (halign : (sp &&& 15#64 == 0#64) = true)
    (hsp : sp' = sp - 112#64) : (sp' &&& 15#64 == 0#64) = true := by
  subst hsp; simp only [beq_iff_eq] at halign ⊢; bv_bits

private theorem SepWPp_call_pk_gen {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    {entry ret_pc sp_call selfPtr : BitVec 64} {A : RustAlloc}
    (hpk : subroutine_ok prog entry (publicKeySerializeSpec A))
    (pk : PublicKey)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hsp_eq : s.sp = sp_call)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = selfPtr)
    (hP : P = ((selfPtr ↦ₛ pk.bytes.toList) ∗ A.pool ∗
      stackAt sp_call publicKeySerializeStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf →
      SepWPp prog ret sf
        ((⌜sf.readReg64 Reg.x1 = 33#64 ∧ sf.trace = s0.trace⌝ ∗
          (selfPtr ↦ₛ pk.bytes.toList) ∗
          boxU8Buf A (sf.readReg64 Reg.x0) pk.serialize ∗
          A.pool ∗ stackAt sp_call publicKeySerializeStack) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  refine SepWPp.call_frame (x := ⟨selfPtr, pk⟩) hpk hpc hrun
    (by unfold State.spAligned; rw [hsp_eq]; exact hsp_align) hlr ?_ hx0 hP
    (fun sf code R' _ h => allowPanic_not_exited h)
    (fun sf _ h => by
      rw [← sepConj_assoc]; exact allowPanic_frame (allocFailedIn_of_trace_eq htr) h)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
  · dsimp only [publicKeySerializeSpec, Spec.allowPanicWhen]
    rw [hsp_eq]
  · dsimp only [publicKeySerializeSpec, Spec.allowPanicWhen]
    rw [hsp_eq, htr]
    exact hnext sf hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f

private theorem SepWPp_call_priv_gen {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    {entry ret_pc sp_call selfPtr retPtr : BitVec 64} {A : RustAlloc}
    (hpriv : subroutine_ok prog entry (privSerializeSpec A))
    (bs : List (BitVec 8))
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hsp_eq : s.sp = sp_call)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx : s.readReg64 Reg.x0 = selfPtr ∧ s.readReg64 Reg.x8 = retPtr ∧ bs.length = 32)
    (hP : P = ((selfPtr ↦ₛ bs) ∗ memRegion retPtr 24 ∗ A.pool ∗
      stackAt sp_call extHookStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf →
      SepWPp prog ret sf
        ((⌜sf.trace = s0.trace⌝ ∗ (selfPtr ↦ₛ bs) ∗
          vecU8 A retPtr bs ∗ A.pool ∗ stackAt sp_call extHookStack) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  refine SepWPp.call_frame (x := (selfPtr, bs, retPtr)) hpriv hpc hrun
    (by unfold State.spAligned; rw [hsp_eq]; exact hsp_align) hlr ?_ hx hP
    (fun sf code R' _ h => allowPanic_not_exited h)
    (fun sf _ h => by
      rw [← sepConj_assoc]; exact allowPanic_frame (allocFailedIn_of_trace_eq htr) h)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
  · dsimp only [privSerializeSpec, Spec.allowPanicWhen]
    rw [hsp_eq]
  · dsimp only [privSerializeSpec, Spec.allowPanicWhen]
    rw [hsp_eq, htr]
    exact hnext sf hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f

/-! ## `pubKeySerdeSerialize_ok` (`0x2657c`) -/

abbrev pubKeySerdeSerializeName : String :=
  "<libsignal_core::curve::PublicKey as \
libsignal_protocol::state::signed_prekey::KeySerde>::serialize"

private theorem stackAt_publicKeySerialize_sub48 (sp : BitVec 64) :
    memRegion (sp - 4176#64) 32 ∗ stackAt (sp - 48#64) allocHookStack =
      stackAt (sp - 48#64) publicKeySerializeStack := by
  unfold stackAt publicKeySerializeStack allocHookStack
  have hsplit := memRegion_split (sp - 4176#64) 32 4096 (by decide)
  have h1 : sp - 48#64 - BitVec.ofNat 64 (32 + 4096) = sp - 4176#64 := by bv_lin
  have h2 : sp - 4176#64 + 32#64 = sp - 48#64 - 4096#64 := by bv_lin
  rw [h1, hsplit, h2]

private theorem stackAt_publicKeySerialize_sub48_assoc (sp : BitVec 64) (R : SepProp) :
    memRegion (sp - 4176#64) 32 ∗ (stackAt (sp - 48#64) allocHookStack ∗ R) =
      stackAt (sp - 48#64) publicKeySerializeStack ∗ R := by
  rw [← sepConj_assoc, stackAt_publicKeySerialize_sub48]

def pubKeySerdeSerializeOkSpec (A : RustAlloc) :
    Spec (BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (self, pk, outPtr) s =>
    ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x8 = outPtr⌝ ∗
    (self ↦ₛ pk.bytes.toList) ∗
    cells outPtr 3 ∗
    (memRegion (s.sp - 4176#64) 32 ∗ stackAt (s.sp - 48#64) allocHookStack ∗
      cells (s.sp - 48#64) 6) ∗
    A.pool
  post := fun (self, pk, outPtr) s0 sf =>
    ∃∗ vecPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ vecPtr ≠ 0⌝ ∗
      (self ↦ₛ pk.bytes.toList) ∗
      (outPtr ↦₆₄ 33#64) ∗ ((outPtr + 8#64) ↦₆₄ vecPtr) ∗ ((outPtr + 16#64) ↦₆₄ 33#64) ∗
      (vecPtr ↦ₛ pk.serialize) ∗ A.live vecPtr 33 1 ∗
      (memRegion (s0.sp - 4176#64) 32 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
        cells (s0.sp - 48#64) 6) ∗
      A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem pubKeySerdeSerialize_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr pubKeySerdeSerializeName)
      (pubKeySerdeSerializeOkSpec A) := by
  unfold pubKeySerdeSerializeOkSpec
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  have hpubser := subroutine_ok_rel2 (public_key_serialize_ok (b := b) (C := C) (ctl := ctl) hA)
    libsignalSessionCode_fnOff_0x3e2c4 libsignalSessionCode_fnOff_0x26630 (k := 97428) (by decide)
  have hshim := session_shim_ok_at b C ctl abs pubKeySerdeSerializeName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x26630))
    (by simp only [arm64_norm])
  have halloc := alloc_ok_at b C A ctl abs hA pubKeySerdeSerializeName (num% (ls_off% "__rustc::__rust_alloc" - 0x26630))
    (by simp only [arm64_norm])
  have hmemcpy := session_memcpy_region_ok_at b C ctl abs pubKeySerdeSerializeName (num% (ls_off% "memcpy" - 0x26630))
    (by simp only [arm64_norm])
  have hpanic := panic_at_handle_error b C ctl abs pubKeySerdeSerializeName (num% (ls_off% "alloc::raw_vec::handle_error" - 0x26630))
    (by simp only [arm64_norm])
  have hdealloc := dealloc_tail48_ok_at b C A ctl abs hA pubKeySerdeSerializeName (num% (ls_off% "__rustc::__rust_dealloc" - 0x26630))
    (by simp only [arm64_norm])
  simp only [rustDeallocTail48Spec, cells, sepConj_emp, sepExists_sepConj_right,
    sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit] at hdealloc
  clear hA
  wpp_init g s0
  simp only [sepConj_assoc]
  have hfn : libsignalSessionCode.fnOff pubKeySerdeSerializeName = 0x26630 :=
    libsignalSessionCode_fnOff_0x26630
  responder_fetches_from b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x26630 0 156
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase b
        (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr pubKeySerdeSerializeName := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAt] at hpubser hshim halloc hmemcpy hpanic hdealloc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr pubKeySerdeSerializeName = entry
  examples_hide_fetches
  obtain ⟨self, pk, outPtr⟩ := g
  dsimp only at *
  subst h_1 h
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  have hser_len : pk.serialize.length = 33 := by
    simp [PublicKey.serialize, List.Vector.toList_length]
  rw [stackAt_publicKeySerialize_sub48_assoc s0.sp]
  apply SepWPp.of_sepWP (mid := entry + 97428#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPp_call_pk_gen hpubser pk
    (ret_pc := entry + 24#64) (sp_call := s0.sp - 48#64) (selfPtr := s0.readReg64 (Reg.gpr 0#5))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (spAligned_sub_48 hsp_align rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus)
    fun sf_pk hpc_pk hrun_pk hsp_pk hcs_pk => ?_
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_pk
  rcases hcs_pk with
    ⟨hcs_k19, hcs_k20, hcs_k21, hcs_k22, hcs_k23, hcs_k24, hcs_k25, hcs_k26, hcs_k27, hcs_k28,
      hcs_k29⟩
  simp only [arm64_norm, *]
    at hcs_k19 hcs_k20 hcs_k21 hcs_k22 hcs_k23 hcs_k24 hcs_k25 hcs_k26 hcs_k27 hcs_k28 hcs_k29
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1, htrace0⟩ => ?_
  refine SepWPp.fold (boxU8Buf_pk_expose A (sf_pk.readReg64 .x0) pk) (by sep_focus) ?_
  rw [← stackAt_publicKeySerialize_sub48 s0.sp]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hbox_ne => ?_
  apply SepWPp.of_sepWP (mid := entry + 76#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true]
    refine sepWPp_pure_mid fun htrace2 => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x26630))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hpanic (by simp only [arm64_norm, *])
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod, htrace2⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    rw [← hser_len]
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), sf_pk.readReg64 (Reg.gpr 0#5), pk.serialize)
    simp only [hser_len]
    wp_steps
    rw [← hser_len]
    wp_call hdealloc (sf_pk.readReg64 (Reg.gpr 0#5), pk.serialize, 1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    simp only [hser_len]
    wp_done

/-! ## `kemPubKeySerdeSerialize_ok` and `kemSecretKeySerdeSerialize_ok` (`0x29484`) -/

abbrev kemPubKeySerdeSerializeName : String :=
  "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public> as \
libsignal_protocol::state::signed_prekey::KeySerde>::serialize"

abbrev kemSecretKeySerdeSerializeName : String :=
  "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Secret> as \
libsignal_protocol::state::signed_prekey::KeySerde>::serialize"

private theorem memRegion_1569_cons (a : BitVec 64) :
    memRegion a 1569 = (∃∗ b0 : BitVec 8, (a ↦₈ b0) ∗ memRegion (a + 1#64) 1568) := by
  rw [memRegion_split a 1 1568 (by decide), ProofLib.memRegion_one, sepExists_sepConj_left]

private theorem memRegion_3169_cons (a : BitVec 64) :
    memRegion a 3169 = (∃∗ b0 : BitVec 8, (a ↦₈ b0) ∗ memRegion (a + 1#64) 3168) := by
  rw [memRegion_split a 1 3168 (by decide), ProofLib.memRegion_one, sepExists_sepConj_left]

def kemPubKeySerdeSerializeOkSpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (self, boxPtr, pk, outPtr) s =>
    ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x8 = outPtr ∧ pk.length = 1568⌝ ∗
    (self ↦₆₄ boxPtr) ∗ ((self + 8#64) ↦₆₄ 0x620#64) ∗
    (boxPtr ↦ₛ pk) ∗
    cells outPtr 3 ∗
    (stackAt (s.sp - 64#64) allocHookStack ∗ cells (s.sp - 64#64) 8) ∗
    A.pool
  post := fun (self, boxPtr, pk, outPtr) s0 sf =>
    ∃∗ vecPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ vecPtr ≠ 0⌝ ∗
      (self ↦₆₄ boxPtr) ∗ ((self + 8#64) ↦₆₄ 0x620#64) ∗
      (boxPtr ↦ₛ pk) ∗
      (outPtr ↦₆₄ 0x621#64) ∗ ((outPtr + 8#64) ↦₆₄ vecPtr) ∗ ((outPtr + 16#64) ↦₆₄ 0x621#64) ∗
      (vecPtr ↦ₛ (8#8 :: pk)) ∗ A.live vecPtr 1569 1 ∗
      (stackAt (s0.sp - 64#64) allocHookStack ∗ cells (s0.sp - 64#64) 8) ∗
      A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem kemPubKeySerdeSerialize_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr kemPubKeySerdeSerializeName)
      (kemPubKeySerdeSerializeOkSpec A) := by
  unfold kemPubKeySerdeSerializeOkSpec
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  have hshim := session_shim_ok_at b C ctl abs kemPubKeySerdeSerializeName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x29568))
    (by simp only [arm64_norm])
  have halloc := alloc_ok_at b C A ctl abs hA kemPubKeySerdeSerializeName (num% (ls_off% "__rustc::__rust_alloc" - 0x29568))
    (by simp only [arm64_norm])
  have hmemcpy := session_memcpy_region_ok_at b C ctl abs kemPubKeySerdeSerializeName (num% (ls_off% "memcpy" - 0x29568))
    (by simp only [arm64_norm])
  have hpanic := panic_at_handle_error b C ctl abs kemPubKeySerdeSerializeName (num% (ls_off% "alloc::raw_vec::handle_error" - 0x29568))
    (by simp only [arm64_norm])
  have hdealloc := dealloc_tail64_ok_at b C A ctl abs hA kemPubKeySerdeSerializeName (num% (ls_off% "__rustc::__rust_dealloc" - 0x29568))
    (by simp only [arm64_norm])
  simp only [rustDeallocTail64Spec, cells, sepConj_emp, sepExists_sepConj_right,
    sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit] at hdealloc
  clear hA
  wpp_init g s0
  simp only [sepConj_assoc]
  have hfn : libsignalSessionCode.fnOff kemPubKeySerdeSerializeName = 0x29568 :=
    libsignalSessionCode_fnOff_0x29568
  responder_fetches_from b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x29568 0 212
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase b
        (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr kemPubKeySerdeSerializeName := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAt] at hshim halloc hmemcpy hpanic hdealloc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr kemPubKeySerdeSerializeName = entry
  examples_hide_fetches
  obtain ⟨self, boxPtr, pk, outPtr⟩ := g
  dsimp only at *
  subst h_1 h_2
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 1569 1 := ⟨by decide, hpow2, by decide⟩
  have hcons_len : (8#8 :: pk).length = 1569 := by simp [h]
  apply SepWPp.of_sepWP (mid := entry + 80#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (1569, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace1 => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x29568))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hpanic (by simp only [arm64_norm, *])
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    simp only [hoom1, ite_false, memRegion_1569_cons, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + 132#64)
    wp_steps
    rw [← h]
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5) + 1#64, boxPtr, pk)
    simp only [h] at *
    refine SepWP.fold
      (pointsToBytes_cons_fold (sf_1.readReg64 (Reg.gpr 0#5)) 8#8 pk) (by sep_focus) ?_
    wp_steps
    wp_call hshim ()
    wp_steps
    wp_call halloc (1569, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom2 : sf_4.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      simp only [hoom2, ite_true]
      refine sepWPp_pure_mid fun htrace2 => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x29568))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hpanic (by simp only [arm64_norm, *])
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      simp only [hoom2, ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod2, htrace2⟩ => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      rw [← hcons_len]
      wp_call hmemcpy (sf_4.readReg64 (Reg.gpr 0#5), sf_1.readReg64 (Reg.gpr 0#5), 8#8 :: pk)
      simp only [hcons_len]
      wp_steps
      rw [← hcons_len]
      wp_call hdealloc (sf_1.readReg64 (Reg.gpr 0#5), 8#8 :: pk, 1,
        s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
        s0.readReg64 (Reg.gpr 24#5), s0.readReg64 (Reg.gpr 23#5),
        s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
        s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
      simp only [hcons_len]
      wp_done

def kemSecretKeySerdeSerializeOkSpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (self, boxPtr, sk, outPtr) s =>
    ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x8 = outPtr ∧ sk.length = 3168⌝ ∗
    (self ↦₆₄ boxPtr) ∗ ((self + 8#64) ↦₆₄ 0xc60#64) ∗
    (boxPtr ↦ₛ sk) ∗
    cells outPtr 3 ∗
    (stackAt (s.sp - 64#64) allocHookStack ∗ cells (s.sp - 64#64) 8) ∗
    A.pool
  post := fun (self, boxPtr, sk, outPtr) s0 sf =>
    ∃∗ vecPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ vecPtr ≠ 0⌝ ∗
      (self ↦₆₄ boxPtr) ∗ ((self + 8#64) ↦₆₄ 0xc60#64) ∗
      (boxPtr ↦ₛ sk) ∗
      (outPtr ↦₆₄ 0xc61#64) ∗ ((outPtr + 8#64) ↦₆₄ vecPtr) ∗ ((outPtr + 16#64) ↦₆₄ 0xc61#64) ∗
      (vecPtr ↦ₛ (8#8 :: sk)) ∗ A.live vecPtr 3169 1 ∗
      (stackAt (s0.sp - 64#64) allocHookStack ∗ cells (s0.sp - 64#64) 8) ∗
      A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem kemSecretKeySerdeSerialize_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr kemSecretKeySerdeSerializeName)
      (kemSecretKeySerdeSerializeOkSpec A) := by
  unfold kemSecretKeySerdeSerializeOkSpec
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  have hshim := session_shim_ok_at b C ctl abs kemSecretKeySerdeSerializeName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x29568))
    (by simp only [arm64_norm])
  have halloc := alloc_ok_at b C A ctl abs hA kemSecretKeySerdeSerializeName (num% (ls_off% "__rustc::__rust_alloc" - 0x29568))
    (by simp only [arm64_norm])
  have hmemcpy := session_memcpy_region_ok_at b C ctl abs kemSecretKeySerdeSerializeName (num% (ls_off% "memcpy" - 0x29568))
    (by simp only [arm64_norm])
  have hpanic := panic_at_handle_error b C ctl abs kemSecretKeySerdeSerializeName (num% (ls_off% "alloc::raw_vec::handle_error" - 0x29568))
    (by simp only [arm64_norm])
  have hdealloc := dealloc_tail64_ok_at b C A ctl abs hA kemSecretKeySerdeSerializeName (num% (ls_off% "__rustc::__rust_dealloc" - 0x29568))
    (by simp only [arm64_norm])
  simp only [rustDeallocTail64Spec, cells, sepConj_emp, sepExists_sepConj_right,
    sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit] at hdealloc
  clear hA
  wpp_init g s0
  simp only [sepConj_assoc]
  have hfn : libsignalSessionCode.fnOff kemSecretKeySerdeSerializeName = 0x29568 :=
    libsignalSessionCode_fnOff_0x29568_1
  responder_fetches_from b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x29568 0 212
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase b
        (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
        kemSecretKeySerdeSerializeName := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAt] at hshim halloc hmemcpy hpanic hdealloc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
    kemSecretKeySerdeSerializeName = entry
  examples_hide_fetches
  obtain ⟨self, boxPtr, sk, outPtr⟩ := g
  dsimp only at *
  subst h_1 h_2
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 3169 1 := ⟨by decide, hpow2, by decide⟩
  have hcons_len : (8#8 :: sk).length = 3169 := by simp [h]
  apply SepWPp.of_sepWP (mid := entry + 80#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (3169, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace1 => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x29568))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hpanic (by simp only [arm64_norm, *])
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    simp only [hoom1, ite_false, memRegion_3169_cons, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + 132#64)
    wp_steps
    rw [← h]
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5) + 1#64, boxPtr, sk)
    simp only [h] at *
    refine SepWP.fold
      (pointsToBytes_cons_fold (sf_1.readReg64 (Reg.gpr 0#5)) 8#8 sk) (by sep_focus) ?_
    wp_steps
    wp_call hshim ()
    wp_steps
    wp_call halloc (3169, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom2 : sf_4.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      simp only [hoom2, ite_true]
      refine sepWPp_pure_mid fun htrace2 => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x29568))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hpanic (by simp only [arm64_norm, *])
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      simp only [hoom2, ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod2, htrace2⟩ => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      rw [← hcons_len]
      wp_call hmemcpy (sf_4.readReg64 (Reg.gpr 0#5), sf_1.readReg64 (Reg.gpr 0#5), 8#8 :: sk)
      simp only [hcons_len]
      wp_steps
      rw [← hcons_len]
      wp_call hdealloc (sf_1.readReg64 (Reg.gpr 0#5), 8#8 :: sk, 1,
        s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
        s0.readReg64 (Reg.gpr 24#5), s0.readReg64 (Reg.gpr 23#5),
        s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
        s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
      simp only [hcons_len]
      wp_done

/-! ## `preKeyRecordNew_ok` (`0x1e8b4`) -/

abbrev preKeyRecordNewName : String :=
  "<libsignal_protocol::state::prekey::PreKeyRecord>::new"

private theorem stackAt_112_ext_to (sp : BitVec 64) (k : Nat) (hk : k ≤ extHookStack := by decide) :
    stackAt (sp - 112#64) extHookStack ⊢
      memRegion (sp - 16496#64) (extHookStack - k) ∗ stackAt (sp - 112#64) k := by
  rw [stackAt_sub_split (sp - 112#64) extHookStack k hk (by decide)]
  have heq : sp - 112#64 - BitVec.ofNat 64 extHookStack = sp - 16496#64 := by
    simp only [extHookStack]; bv_omega
  rw [heq]
  exact Entails.refl _

private theorem stackAt_112_to_ext (sp : BitVec 64) {sp' : BitVec 64} (k : Nat)
    (hsp : sp' = sp - 112#64) (hk : k ≤ extHookStack := by decide) :
    (memRegion (sp - 16496#64) (extHookStack - k) ∗ stackAt sp' k) ⊢
      stackAt (sp - 112#64) extHookStack := by
  subst hsp
  have h := (stackAt_sub_split (sp - 112#64) extHookStack k hk (by decide)).symm
  have heq : sp - 112#64 - BitVec.ofNat 64 extHookStack = sp - 16496#64 := by
    simp only [extHookStack]; bv_omega
  rw [heq] at h
  exact Entails.of_eq h

private theorem SepWPp_fold_stack_112_to_ext {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (sp : BitVec 64) {sp' : BitVec 64} (k : Nat)
    (hk : k ≤ extHookStack)
    (hf : P = (memRegion (sp - 16496#64) (extHookStack - k) ∗ stackAt sp' k) ∗ F)
    (hsp : sp' = sp - 112#64)
    (h : SepWPp prog ret s (stackAt (sp - 112#64) extHookStack ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.fold (stackAt_112_to_ext sp k hsp hk) hf h

private theorem SepWP_fold_stack_112_to_ext {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (sp : BitVec 64) {sp' : BitVec 64} (k : Nat)
    (hk : k ≤ extHookStack)
    (hf : P = (memRegion (sp - 16496#64) (extHookStack - k) ∗ stackAt sp' k) ∗ F)
    (hsp : sp' = sp - 112#64)
    (h : SepWP prog ret s (stackAt (sp - 112#64) extHookStack ∗ F) Q) :
    SepWP prog ret s P Q :=
  SepWP.fold (stackAt_112_to_ext sp k hsp hk) hf h

private theorem stack_24_to_memRegion_104 (sp v0 v1 v2 : BitVec 64) :
    (((sp - 104#64) ↦₆₄ v0) ∗ ((sp - 96#64) ↦₆₄ v1) ∗ ((sp - 88#64) ↦₆₄ v2)) ⊢
      memRegion (sp - 104#64) 24 := by
  have h := mr_split_24 (sp - 104#64) 0
  have h0 : sp - 104#64 + BitVec.ofNat 64 0 = sp - 104#64 := by bv_omega
  have h1 : sp - 104#64 + BitVec.ofNat 64 (0 + 8) = sp - 96#64 := by bv_omega
  have h2 : sp - 104#64 + BitVec.ofNat 64 (0 + 8 + 8) = sp - 88#64 := by bv_omega
  rw [h0, h1, h2] at h
  rw [h]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))

private theorem vecU8At_priv_expose_104 (A : RustAlloc) (sp cap ptr : BitVec 64)
    (k : List.Vector (BitVec 8) 32) :
    vecU8At A (sp - 104#64) cap ptr k.toList ⊢
      ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ (cap == 0#64) = false ∧ ptr ≠ 0⌝ ∗
      ((sp - 104#64) ↦₆₄ cap) ∗ ((sp - 96#64) ↦₆₄ ptr) ∗ ((sp - 88#64) ↦₆₄ 32#64) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ k.toList) ∗ memRegion (ptr + 32#64) (cap.toNat - 32) := by
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader vecU8Buf
  have hlen : k.toList.length = 32 := k.toList_length
  have h1 : sp - 104#64 + 8#64 = sp - 96#64 := by bv_omega
  have h2 : sp - 104#64 + 16#64 = sp - 88#64 := by bv_omega
  rw [hlen, h1, h2]
  simp only [BitVec.ofNat_eq_ofNat, sepConj_assoc]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨hle, hlt, hptr⟩
  have hc0 : cap ≠ 0#64 := by intro h; subst h; simp at hle
  have hc0_beq : (cap == 0#64) = false := beq_false_of_ne hc0
  apply Entails.pure_right ⟨hle, hlt, hc0_beq, hptr⟩
  rw [ite_eq_right_iff.mpr (fun h => (hc0 h).elim)]
  exact Entails.refl _

private theorem vecU8_priv_expose_104 (A : RustAlloc) (sp : BitVec 64)
    (k : List.Vector (BitVec 8) 32) :
    vecU8 A (sp - 104#64) k.toList ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ (cap == 0#64) = false ∧ ptr ≠ 0⌝ ∗
        ((sp - 104#64) ↦₆₄ cap) ∗ ((sp - 96#64) ↦₆₄ ptr) ∗ ((sp - 88#64) ↦₆₄ 32#64) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ k.toList) ∗ memRegion (ptr + 32#64) (cap.toNat - 32) := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  exact Entails.sepExists_right cap
    (Entails.sepExists_right ptr (vecU8At_priv_expose_104 A sp cap ptr k))

def preKeyRecordNewOkSpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × PublicKey × List.Vector (BitVec 8) 32 × BitVec 64) where
  pre := fun (id, kpPtr, pk, priv, outPtr) s =>
    (∃∗ v_id : BitVec 32,
      ⌜s.readReg64 .x0 = id ∧ s.readReg64 .x1 = kpPtr ∧ s.readReg64 .x8 = outPtr⌝ ∗
      (kpPtr ↦ₛ pk.bytes.toList) ∗
      ((kpPtr + 32#64) ↦ₛ priv.toList) ∗
      cells outPtr 6 ∗ ((outPtr + 48#64) ↦₃₂ v_id) ∗
      (stackAt (s.sp - 112#64) extHookStack ∗ cells (s.sp - 104#64) 13) ∗
      A.pool)
  post := fun (id, kpPtr, pk, priv, outPtr) s0 sf =>
    ∃∗ pkVecPtr : BitVec 64, ∃∗ privVecPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ pkVecPtr ≠ 0 ∧ privVecPtr ≠ 0⌝ ∗
      (kpPtr ↦ₛ pk.bytes.toList) ∗
      ((kpPtr + 32#64) ↦ₛ priv.toList) ∗
      (outPtr ↦₆₄ 33#64) ∗ ((outPtr + 8#64) ↦₆₄ pkVecPtr) ∗
      ((outPtr + 16#64) ↦₆₄ 33#64) ∗ ((outPtr + 24#64) ↦₆₄ 32#64) ∗
      ((outPtr + 32#64) ↦₆₄ privVecPtr) ∗ ((outPtr + 40#64) ↦₆₄ 32#64) ∗
      ((outPtr + 48#64) ↦₃₂ id.truncate 32) ∗
      (pkVecPtr ↦ₛ pk.serialize) ∗ A.live pkVecPtr 33 1 ∗
      (privVecPtr ↦ₛ priv.toList) ∗ A.live privVecPtr 32 1 ∗
      (stackAt (s0.sp - 112#64) extHookStack ∗ cells (s0.sp - 104#64) 13) ∗
      A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem preKeyRecordNew_ok {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyRecordNewName)
      (preKeyRecordNewOkSpec A) := by
  unfold preKeyRecordNewOkSpec
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  have hpubser := subroutine_ok_rel2 (public_key_serialize_ok (b := b) (C := C) (ctl := ctl) hA)
    libsignalSessionCode_fnOff_0x3e2c4 libsignalSessionCode_fnOff_0x1e8b4 (k := 129552) (by decide)
  have hprivser := priv_serialize_ok_at b C A ctl abs hA preKeyRecordNewName 130828
    (by simp only [arm64_norm])
  have hshim := session_shim_ok_at b C ctl abs preKeyRecordNewName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x1e8b4))
    (by simp only [arm64_norm])
  have halloc := alloc_ok_at b C A ctl abs hA preKeyRecordNewName (num% (ls_off% "__rustc::__rust_alloc" - 0x1e8b4))
    (by simp only [arm64_norm])
  have hdealloc := dealloc_ok_at b C A ctl abs hA preKeyRecordNewName (num% (ls_off% "__rustc::__rust_dealloc" - 0x1e8b4))
    (by simp only [arm64_norm])
  have hmemcpy := session_memcpy_region_ok_at b C ctl abs preKeyRecordNewName (num% (ls_off% "memcpy" - 0x1e8b4))
    (by simp only [arm64_norm])
  have hpanic := panic_at_handle_error b C ctl abs preKeyRecordNewName (num% (ls_off% "alloc::raw_vec::handle_error" - 0x1e8b4))
    (by simp only [arm64_norm])
  clear hA
  wpp_init g s0
  simp only [sepConj_assoc]
  have hfn : libsignalSessionCode.fnOff preKeyRecordNewName = 0x1e8b4 :=
    libsignalSessionCode_fnOff_0x1e8b4
  responder_fetches_from b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1e8b4 0 324
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase b
        (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr preKeyRecordNewName := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAt] at hpubser hprivser hshim halloc hdealloc hmemcpy hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr preKeyRecordNewName = entry
  examples_hide_fetches
  obtain ⟨id, kpPtr, pk, priv, outPtr⟩ := g
  dsimp only at *
  subst h h_1 h_2
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay33 : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  have hlay32 : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  have hser_len : pk.serialize.length = 33 := by
    simp [PublicKey.serialize, List.Vector.toList_length]
  have hpriv_len : priv.toList.length = 32 := priv.toList_length
  refine SepWPp.fold (stackAt_112_ext_to s0.sp publicKeySerializeStack) (by sep_focus) ?_
  apply SepWPp.of_sepWP (mid := entry + 129552#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPp_call_pk_gen hpubser pk
    (ret_pc := entry + 48#64) (sp_call := s0.sp - 112#64) (selfPtr := s0.readReg64 (Reg.gpr 1#5))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (spAligned_sub_112 hsp_align rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus)
    fun sf_pk hpc_pk hrun_pk hsp_pk hcs_pk => ?_
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_pk
  rcases hcs_pk with
    ⟨hcs_k19, hcs_k20, hcs_k21, hcs_k22, hcs_k23, hcs_k24, hcs_k25, hcs_k26, hcs_k27, hcs_k28,
      hcs_k29⟩
  simp only [arm64_norm, *]
    at hcs_k19 hcs_k20 hcs_k21 hcs_k22 hcs_k23 hcs_k24 hcs_k25 hcs_k26 hcs_k27 hcs_k28 hcs_k29
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1, htrace0⟩ => ?_
  refine SepWPp.fold (boxU8Buf_pk_expose A (sf_pk.readReg64 .x0) pk) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hbox_ne => ?_
  refine SepWPp_fold_stack_112_to_ext s0.sp publicKeySerializeStack
    (by decide) (by sep_focus) rfl ?_
  refine SepWPp.fold (stackAt_112_ext_to s0.sp allocHookStack) (by sep_focus) ?_
  apply SepWPp.of_sepWP (mid := entry + 100#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace1 => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x1e8b4))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hpanic (by simp only [arm64_norm, *])
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    simp only [hoom1, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + 130828#64)
    wp_steps
    rw [← hser_len]
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), sf_pk.readReg64 (Reg.gpr 0#5), pk.serialize)
    simp only [hser_len]
    refine SepWP.fold (pk_buf_to_memRegion (sf_pk.readReg64 .x0) pk) (by sep_focus) ?_
    wp_steps
    wp_call hdealloc (sf_pk.readReg64 (Reg.gpr 0#5), 33, 1)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPp_fold_stack_112_to_ext s0.sp allocHookStack
      (by decide) (by sep_focus) (by simp only [arm64_norm, *]) ?_
    refine SepWPp.fold (stack_24_to_memRegion_104 s0.sp v_stk_1 v_stk_2 v_stk_3) (by sep_focus) ?_
    refine SepWPp_call_priv_gen hprivser priv.toList
      (ret_pc := entry + 148#64) (sp_call := s0.sp - 112#64)
      (selfPtr := s0.readReg64 (Reg.gpr 1#5) + 32#64) (retPtr := s0.sp - 104#64)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (spAligned_sub_112 hsp_align rfl)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus)
      fun sf_priv hpc_priv hrun_priv hsp_priv hcs_priv => ?_
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_priv
    rcases hcs_priv with
      ⟨hcs_p19, hcs_p20, hcs_p21, hcs_p22, hcs_p23, hcs_p24, hcs_p25, hcs_p26, hcs_p27, hcs_p28,
        hcs_p29⟩
    simp only [arm64_norm, *]
      at hcs_p19 hcs_p20 hcs_p21 hcs_p22 hcs_p23 hcs_p24 hcs_p25 hcs_p26 hcs_p27 hcs_p28 hcs_p29
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hpriv_tr => ?_
    refine SepWPp.fold (vecU8_priv_expose_104 A s0.sp priv) (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun privTempCap => SepWPp.exists_elim fun privTempPtr => ?_
    refine SepWPp.pure_elim fun ⟨hpt_le, hpt_lt, hpt_c0, hpt_ptr⟩ => ?_
    refine SepWPp.fold (stackAt_112_ext_to s0.sp allocHookStack) (by sep_focus) ?_
    apply SepWPp.of_sepWP (mid := entry + 224#64)
    wp_steps
    wp_call hshim ()
    wp_steps
    wp_call halloc (32, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom2 : sf_5.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      simp only [hoom2, ite_true]
      refine sepWPp_pure_mid fun htrace2 => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x1e8b4))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hpanic (by simp only [arm64_norm, *])
    · have hoom2_64 : sf_5.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      simp only [hoom2, ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod2, htrace2⟩ => ?_
      have hpt_layout : LayoutOk privTempCap.toNat 1 :=
        layoutOk_of_pos_lt (Nat.lt_of_lt_of_le (by decide : 0 < 32) hpt_le) hpt_lt
      apply SepWPp.of_sepWP_ret
      wp_steps
      rw [show memRegion (sf_5.readReg64 (Reg.gpr 0#5)) 32 =
        memRegion (sf_5.readReg64 (Reg.gpr 0#5)) priv.toList.length by rw [hpriv_len]]
      wp_call hmemcpy (sf_5.readReg64 (Reg.gpr 0#5), privTempPtr, priv.toList)
      refine SepWP.fold
        (priv_buf_to_memRegion privTempPtr privTempCap priv hpt_le hpt_lt) (by sep_focus) ?_
      wp_steps
      wp_call hdealloc (privTempPtr, privTempCap.toNat, 1)
      wp_steps
      refine SepWP_fold_stack_112_to_ext s0.sp allocHookStack
        (by decide) (by sep_focus) (by simp only [arm64_norm, *]) ?_
      wp_done

/-! ## Relocatable `[LibsignalPlacement]` Contracts -/

set_option maxHeartbeats 1200000 in
theorem curveKeyPairFromPubPriv_placed_ok [LibsignalPlacement]
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_209).rebase (blkPl_209).base H) (blkPl_209).base
      curveKeyPairFromPubPrivOkSpec := by
  unfold curveKeyPairFromPubPrivOkSpec
  simp only [memRegion_65_cells, cells, sepConj_emp, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]
  wp_init x s0
  obtain ⟨pubPtr, pk, privPtr, sk, outPtr⟩ := x
  dsimp only at *
  subst h_1 h_3 h_5
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk, _⟩ := exists_bytes32_of_length_32 h_6
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13, sk14, sk15,
    sk16, sk17, sk18, sk19, sk20, sk21, sk22, sk23, sk24, sk25, sk26, sk27, sk28, sk29, sk30, sk31,
    hsk, hsk_clamp⟩ := exists_bytes32_of_length_32 h
  wp_pull_exists
  rw [pointsToBytes_cons, hpk (s0.readReg64 (.gpr 0#5) + 1#64),
    hsk (s0.readReg64 (.gpr 2#5)),
    hpk (s0.readReg64 (.gpr 8#5) + 1#64),
    hsk_clamp (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 1#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 9#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 17#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 25#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 41#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 49#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 57#64)]
  dsimp only [bytes32At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

set_option maxHeartbeats 1200000 in
theorem curveKeyPairSerde_placed_ok [LibsignalPlacement]
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_112).rebase (blkPl_112).base H) (blkPl_112).base
      (withLsCodeLoaded lsmpl curveKeyPairSerdeOkSpec) := by
  unfold curveKeyPairSerdeOkSpec
  have hinner := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_112).rebase (blkPl_112).base H) (entry := lsmpl.base 209)
    (curveKeyPairFromPubPriv_placed_ok H)
  simp only [withLsCl, curveKeyPairFromPubPrivOkSpec, cells, sepExists_sepConj_right,
    sepConj_emp, bv_sub_add_lit', BitVec.reduceSub] at hinner
  wp_init x s0
  obtain ⟨pubPtr, pk, privPtr, sk, outPtr⟩ := x
  dsimp only [withLsCodeLoaded] at *
  subst h_2 h_4 h_6
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk, _⟩ := exists_bytes32_of_length_32 h_7
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13, sk14, sk15,
    sk16, sk17, sk18, sk19, sk20, sk21, sk22, sk23, sk24, sk25, sk26, sk27, sk28, sk29, sk30, sk31,
    _, hsk_clamp⟩ := exists_bytes32_of_length_32 h_1
  rw (occs := .pos [1]) [cells_8_sub176 s0.sp]
  rw (occs := .pos [1]) [cells_14_curveKeyPairSerde s0.sp]
  rw [memRegion_8_bytes (s0.sp - 8#64)]
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepExists_sepConj_left, sepExists_sepConj_right]
  wp_pull_exists
  wp_steps_lscl (lsmpl.base 209)
  wp_call hinner (s0.readReg64 (.gpr 0#5), pk, s0.readReg64 (.gpr 2#5), sk, s0.sp - 104#64)
  rw [memRegion_65_bytes8 (s0.readReg64 (.gpr 8#5))]
  simp only [ProofLib.memRegion_eight]
  wp_pull_exists
  rw [hpk (s0.sp - 103#64),
    hsk_clamp (s0.sp - 71#64),
    hpk (s0.readReg64 (.gpr 8#5) + 1#64),
    hsk_clamp (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 1#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 9#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 17#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 25#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 41#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 49#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 57#64)]
  rw [cells_8_sub176_mr s0.sp, cells_14_curveKeyPairSerde_mr s0.sp]
  dsimp only [memRegion_8_bytes_mr_rhs, bytes32At]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_steps
  wp_done

set_option maxHeartbeats 1200000 in
theorem preKeyRecordKeyPair_placed_ok [LibsignalPlacement]
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_67).rebase (blkPl_67).base H) (blkPl_67).base
      (withLsCodeLoaded lsmpl preKeyRecordKeyPairOkSpec) := by
  unfold preKeyRecordKeyPairOkSpec
  have hinner := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_67).rebase (blkPl_67).base H) (entry := lsmpl.base 209)
    (curveKeyPairFromPubPriv_placed_ok H)
  simp only [withLsCl, curveKeyPairFromPubPrivOkSpec, cells, sepExists_sepConj_right,
    sepConj_emp, bv_sub_add_lit', BitVec.reduceSub] at hinner
  wp_init x s0
  obtain ⟨recPtr, pubPtr, pk, privPtr, sk, outPtr⟩ := x
  dsimp only [withLsCodeLoaded] at *
  subst h_2 h_3
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk, _⟩ := exists_bytes32_of_length_32 h_4
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13, sk14, sk15,
    sk16, sk17, sk18, sk19, sk20, sk21, sk22, sk23, sk24, sk25, sk26, sk27, sk28, sk29, sk30, sk31,
    _, hsk_clamp⟩ := exists_bytes32_of_length_32 h_1
  rw (occs := .pos [1]) [cells_8_sub176 s0.sp]
  rw (occs := .pos [1]) [cells_14_curveKeyPairSerde s0.sp]
  rw [memRegion_8_bytes (s0.sp - 8#64)]
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepExists_sepConj_left, sepExists_sepConj_right]
  wp_pull_exists
  wp_steps_lscl (lsmpl.base 209)
  wp_call hinner (pubPtr, pk, privPtr, sk, s0.sp - 104#64)
  rw [memRegion_65_bytes8 (s0.readReg64 (.gpr 8#5))]
  simp only [ProofLib.memRegion_eight]
  wp_pull_exists
  rw [hpk (s0.sp - 103#64),
    hsk_clamp (s0.sp - 71#64),
    hpk (s0.readReg64 (.gpr 8#5) + 1#64),
    hsk_clamp (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 1#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 9#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 17#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 25#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 41#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 49#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 57#64)]
  rw [cells_8_sub176_mr s0.sp, cells_14_curveKeyPairSerde_mr s0.sp]
  dsimp only [memRegion_8_bytes_mr_rhs, bytes32At]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_steps
  wp_done

theorem privKeySerdeSerialize_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_107).rebase (blkPl_107).base H) (blkPl_107).base
      (withLsCodeLoaded lsmpl (privSerializeSpec A)) := by
  have hinner := ls_subroutine_ok_of_block
    (callerProg := (blkPC_107).rebase (blkPl_107).base H)
    (entry := lsmpl.base 208)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (privSerialize_placed_ok hshim halloc hpanic))
  exact subroutine_ok_of_b (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm])
    rfl (by intros; rfl) hinner (by intros; rfl) (by intros; rfl) (by intros; rfl)

abbrev lsAllocHandleErrorSym : String :=
  "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error"

set_option maxHeartbeats 1200000 in
theorem kemKeyPairFromPubPriv_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic_alloc : H lsAllocHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_70).rebase (blkPl_70).base H) (blkPl_70).base
      (kemKeyPairFromPubPrivOkSpec A) := by
  unfold kemKeyPairFromPubPrivOkSpec
  simp only [stackAt_kemKeyPairFromPubPriv]
  simp only [cells, sepConj_emp, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hshim_ok : subroutine_ok ((blkPC_70).rebase (blkPl_70).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec :=
    ls_hook_ok_of_mem hshim
  have halloc_ok : subroutine_ok ((blkPC_70).rebase (blkPl_70).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) :=
    ls_hook_ok_of_mem halloc
  have hmemcpy_ok : subroutine_ok ((blkPC_70).rebase (blkPl_70).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec :=
    ls_hook_ok_of_mem hmemcpy
  have hpanic_ok : ((blkPC_70).rebase (blkPl_70).base H).externAt? (lsρ lsAllocHandleErrorSym) =
      some Rust.panicked :=
    (ls_externAt?_of_mem (sym := lsAllocHandleErrorSym)).trans hpanic_alloc
  wpp_init g s0
  simp only [sepConj_assoc]
  obtain ⟨pubPtr, pk, privPtr, sk, outPtr⟩ := g
  dsimp only at *
  subst h_1 h_3 h_5
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay1 : LayoutOk 1568 1 := ⟨by decide, hpow2, by decide⟩
  have hlay2 : LayoutOk 3168 1 := ⟨by decide, hpow2, by decide⟩
  rw [pointsToBytes_cons (s0.readReg64 (.gpr 0#5)),
    pointsToBytes_cons (s0.readReg64 (.gpr 2#5))]
  apply SepWPp.of_sepWP (mid := (blkPl_70).base + 76#64)
  wp_steps
  wp_call hshim_ok ()
  wp_steps
  wp_call halloc_ok (1568, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace1 => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsAllocHandleErrorSym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hpanic_ok (by simp only [arm64_norm, *])
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    simp only [hoom1, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_70).base + 140#64)
    wp_steps
    rw [← h_6]
    wp_call hmemcpy_ok (sf_1.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 0#5) + 1#64, pk)
    simp only [h_6] at *
    wp_steps
    wp_call hshim_ok ()
    wp_steps
    wp_call halloc_ok (3168, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom2 : sf_4.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      simp only [hoom2, ite_true]
      refine sepWPp_pure_mid fun htrace2 => ?_
      apply SepWPp.of_sepWP (mid := lsρ lsAllocHandleErrorSym)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hpanic_ok (by simp only [arm64_norm, *])
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      simp only [hoom2, ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod2, htrace2⟩ => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      rw [← h]
      wp_call hmemcpy_ok (sf_4.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 2#5) + 1#64, sk)
      simp only [h] at *
      wp_steps
      wp_done

theorem kemKeyPairSerde_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic_alloc : H lsAllocHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_113).rebase (blkPl_113).base H) (blkPl_113).base
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec A)) := by
  have hinner := ls_subroutine_ok_of_block
    (callerProg := (blkPC_113).rebase (blkPl_113).base H)
    (entry := lsmpl.base 70)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (kemKeyPairFromPubPriv_placed_ok hshim halloc hmemcpy hpanic_alloc))
  exact subroutine_ok_of_b (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm])
    rfl (by intros; rfl) hinner (by intros; rfl) (by intros; rfl) (by intros; rfl)

private theorem dealloc_tail48_of_dealloc {prog : Program} {addr : BitVec 64} {A : RustAlloc}
    (hdealloc : subroutine_ok prog addr (rustDeallocSpec A)) :
    subroutine_ok prog addr (rustDeallocTail48Spec A) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨p, bs, align, v0, v1, v2, v3, v4, v5⟩ R s0 hpc hrun hpre hsp
  have hcells :
      (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
        ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
        ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ⊢ cells (s0.sp - 48#64) 6 := by
    have h := pointsTo64_6_entails_cells (s0.sp - 48#64) v0 v1 v2 v3 v4 v5
    have ha1 : s0.sp - 48#64 + 8#64 = s0.sp - 40#64 := by bv_lin
    have ha2 : s0.sp - 48#64 + 16#64 = s0.sp - 32#64 := by bv_lin
    have ha3 : s0.sp - 48#64 + 24#64 = s0.sp - 24#64 := by bv_lin
    have ha4 : s0.sp - 48#64 + 32#64 = s0.sp - 16#64 := by bv_lin
    have ha5 : s0.sp - 48#64 + 40#64 = s0.sp - 8#64 := by bv_lin
    rwa [ha1, ha2, ha3, ha4, ha5] at h
  have hbs_mem := pointsToBytes_entails_memRegion p bs
  have hpre2 : s0.mem ⊨ (rustDeallocSpec A).pre (p, bs.length, align) s0 ∗
      (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗ R) := by
    unfold rustDeallocTail48Spec at hpre
    unfold rustDeallocSpec
    dsimp only at hpre ⊢
    have h1 : s0.mem ⊨
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align⌝ ∗
          A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
          (stackAt (s0.sp - 48#64) allocHookStack ∗ cells (s0.sp - 48#64) 6)) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hpre
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hbs_mem (sepConj_mono_right hcells))))
    rw [← stackAt_add_48, stackAt_add_48_comm] at h1
    exact (by ac_rfl :
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align⌝ ∗
        A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗ stackAt s0.sp allocHookStack)) ∗ R) =
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align⌝ ∗
        A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗ stackAt s0.sp allocHookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗ R))) ▸ h1
  refine (hdealloc.to_outcome (p, bs.length, align)
    (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗ R) s0 hpc hrun hpre2 hsp).mono_outcome
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    unfold rustDeallocTail48Spec
    unfold rustDeallocSpec at hpost
    dsimp only at hpost ⊢
    rw [← stackAt_add_48, stackAt_add_48_comm]
    exact (by ac_rfl :
      ((⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp allocHookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗ R)) =
      ((⌜sf.trace = s0.trace⌝ ∗ A.pool ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗
          stackAt s0.sp allocHookStack)) ∗ R)) ▸ hpost
  · exact False.elim (not_satisfies_false_sepConj hpost)
  · exact False.elim (not_satisfies_false_sepConj hpost)
  · exact False.elim (not_satisfies_false_sepConj hpost)

private theorem dealloc_tail64_of_dealloc {prog : Program} {addr : BitVec 64} {A : RustAlloc}
    (hdealloc : subroutine_ok prog addr (rustDeallocSpec A)) :
    subroutine_ok prog addr (rustDeallocTail64Spec A) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨p, bs, align, v0, v1, v2, v3, v4, v5, v6, v7⟩ R s0 hpc hrun hpre hsp
  have hcells :
      (((s0.sp - 64#64) ↦₆₄ v0) ∗ ((s0.sp - 56#64) ↦₆₄ v1) ∗
        ((s0.sp - 48#64) ↦₆₄ v2) ∗ ((s0.sp - 40#64) ↦₆₄ v3) ∗
        ((s0.sp - 32#64) ↦₆₄ v4) ∗ ((s0.sp - 24#64) ↦₆₄ v5) ∗
        ((s0.sp - 16#64) ↦₆₄ v6) ∗ ((s0.sp - 8#64) ↦₆₄ v7)) ⊢ cells (s0.sp - 64#64) 8 := by
    have h := pointsTo64_8_entails_cells (s0.sp - 64#64) v0 v1 v2 v3 v4 v5 v6 v7
    have ha1 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_lin
    have ha2 : s0.sp - 64#64 + 16#64 = s0.sp - 48#64 := by bv_lin
    have ha3 : s0.sp - 64#64 + 24#64 = s0.sp - 40#64 := by bv_lin
    have ha4 : s0.sp - 64#64 + 32#64 = s0.sp - 32#64 := by bv_lin
    have ha5 : s0.sp - 64#64 + 40#64 = s0.sp - 24#64 := by bv_lin
    have ha6 : s0.sp - 64#64 + 48#64 = s0.sp - 16#64 := by bv_lin
    have ha7 : s0.sp - 64#64 + 56#64 = s0.sp - 8#64 := by bv_lin
    rwa [ha1, ha2, ha3, ha4, ha5, ha6, ha7] at h
  have hbs_mem := pointsToBytes_entails_memRegion p bs
  have hpre2 : s0.mem ⊨ (rustDeallocSpec A).pre (p, bs.length, align) s0 ∗
      (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗ R) := by
    unfold rustDeallocTail64Spec at hpre
    unfold rustDeallocSpec
    dsimp only at hpre ⊢
    have h1 : s0.mem ⊨
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align⌝ ∗
          A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
          (stackAt (s0.sp - 64#64) allocHookStack ∗ cells (s0.sp - 64#64) 8)) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hpre
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hbs_mem (sepConj_mono_right hcells))))
    rw [← stackAt_add_64, stackAt_add_64_comm] at h1
    exact (by ac_rfl :
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align⌝ ∗
        A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗ stackAt s0.sp allocHookStack)) ∗ R) =
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align⌝ ∗
        A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗ stackAt s0.sp allocHookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗ R))) ▸ h1
  refine (hdealloc.to_outcome (p, bs.length, align)
    (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗ R) s0 hpc hrun hpre2 hsp).mono_outcome
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    unfold rustDeallocTail64Spec
    unfold rustDeallocSpec at hpost
    dsimp only at hpost ⊢
    rw [← stackAt_add_64, stackAt_add_64_comm]
    exact (by ac_rfl :
      ((⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp allocHookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗ R)) =
      ((⌜sf.trace = s0.trace⌝ ∗ A.pool ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗
          stackAt s0.sp allocHookStack)) ∗ R)) ▸ hpost
  · exact False.elim (not_satisfies_false_sepConj hpost)
  · exact False.elim (not_satisfies_false_sepConj hpost)
  · exact False.elim (not_satisfies_false_sepConj hpost)

theorem kemPubKeySerdeSerialize_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_109).rebase (blkPl_109).base H) (blkPl_109).base
      (kemPubKeySerdeSerializeOkSpec A) := by
  unfold kemPubKeySerdeSerializeOkSpec
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  have hshim_ok : subroutine_ok ((blkPC_109).rebase (blkPl_109).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec :=
    ls_hook_ok_of_mem hshim
  have halloc_ok : subroutine_ok ((blkPC_109).rebase (blkPl_109).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) :=
    ls_hook_ok_of_mem halloc
  have hmemcpy_ok : subroutine_ok ((blkPC_109).rebase (blkPl_109).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec :=
    ls_hook_ok_of_mem hmemcpy
  have hpanic_ok : ((blkPC_109).rebase (blkPl_109).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked :=
    (ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic
  have hdealloc_ok := dealloc_tail64_of_dealloc
    (ls_hook_ok_of_mem (prog := (blkPC_109).rebase (blkPl_109).base H) hdealloc)
  simp only [rustDeallocTail64Spec, cells, sepConj_emp, sepExists_sepConj_right,
    sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit] at hdealloc_ok
  wpp_init g s0
  simp only [sepConj_assoc]
  obtain ⟨self, boxPtr, pk, outPtr⟩ := g
  dsimp only at *
  subst h_1 h_2
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 1569 1 := ⟨by decide, hpow2, by decide⟩
  have hcons_len : (8#8 :: pk).length = 1569 := by simp [h]
  apply SepWPp.of_sepWP (mid := (blkPl_109).base + 80#64)
  wp_steps
  wp_call hshim_ok ()
  wp_steps
  wp_call halloc_ok (1569, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace1 => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hpanic_ok (by simp only [arm64_norm, *])
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    simp only [hoom1, ite_false, memRegion_1569_cons, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_109).base + 132#64)
    wp_steps
    rw [← h]
    wp_call hmemcpy_ok (sf_1.readReg64 (Reg.gpr 0#5) + 1#64, boxPtr, pk)
    simp only [h] at *
    refine SepWP.fold
      (pointsToBytes_cons_fold (sf_1.readReg64 (Reg.gpr 0#5)) 8#8 pk) (by sep_focus) ?_
    wp_steps
    wp_call hshim_ok ()
    wp_steps
    wp_call halloc_ok (1569, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom2 : sf_4.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      simp only [hoom2, ite_true]
      refine sepWPp_pure_mid fun htrace2 => ?_
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hpanic_ok (by simp only [arm64_norm, *])
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      simp only [hoom2, ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod2, htrace2⟩ => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      rw [← hcons_len]
      wp_call hmemcpy_ok (sf_4.readReg64 (Reg.gpr 0#5), sf_1.readReg64 (Reg.gpr 0#5), 8#8 :: pk)
      simp only [hcons_len]
      wp_steps
      rw [← hcons_len]
      wp_call hdealloc_ok (sf_1.readReg64 (Reg.gpr 0#5), 8#8 :: pk, 1,
        s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
        s0.readReg64 (Reg.gpr 24#5), s0.readReg64 (Reg.gpr 23#5),
        s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
        s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
      simp only [hcons_len]
      wp_done

theorem kemSecretKeySerdeSerialize_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_109).rebase (blkPl_109).base H) (blkPl_109).base
      (kemSecretKeySerdeSerializeOkSpec A) := by
  unfold kemSecretKeySerdeSerializeOkSpec
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  have hshim_ok : subroutine_ok ((blkPC_109).rebase (blkPl_109).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec :=
    ls_hook_ok_of_mem hshim
  have halloc_ok : subroutine_ok ((blkPC_109).rebase (blkPl_109).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) :=
    ls_hook_ok_of_mem halloc
  have hmemcpy_ok : subroutine_ok ((blkPC_109).rebase (blkPl_109).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec :=
    ls_hook_ok_of_mem hmemcpy
  have hpanic_ok : ((blkPC_109).rebase (blkPl_109).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked :=
    (ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic
  have hdealloc_ok := dealloc_tail64_of_dealloc
    (ls_hook_ok_of_mem (prog := (blkPC_109).rebase (blkPl_109).base H) hdealloc)
  simp only [rustDeallocTail64Spec, cells, sepConj_emp, sepExists_sepConj_right,
    sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit] at hdealloc_ok
  wpp_init g s0
  simp only [sepConj_assoc]
  obtain ⟨self, boxPtr, sk, outPtr⟩ := g
  dsimp only at *
  subst h_1 h_2
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 3169 1 := ⟨by decide, hpow2, by decide⟩
  have hcons_len : (8#8 :: sk).length = 3169 := by simp [h]
  apply SepWPp.of_sepWP (mid := (blkPl_109).base + 80#64)
  wp_steps
  wp_call hshim_ok ()
  wp_steps
  wp_call halloc_ok (3169, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace1 => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hpanic_ok (by simp only [arm64_norm, *])
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    simp only [hoom1, ite_false, memRegion_3169_cons, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_109).base + 132#64)
    wp_steps
    rw [← h]
    wp_call hmemcpy_ok (sf_1.readReg64 (Reg.gpr 0#5) + 1#64, boxPtr, sk)
    simp only [h] at *
    refine SepWP.fold
      (pointsToBytes_cons_fold (sf_1.readReg64 (Reg.gpr 0#5)) 8#8 sk) (by sep_focus) ?_
    wp_steps
    wp_call hshim_ok ()
    wp_steps
    wp_call halloc_ok (3169, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom2 : sf_4.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      simp only [hoom2, ite_true]
      refine sepWPp_pure_mid fun htrace2 => ?_
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hpanic_ok (by simp only [arm64_norm, *])
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      simp only [hoom2, ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod2, htrace2⟩ => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      rw [← hcons_len]
      wp_call hmemcpy_ok (sf_4.readReg64 (Reg.gpr 0#5), sf_1.readReg64 (Reg.gpr 0#5), 8#8 :: sk)
      simp only [hcons_len]
      wp_steps
      rw [← hcons_len]
      wp_call hdealloc_ok (sf_1.readReg64 (Reg.gpr 0#5), 8#8 :: sk, 1,
        s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
        s0.readReg64 (Reg.gpr 24#5), s0.readReg64 (Reg.gpr 23#5),
        s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
        s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
      simp only [hcons_len]
      wp_done

private theorem sepWPp_of_sepWP_lscl {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {pl : Obj.MultiPlacement} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h (fun _ _ _ _ hclf hnext => hnext hclf))

private def pkClSpecAt [LibsignalPlacement] (A : RustAlloc) (m : Memory) :
    Spec PublicKeySerializeCall where
  pre := fun ⟨self, pk⟩ s' =>
    ⌜s'.readReg64 .x0 = self ∧ s'.mem = m⌝ ∗
      ((self ↦ₛ pk.bytes.toList) ∗ A.pool ∗ stackAt s'.sp publicKeySerializeStack)
  post := fun ⟨self, pk⟩ s0 sf =>
    ⌜LibsignalCodeLoaded lsmpl sf.mem ∧ sf.readReg64 .x1 = 33#64 ∧ sf.trace = s0.trace⌝ ∗
      (self ↦ₛ pk.bytes.toList) ∗ boxU8Buf A (sf.readReg64 .x0) pk.serialize ∗
      A.pool ∗ stackAt s0.sp publicKeySerializeStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem subroutine_ok_pkClSpecAt [LibsignalPlacement] {prog : Program}
    {entry : BitVec 64} {A : RustAlloc} {m : Memory}
    (hpk : subroutine_ok prog entry (withLsCl lsmpl (publicKeySerializeSpec A)))
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok prog entry (pkClSpecAt A m) := by
  refine subroutine_ok_mono hpk
    (fun ⟨self, pk⟩ R s' hpre => ?_)
    (fun ⟨self, pk⟩ R s0 sf hpost => ?_)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h)
  · dsimp only [pkClSpecAt] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hm⟩, hrest⟩
    have hcl' : LibsignalCodeLoaded lsmpl s'.mem := hm ▸ hcl
    dsimp only [withLsCl, publicKeySerializeSpec, publicKeySerializeSpecWithStack, Spec.allowPanicWhen]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0, hrest⟩
  · dsimp only [withLsCl, publicKeySerializeSpec, publicKeySerializeSpecWithStack, Spec.allowPanicWhen] at hpost
    dsimp only [pkClSpecAt]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hcl_f, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx1, htr⟩, hrest⟩
    exact ⟨⟨hcl_f, hx1, htr⟩, hrest⟩

private theorem SepWPp_call_pk_gen_cl [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s0 s : State} {P F R : SepProp} {Q : State → SepProp → Prop}
    {entry ret_pc sp_call selfPtr : BitVec 64} {A : RustAlloc}
    (hpk : subroutine_ok prog entry (withLsCl lsmpl (publicKeySerializeSpec A)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (pk : PublicKey)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hsp_eq : s.sp = sp_call)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = selfPtr)
    (hP : P = ((selfPtr ↦ₛ pk.bytes.toList) ∗ A.pool ∗
      stackAt sp_call publicKeySerializeStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog ret sf
        ((⌜sf.readReg64 Reg.x1 = 33#64 ∧ sf.trace = s0.trace⌝ ∗
          (selfPtr ↦ₛ pk.bytes.toList) ∗
          boxU8Buf A (sf.readReg64 Reg.x0) pk.serialize ∗
          A.pool ∗ stackAt sp_call publicKeySerializeStack) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  have hpk' := subroutine_ok_pkClSpecAt hpk hcl
  have hx0' : s.readReg64 Reg.x0 = selfPtr ∧ s.mem = s.mem := ⟨hx0, rfl⟩
  refine SepWPp.call_frame (x := ⟨selfPtr, pk⟩) hpk' hpc hrun
    (by unfold State.spAligned; rw [hsp_eq]; exact hsp_align) hlr ?_ hx0' hP
    (fun sf code R' _ h => allowPanic_not_exited h)
    (fun sf _ h => by
      rw [← sepConj_assoc]; exact allowPanic_frame (allocFailedIn_of_trace_eq htr) h)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
  · dsimp only [pkClSpecAt]
    rw [hsp_eq]
  · dsimp only [pkClSpecAt]
    rw [hsp_eq, htr]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hcl_f, hx1, htr_f⟩ => ?_
    have h := hnext sf hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f hcl_f
    rw [sepConj_assoc] at h
    exact SepWPp.weaken_pre (Entails.pure_right ⟨hx1, htr_f⟩ (Entails.refl _)) h

private def privClSpecAt [LibsignalPlacement] (A : RustAlloc) (m : Memory) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (self, bs, ret) s' =>
    ⌜(s'.readReg64 .x0 = self ∧ s'.readReg64 .x8 = ret ∧ bs.length = 32) ∧ s'.mem = m⌝ ∗
      ((self ↦ₛ bs) ∗ memRegion ret 24 ∗ A.pool ∗ stackAt s'.sp extHookStack)
  post := fun (self, bs, ret) s0 sf =>
    ⌜LibsignalCodeLoaded lsmpl sf.mem ∧ sf.trace = s0.trace⌝ ∗
      (self ↦ₛ bs) ∗ vecU8 A ret bs ∗ A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem subroutine_ok_privClSpecAt [LibsignalPlacement] {prog : Program}
    {entry : BitVec 64} {A : RustAlloc} {m : Memory}
    (hpriv : subroutine_ok prog entry (withLsCl lsmpl (privSerializeSpec A)))
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok prog entry (privClSpecAt A m) := by
  refine subroutine_ok_mono hpriv
    (fun (self, bs, ret) R s' hpre => ?_)
    (fun (self, bs, ret) R s0 sf hpost => ?_)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h)
  · dsimp only [privClSpecAt] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx, hm⟩, hrest⟩
    have hcl' : LibsignalCodeLoaded lsmpl s'.mem := hm ▸ hcl
    dsimp only [withLsCl, privSerializeSpec, Spec.allowPanicWhen]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx, hrest⟩
  · dsimp only [withLsCl, privSerializeSpec, Spec.allowPanicWhen] at hpost
    dsimp only [privClSpecAt]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hcl_f, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htr, hrest⟩
    exact ⟨⟨hcl_f, htr⟩, hrest⟩

private theorem SepWPp_call_priv_gen_cl [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s0 s : State} {P F R : SepProp} {Q : State → SepProp → Prop}
    {entry ret_pc sp_call selfPtr retPtr : BitVec 64} {A : RustAlloc}
    (hpriv : subroutine_ok prog entry (withLsCl lsmpl (privSerializeSpec A)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (bs : List (BitVec 8))
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hsp_eq : s.sp = sp_call)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx : s.readReg64 Reg.x0 = selfPtr ∧ s.readReg64 Reg.x8 = retPtr ∧ bs.length = 32)
    (hP : P = ((selfPtr ↦ₛ bs) ∗ memRegion retPtr 24 ∗ A.pool ∗
      stackAt sp_call extHookStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog ret sf
        ((⌜sf.trace = s0.trace⌝ ∗ (selfPtr ↦ₛ bs) ∗
          vecU8 A retPtr bs ∗ A.pool ∗ stackAt sp_call extHookStack) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  have hpriv' := subroutine_ok_privClSpecAt hpriv hcl
  have hx' : (s.readReg64 Reg.x0 = selfPtr ∧ s.readReg64 Reg.x8 = retPtr ∧ bs.length = 32) ∧ s.mem = s.mem :=
    ⟨hx, rfl⟩
  refine SepWPp.call_frame (x := (selfPtr, bs, retPtr)) hpriv' hpc hrun
    (by unfold State.spAligned; rw [hsp_eq]; exact hsp_align) hlr ?_ hx' hP
    (fun sf code R' _ h => allowPanic_not_exited h)
    (fun sf _ h => by
      rw [← sepConj_assoc]; exact allowPanic_frame (allocFailedIn_of_trace_eq htr) h)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
  · dsimp only [privClSpecAt]
    rw [hsp_eq]
  · dsimp only [privClSpecAt]
    rw [hsp_eq, htr]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hcl_f, htr_f⟩ => ?_
    have h := hnext sf hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f hcl_f
    rw [sepConj_assoc] at h
    exact SepWPp.weaken_pre (Entails.pure_right htr_f (Entails.refl _)) h

theorem pubKeySerdeSerialize_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim0 : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_87).rebase (blkPl_87).base H) (blkPl_87).base
      (withLsCodeLoaded lsmpl (pubKeySerdeSerializeOkSpec A)) := by
  unfold pubKeySerdeSerializeOkSpec
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  have hpubser := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_87).rebase (blkPl_87).base H) (entry := lsmpl.base 205)
    (public_key_serialize_placed_ok hshim0 halloc hpanic)
  have hshim_ok : subroutine_ok ((blkPC_87).rebase (blkPl_87).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec :=
    ls_hook_ok_of_mem hshim
  have halloc_ok : subroutine_ok ((blkPC_87).rebase (blkPl_87).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) :=
    ls_hook_ok_of_mem halloc
  have hmemcpy_ok : subroutine_ok ((blkPC_87).rebase (blkPl_87).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec :=
    ls_hook_ok_of_mem hmemcpy
  have hpanic_ok : ((blkPC_87).rebase (blkPl_87).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked :=
    (ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic
  have hdealloc_ok := dealloc_tail48_of_dealloc
    (ls_hook_ok_of_mem (prog := (blkPC_87).rebase (blkPl_87).base H) hdealloc)
  simp only [rustDeallocTail48Spec, cells, sepConj_emp, sepExists_sepConj_right,
    sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit] at hdealloc_ok
  wpp_init g s0
  simp only [sepConj_assoc]
  obtain ⟨self, pk, outPtr⟩ := g
  dsimp only [withLsCodeLoaded] at *
  subst h_2 h_1
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  have hser_len : pk.serialize.length = 33 := by
    simp [PublicKey.serialize, List.Vector.toList_length]
  rw [stackAt_publicKeySerialize_sub48_assoc s0.sp]
  apply sepWPp_of_sepWP_lscl h (mid := lsmpl.base 205)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcl_call
  refine SepWPp_call_pk_gen_cl hpubser hcl_call pk
    (ret_pc := (blkPl_87).base + 24#64) (sp_call := s0.sp - 48#64)
    (selfPtr := s0.readReg64 (Reg.gpr 0#5))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (spAligned_sub_48 hsp_align rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus)
    fun sf_pk hpc_pk hrun_pk hsp_pk hcs_pk _hcl_pk => ?_
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_pk
  rcases hcs_pk with
    ⟨hcs_k19, hcs_k20, hcs_k21, hcs_k22, hcs_k23, hcs_k24, hcs_k25, hcs_k26, hcs_k27, hcs_k28,
      hcs_k29⟩
  simp only [arm64_norm, *]
    at hcs_k19 hcs_k20 hcs_k21 hcs_k22 hcs_k23 hcs_k24 hcs_k25 hcs_k26 hcs_k27 hcs_k28 hcs_k29
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1, htrace0⟩ => ?_
  refine SepWPp.fold (boxU8Buf_pk_expose A (sf_pk.readReg64 .x0) pk) (by sep_focus) ?_
  rw [← stackAt_publicKeySerialize_sub48 s0.sp]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hbox_ne => ?_
  apply SepWPp.of_sepWP (mid := (blkPl_87).base + 76#64)
  wp_steps
  wp_call hshim_ok ()
  wp_steps
  wp_call halloc_ok (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true]
    refine sepWPp_pure_mid fun htrace2 => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hpanic_ok (by simp only [arm64_norm, *])
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod, htrace2⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    rw [← hser_len]
    wp_call hmemcpy_ok (sf_1.readReg64 (Reg.gpr 0#5), sf_pk.readReg64 (Reg.gpr 0#5), pk.serialize)
    simp only [hser_len]
    wp_steps
    rw [← hser_len]
    wp_call hdealloc_ok (sf_pk.readReg64 (Reg.gpr 0#5), pk.serialize, 1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    simp only [hser_len]
    wp_done

theorem preKeyRecordNew_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim0 : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_66).rebase (blkPl_66).base H) (blkPl_66).base
      (withLsCodeLoaded lsmpl (preKeyRecordNewOkSpec A)) := by
  unfold preKeyRecordNewOkSpec
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  have hpubser := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_66).rebase (blkPl_66).base H) (entry := lsmpl.base 205)
    (public_key_serialize_placed_ok hshim0 halloc hpanic)
  have hprivser := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_66).rebase (blkPl_66).base H) (entry := lsmpl.base 208)
    (privSerialize_placed_ok hshim0 halloc hpanic)
  have hshim_ok : subroutine_ok ((blkPC_66).rebase (blkPl_66).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimSpec :=
    ls_hook_ok_of_mem hshim
  have halloc_ok : subroutine_ok ((blkPC_66).rebase (blkPl_66).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) :=
    ls_hook_ok_of_mem halloc
  have hdealloc_ok : subroutine_ok ((blkPC_66).rebase (blkPl_66).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A) :=
    ls_hook_ok_of_mem hdealloc
  have hmemcpy_ok : subroutine_ok ((blkPC_66).rebase (blkPl_66).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec :=
    ls_hook_ok_of_mem hmemcpy
  have hpanic_ok : ((blkPC_66).rebase (blkPl_66).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked :=
    (ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic
  wpp_init g s0
  simp only [sepConj_assoc]
  obtain ⟨id, kpPtr, pk, priv, outPtr⟩ := g
  dsimp only [withLsCodeLoaded] at *
  subst h_1 h_2 h_3
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay33 : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  have hlay32 : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  have hser_len : pk.serialize.length = 33 := by
    simp [PublicKey.serialize, List.Vector.toList_length]
  have hpriv_len : priv.toList.length = 32 := priv.toList_length
  refine SepWPp.fold (stackAt_112_ext_to s0.sp publicKeySerializeStack) (by sep_focus) ?_
  apply sepWPp_of_sepWP_lscl h (mid := lsmpl.base 205)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcl_call1
  refine SepWPp_call_pk_gen_cl hpubser hcl_call1 pk
    (ret_pc := (blkPl_66).base + 48#64) (sp_call := s0.sp - 112#64)
    (selfPtr := s0.readReg64 (Reg.gpr 1#5))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (spAligned_sub_112 hsp_align rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus)
    fun sf_pk hpc_pk hrun_pk hsp_pk hcs_pk hcl_pk => ?_
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_pk
  rcases hcs_pk with
    ⟨hcs_k19, hcs_k20, hcs_k21, hcs_k22, hcs_k23, hcs_k24, hcs_k25, hcs_k26, hcs_k27, hcs_k28,
      hcs_k29⟩
  simp only [arm64_norm, *]
    at hcs_k19 hcs_k20 hcs_k21 hcs_k22 hcs_k23 hcs_k24 hcs_k25 hcs_k26 hcs_k27 hcs_k28 hcs_k29
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1, htrace0⟩ => ?_
  refine SepWPp.fold (boxU8Buf_pk_expose A (sf_pk.readReg64 .x0) pk) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hbox_ne => ?_
  refine SepWPp_fold_stack_112_to_ext s0.sp publicKeySerializeStack
    (by decide) (by sep_focus) rfl ?_
  refine SepWPp.fold (stackAt_112_ext_to s0.sp allocHookStack) (by sep_focus) ?_
  apply sepWPp_of_sepWP_lscl hcl_pk (mid := (blkPl_66).base + 100#64)
  wp_steps
  wp_call hshim_ok ()
  wp_steps
  wp_call halloc_ok (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl_alloc1
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace1 => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hpanic_ok (by simp only [arm64_norm, *])
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    simp only [hoom1, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    apply sepWPp_of_sepWP_lscl hcl_alloc1 (mid := lsmpl.base 208)
    wp_steps
    rw [← hser_len]
    wp_call hmemcpy_ok (sf_1.readReg64 (Reg.gpr 0#5), sf_pk.readReg64 (Reg.gpr 0#5), pk.serialize)
    simp only [hser_len]
    refine SepWP.fold (pk_buf_to_memRegion (sf_pk.readReg64 .x0) pk) (by sep_focus) ?_
    wp_steps
    wp_call hdealloc_ok (sf_pk.readReg64 (Reg.gpr 0#5), 33, 1)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl_call2
    refine SepWPp_fold_stack_112_to_ext s0.sp allocHookStack
      (by decide) (by sep_focus) (by simp only [arm64_norm, *]) ?_
    refine SepWPp.fold (stack_24_to_memRegion_104 s0.sp v_stk_1 v_stk_2 v_stk_3) (by sep_focus) ?_
    refine SepWPp_call_priv_gen_cl hprivser hcl_call2 priv.toList
      (ret_pc := (blkPl_66).base + 148#64) (sp_call := s0.sp - 112#64)
      (selfPtr := s0.readReg64 (Reg.gpr 1#5) + 32#64) (retPtr := s0.sp - 104#64)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (spAligned_sub_112 hsp_align rfl)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by sep_focus)
      fun sf_priv hpc_priv hrun_priv hsp_priv hcs_priv _hcl_priv => ?_
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_priv
    rcases hcs_priv with
      ⟨hcs_p19, hcs_p20, hcs_p21, hcs_p22, hcs_p23, hcs_p24, hcs_p25, hcs_p26, hcs_p27, hcs_p28,
        hcs_p29⟩
    simp only [arm64_norm, *]
      at hcs_p19 hcs_p20 hcs_p21 hcs_p22 hcs_p23 hcs_p24 hcs_p25 hcs_p26 hcs_p27 hcs_p28 hcs_p29
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hpriv_tr => ?_
    refine SepWPp.fold (vecU8_priv_expose_104 A s0.sp priv) (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun privTempCap => SepWPp.exists_elim fun privTempPtr => ?_
    refine SepWPp.pure_elim fun ⟨hpt_le, hpt_lt, hpt_c0, hpt_ptr⟩ => ?_
    refine SepWPp.fold (stackAt_112_ext_to s0.sp allocHookStack) (by sep_focus) ?_
    apply SepWPp.of_sepWP (mid := (blkPl_66).base + 224#64)
    wp_steps
    wp_call hshim_ok ()
    wp_steps
    wp_call halloc_ok (32, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom2 : sf_5.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      simp only [hoom2, ite_true]
      refine sepWPp_pure_mid fun htrace2 => ?_
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      apply SepWPp_panic_oom (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hpanic_ok (by simp only [arm64_norm, *])
    · have hoom2_64 : sf_5.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      simp only [hoom2, ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod2, htrace2⟩ => ?_
      have hpt_layout : LayoutOk privTempCap.toNat 1 :=
        layoutOk_of_pos_lt (Nat.lt_of_lt_of_le (by decide : 0 < 32) hpt_le) hpt_lt
      apply SepWPp.of_sepWP_ret
      wp_steps
      rw [show memRegion (sf_5.readReg64 (Reg.gpr 0#5)) 32 =
        memRegion (sf_5.readReg64 (Reg.gpr 0#5)) priv.toList.length by rw [hpriv_len]]
      wp_call hmemcpy_ok (sf_5.readReg64 (Reg.gpr 0#5), privTempPtr, priv.toList)
      refine SepWP.fold
        (priv_buf_to_memRegion privTempPtr privTempCap priv hpt_le hpt_lt) (by sep_focus) ?_
      wp_steps
      wp_call hdealloc_ok (privTempPtr, privTempCap.toNat, 1)
      wp_steps
      refine SepWP_fold_stack_112_to_ext s0.sp allocHookStack
        (by decide) (by sep_focus) (by simp only [arm64_norm, *]) ?_
      wp_done

end CryptoVerification.E2E.Pqxdh.ResponderStore
