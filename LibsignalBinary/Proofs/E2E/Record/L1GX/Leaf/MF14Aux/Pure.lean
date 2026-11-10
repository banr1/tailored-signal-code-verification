/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs
import LibsignalBinary.Proofs.E2E.Epochs
import LibsignalBinary.Proofs.ProtoCodecRoundTrip

/-!
# Pure codec and heap-layout lemmas for `merge_field` tag 14

Payload byte decompositions for `GenFieldX.kyber i ct` (`pending_kyber_pre_key`, 1569-byte
ciphertext) and separation-logic isolating splits for the 32-byte `Option<PendingKyberPreKey>`
slot at `ss + 0x128`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX

/-! ## Payload byte layout (`i = 0`) -/

theorem genFieldX_tag_eq_14_iff (fl : GenFieldX) :
    fl.tag = 14 ↔ ∃ i ct, fl = .kyber i ct := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> simp [GenFieldX.tag]
  cases f <;> simp [GenField.tag]

theorem encodeVarint_1569 : encodeVarint (BitVec.ofNat 64 1569) = [161#8, 12#8] := by
  decide

theorem encodeVarint_1572 : encodeVarint (BitVec.ofNat 64 1572) = [164#8, 12#8] := by
  decide

theorem encodeKey_1_varint : encodeKey 1 .varint = [8#8] := by
  decide

theorem encodeKey_2_ld : encodeKey 2 .lengthDelimited = [18#8] := by
  decide

/-- Inner tag-2 payload suffix consisting of the length-prefixed ciphertext followed by `tail`. -/
def innerBytes (ct tail : List (BitVec 8)) : List (BitVec 8) :=
  encodeVarint (BitVec.ofNat 64 ct.length) ++ (ct ++ tail)

theorem innerBytes_length {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    (innerBytes ct tail).length = 1571 + tail.length := by
  unfold innerBytes
  rw [List.length_append, List.length_append, hct, encodeVarint_1569]
  simp only [List.length_cons, List.length_nil]
  omega

theorem kyberBody_eq {ct : List (BitVec 8)} :
    kyberBody 0#32 ct = 18#8 :: (encodeVarint (BitVec.ofNat 64 ct.length) ++ ct) := by
  unfold kyberBody uint32Field lenField
  rw [encodeKey_2_ld]
  split
  · rfl
  · exact absurd rfl ‹_›

theorem kyberBody_length {ct : List (BitVec 8)} (hct : ct.length = 1569) :
    (kyberBody 0#32 ct).length = 1572 := by
  rw [kyberBody_eq, List.length_cons, List.length_append, hct, encodeVarint_1569]
  rfl

theorem kyber_payload_eq {ct : List (BitVec 8)} (hct : ct.length = 1569) :
    (GenFieldX.kyber 0#32 ct).payload =
      164#8 :: 12#8 :: kyberBody 0#32 ct := by
  dsimp only [GenFieldX.payload]
  rw [kyberBody_length hct, encodeVarint_1572]
  rfl

theorem kyber_payload_tail_eq {ct : List (BitVec 8)} (hct : ct.length = 1569)
    (tail : List (BitVec 8)) :
    (GenFieldX.kyber 0#32 ct).payload ++ tail =
      164#8 :: 12#8 :: 18#8 :: innerBytes ct tail := by
  rw [kyber_payload_eq hct, kyberBody_eq]
  unfold innerBytes
  simp only [List.cons_append, List.append_assoc]

theorem kyber_payload_tail_length {ct : List (BitVec 8)} (hct : ct.length = 1569)
    (tail : List (BitVec 8)) :
    ((GenFieldX.kyber 0#32 ct).payload ++ tail).length = 1574 + tail.length := by
  rw [kyber_payload_tail_eq hct, List.length_cons, List.length_cons, List.length_cons,
    innerBytes_length hct]
  omega

theorem decodeVarint_kyber {ct : List (BitVec 8)} (tail : List (BitVec 8)) :
    decodeVarint (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail) =
      some (BitVec.ofNat 64 1572, 18#8 :: innerBytes ct tail) := by
  have h := decodeVarint_encodeVarint (BitVec.ofNat 64 1572) (18#8 :: innerBytes ct tail)
  rw [encodeVarint_1572] at h
  exact h

theorem mergeBytes_inner {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    mergeBytes .lengthDelimited (innerBytes ct tail) = some (ct, tail) := by
  unfold innerBytes
  exact mergeBytes_encode ct tail (by omega)

/-! ## Payload byte layout (`i ≠ 0`) -/

theorem encodeVarintAux_length_le_mf14 (n : Nat) (v : BitVec 64) :
    (encodeVarintAux n v).length ≤ n := by
  induction n generalizing v with
  | zero => simp [encodeVarintAux]
  | succ n ih =>
    unfold encodeVarintAux
    split
    · simp
    · simp only [List.length_cons]
      have := ih (v >>> 7)
      omega

theorem encodeVarint_length_bounds_mf14 (v : BitVec 64) :
    1 ≤ (encodeVarint v).length ∧ (encodeVarint v).length ≤ 10 :=
  ⟨List.length_pos_iff.mpr (encodeVarint_ne_nil v), encodeVarintAux_length_le_mf14 10 v⟩

theorem encodeVarint_1573_add_mf14 {m : Nat} (hm : m ≤ 10) :
    encodeVarint (BitVec.ofNat 64 (1573 + m)) = [BitVec.ofNat 8 (165 + m), 12#8] := by
  rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · omega

/-- Leading byte of the 2-byte outer length varint when `i ≠ 0#32`. -/
def kyberB0 (i : BitVec 32) : BitVec 8 :=
  BitVec.ofNat 8 (165 + (encodeVarint (i.setWidth 64)).length)

theorem kyberB0_signExtend_getLsbD_63 (i : BitVec 32) :
    (BitVec.signExtend 64 (kyberB0 i)).getLsbD 63 = true := by
  have hm := (encodeVarint_length_bounds_mf14 (i.setWidth 64)).2
  unfold kyberB0
  generalize (encodeVarint (i.setWidth 64)).length = m at hm ⊢
  rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · omega

theorem kyberB0_signExtend_getLsbD_63_beq (i : BitVec 32) :
    ((BitVec.signExtend 64 (kyberB0 i)).getLsbD 63 == true) = true := by
  rw [kyberB0_signExtend_getLsbD_63]
  rfl

/-- Bytes following the inner tag-1 key `0x08` when `i ≠ 0#32`: varint-encoded `i` and tag-2
ciphertext field. -/
def kyberIdBytes (i : BitVec 32) (ct tail : List (BitVec 8)) : List (BitVec 8) :=
  encodeVarint (i.setWidth 64) ++ (18#8 :: innerBytes ct tail)

theorem kyberIdBytes_length (i : BitVec 32) {ct : List (BitVec 8)} (hct : ct.length = 1569)
    (tail : List (BitVec 8)) :
    (kyberIdBytes i ct tail).length =
      1572 + (encodeVarint (i.setWidth 64)).length + tail.length := by
  unfold kyberIdBytes
  rw [List.length_append, List.length_cons, innerBytes_length hct]
  omega

theorem kyberBody_ne_eq {i : BitVec 32} (hi : i ≠ 0#32) {ct : List (BitVec 8)} :
    kyberBody i ct =
      8#8 :: (encodeVarint (i.setWidth 64) ++
        (18#8 :: (encodeVarint (BitVec.ofNat 64 ct.length) ++ ct))) := by
  unfold kyberBody uint32Field lenField
  rw [encodeKey_1_varint, encodeKey_2_ld]
  split
  · exact absurd ‹_› hi
  · simp only [List.cons_append, List.nil_append]

theorem kyberBody_ne_length {i : BitVec 32} (hi : i ≠ 0#32) {ct : List (BitVec 8)}
    (hct : ct.length = 1569) :
    (kyberBody i ct).length = 1573 + (encodeVarint (i.setWidth 64)).length := by
  rw [kyberBody_ne_eq hi, List.length_cons, List.length_append, List.length_cons,
    List.length_append, hct, encodeVarint_1569]
  simp only [List.length_cons, List.length_nil]
  omega

theorem kyber_ne_payload_eq {i : BitVec 32} (hi : i ≠ 0#32) {ct : List (BitVec 8)}
    (hct : ct.length = 1569) :
    (GenFieldX.kyber i ct).payload =
      kyberB0 i :: 12#8 :: kyberBody i ct := by
  dsimp only [GenFieldX.payload]
  rw [kyberBody_ne_length hi hct,
    encodeVarint_1573_add_mf14 (encodeVarint_length_bounds_mf14 (i.setWidth 64)).2]
  rfl

theorem kyber_ne_payload_tail_eq {i : BitVec 32} (hi : i ≠ 0#32) {ct : List (BitVec 8)}
    (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    (GenFieldX.kyber i ct).payload ++ tail =
      kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail := by
  rw [kyber_ne_payload_eq hi hct, kyberBody_ne_eq hi]
  unfold kyberIdBytes innerBytes
  simp only [List.cons_append, List.append_assoc]

theorem kyber_ne_payload_tail_length {i : BitVec 32} (hi : i ≠ 0#32) {ct : List (BitVec 8)}
    (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    ((GenFieldX.kyber i ct).payload ++ tail).length =
      1575 + (encodeVarint (i.setWidth 64)).length + tail.length := by
  rw [kyber_ne_payload_tail_eq hi hct, List.length_cons, List.length_cons, List.length_cons,
    kyberIdBytes_length i hct]
  omega

theorem decodeVarint_kyber_ne (i : BitVec 32) {ct : List (BitVec 8)} (tail : List (BitVec 8)) :
    decodeVarint (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail) =
      some (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length),
        8#8 :: kyberIdBytes i ct tail) := by
  have h := decodeVarint_encodeVarint
    (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length))
    (8#8 :: kyberIdBytes i ct tail)
  rw [encodeVarint_1573_add_mf14 (encodeVarint_length_bounds_mf14 (i.setWidth 64)).2] at h
  exact h

theorem mergeUint32_kyberIdBytes (i : BitVec 32) {ct : List (BitVec 8)} (tail : List (BitVec 8)) :
    mergeUint32 .varint (kyberIdBytes i ct tail) = some (i, 18#8 :: innerBytes ct tail) := by
  unfold kyberIdBytes
  exact mergeUint32_encode i (18#8 :: innerBytes ct tail)

/-! ## `SessionStructure` layout split at `+0x128` -/

/-- Portion of `prostSSGXAt` outside the 32-byte `pending_kyber_pre_key` slot at `ss + 0x128`. -/
def restX14 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗ vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    ((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
    ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg)

theorem restX14_apply_kyber (A : RustAlloc) (ss : BitVec 64) (v : SSGX) (i : BitVec 32)
    (ct : List (BitVec 8)) : restX14 A ss (v.apply (.kyber i ct)) = restX14 A ss v := rfl

theorem memRegion_24_split_kyber (ss : BitVec 64) :
    memRegion (ss + 0x130#64) 24 =
      (∃∗ w130 : BitVec 64, (ss + 0x130#64) ↦₆₄ w130) ∗
      (∃∗ w138 : BitVec 64, (ss + 0x138#64) ↦₆₄ w138) ∗
      (∃∗ w140 : BitVec 32, (ss + 0x140#64) ↦₃₂ w140) ∗
      memRegion (ss + 0x144#64) 4 := by
  rw [memRegion_split' (b := ss + 0x130#64) (b' := ss + 0x138#64) (n := 8) (k := 16) rfl (by bv_lin) (by decide),
      memRegion_split' (b := ss + 0x138#64) (b' := ss + 0x140#64) (n := 8) (k := 8) rfl (by bv_lin) (by decide),
      memRegion_split' (b := ss + 0x140#64) (b' := ss + 0x144#64) (n := 4) (k := 4) rfl (by bv_lin) (by decide),
      ProofLib.memRegion_eight (ss + 0x130#64), ProofLib.memRegion_eight (ss + 0x138#64),
      ProofLib.memRegion_four (ss + 0x140#64)]

/-- Unfolds `prostSSGXAt` when `kyber = none` into the `None` niche at `ss + 0x128`, its trailing
24 bytes, and `restX14`. -/
theorem prostSSGXAt_kyber_none_unfold (A : RustAlloc) (ss : BitVec 64) (v : SSGX)
    (hk : v.ext.kyber = none) :
    prostSSGXAt A ss v =
      ((ss + 0x128#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      (∃∗ w130 : BitVec 64, (ss + 0x130#64) ↦₆₄ w130) ∗
      (∃∗ w138 : BitVec 64, (ss + 0x138#64) ↦₆₄ w138) ∗
      (∃∗ w140 : BitVec 32, (ss + 0x140#64) ↦₃₂ w140) ∗
      memRegion (ss + 0x144#64) 4 ∗
      restX14 A ss v := by
  unfold prostSSGXAt restX14
  rw [hk]
  dsimp only [kyberAt]
  rw [memRegion_24_split_kyber ss]
  dsimp only [noneCap]
  ac_rfl

theorem emptyVec_kyber_eq_vecU8At (A : RustAlloc) (ss : BitVec 64) :
    ((ss + 0x128#64) ↦₆₄ 0#64) ∗ ((ss + 0x130#64) ↦₆₄ 1#64) ∗ ((ss + 0x138#64) ↦₆₄ 0#64) =
      vecU8At A (ss + 0x128#64) 0#64 1#64 [] := by
  have h130 : ss + 0x128#64 + 8#64 = ss + 0x130#64 := by bv_lin
  have h138 : ss + 0x128#64 + 16#64 = ss + 0x138#64 := by bv_lin
  have hp : ([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 :=
    ⟨by decide, by decide, by decide⟩
  dsimp only [vecU8At, vecHeader]
  have hite : (if (0#64 : BitVec 64) = 0 then emp else
      A.live (1#64) (0#64).toNat 1 ∗ 1#64 ↦ₛ [] ∗
        memRegion (1#64 + BitVec.ofNat 64 ([] : List (BitVec 8)).length)
          ((0#64 : BitVec 64).toNat - ([] : List (BitVec 8)).length)) = emp := rfl
  rw [h130, h138, eq_true hp, hite, pure_true, emp_sepConj, sepConj_emp, List.length_nil]

/-- Folds a decoded `Some(PendingKyberPreKey)` at `ss + 0x128` with `restX14` back into `prostSSGXAt`. -/
theorem prostSSGXAt_kyber_some_fold (A : RustAlloc) (ss cap' ptr' : BitVec 64) (v : SSGX)
    (i : BitVec 32) (ct : List (BitVec 8)) :
    vecU8At A (ss + 0x128#64) cap' ptr' ct ∗
      ((ss + 0x140#64) ↦₃₂ i) ∗ memRegion (ss + 0x144#64) 4 ∗ restX14 A ss v ⊢
      prostSSGXAt A ss (v.apply (.kyber i ct)) := by
  have hv : vecU8At A (ss + 0x128#64) cap' ptr' ct ⊢ vecU8 A (ss + 0x128#64) ct := by
    unfold vecU8
    exact Entails.trans
      (Entails.sepExists_intro (P := fun ptr => vecU8At A (ss + 0x128#64) cap' ptr ct) ptr')
      (Entails.sepExists_intro (P := fun cap => ∃∗ ptr, vecU8At A (ss + 0x128#64) cap ptr ct) cap')
  refine Entails.trans (sepConj_mono_left hv) ?_
  unfold prostSSGXAt restX14 SSGX.apply
  dsimp only [kyberAt]
  apply Entails.of_eq
  ac_rfl

end CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux
