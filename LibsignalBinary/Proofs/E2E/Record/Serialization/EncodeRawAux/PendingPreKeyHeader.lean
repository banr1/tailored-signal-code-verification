/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PrologueVersionLocalIdentity
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.RemoteIdentityRootKeyCounter
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChains
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `SessionStructure::encode_raw` tag 9 (`pending_pre_key` header and length, `+0x218..+0x368`)
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization.EncodeRawAux

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record

@[local arm64_norm]
theorem truncate32_signExtend64_er (v : BitVec 32) :
    BitVec.truncate 32 (BitVec.signExtend 64 v) = v := by
  ext i hi
  simp [BitVec.getLsbD_signExtend, hi]
  omega

theorem publicKey_deserialize_ne_nil {bs : List (BitVec 8)} {pk : PublicKey}
    (h : PublicKey.deserialize bs = .ok pk) : bs ≠ [] := by
  intro hnil
  subst hnil
  simp [PublicKey.deserialize] at h

theorem optUint32Field1_none_eq : optUint32Field 1 none = [] := rfl

theorem optUint32Field1_some_eq (pkId : BitVec 32) :
    [0x08#8] ++ encodeVarint (BitVec.zeroExtend 64 pkId) = optUint32Field 1 (some pkId) := by
  have hk : encodeKey 1 .varint = [0x08#8] := by decide +kernel
  simp [optUint32Field, hk]

theorem optUint32Field1_some_length_bv (pkId : BitVec 32) :
    BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 pkId)).length + 1#64 =
      BitVec.ofNat 64 (optUint32Field 1 (some pkId)).length := by
  rw [← optUint32Field1_some_eq pkId]
  simp only [List.length_append, List.length_singleton, ← BitVec.ofNat_add, Nat.add_comm]

theorem bytesField2_nonempty_eq {bs : List (BitVec 8)} (hne : bs ≠ []) :
    [0x12#8] ++ encodeVarint (BitVec.ofNat 64 bs.length) ++ bs = bytesField 2 bs := by
  have hk : encodeKey 2 .lengthDelimited = [0x12#8] := by decide +kernel
  simp [bytesField, lenField, hne, hk]

theorem bytesField2_nonempty_length_bv {bs : List (BitVec 8)} (hne : bs ≠ []) :
    BitVec.ofNat 64 bs.length +
      BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 bs.length)).length + 1#64 =
      BitVec.ofNat 64 (bytesField 2 bs).length := by
  rw [← bytesField2_nonempty_eq hne]
  simp only [List.length_append, List.length_singleton, ← BitVec.ofNat_add]
  congr 1
  omega

theorem int32Field3_zero_eq : int32Field 3 0#32 = [] := rfl

theorem int32Field3_nonzero_eq {v : BitVec 32} (h : v ≠ 0#32) :
    [0x18#8] ++ encodeVarint (BitVec.signExtend 64 v) = int32Field 3 v := by
  have hk : encodeKey 3 .varint = [0x18#8] := by decide +kernel
  simp [int32Field, h, hk]

theorem int32Field3_nonzero_length_bv {v : BitVec 32} (h : v ≠ 0#32) :
    BitVec.ofNat 64 (encodeVarint (BitVec.signExtend 64 v)).length + 1#64 =
      BitVec.ofNat 64 (int32Field 3 v).length := by
  rw [← int32Field3_nonzero_eq h]
  simp only [List.length_append, List.length_singleton, ← BitVec.ofNat_add, Nat.add_comm]

theorem uint64Field4_zero_eq : uint64Field 4 0#64 = [] := rfl

theorem uint64Field4_nonzero_eq {v : BitVec 64} (h : v ≠ 0#64) :
    [0x20#8] ++ encodeVarint v = uint64Field 4 v := by
  have hk : encodeKey 4 .varint = [0x20#8] := by decide +kernel
  simp [uint64Field, h, hk]

theorem uint64Field4_nonzero_length_bv {v : BitVec 64} (h : v ≠ 0#64) :
    BitVec.ofNat 64 (encodeVarint v).length + 1#64 =
      BitVec.ofNat 64 (uint64Field 4 v).length := by
  rw [← uint64Field4_nonzero_eq h]
  simp only [List.length_append, List.length_singleton, ← BitVec.ofNat_add, Nat.add_comm]

theorem encPendingMem_length_bv (g : TailVecGhost) (p : PendingPreKey) :
    (BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length +
      BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length) +
    (BitVec.ofNat 64 (int32Field 3 p.signedPreKeyId).length +
      BitVec.ofNat 64 (uint64Field 4 p.timestamp).length) =
    BitVec.ofNat 64 (encPendingMem g p).length := by
  unfold encPendingMem
  simp only [List.length_append, ← BitVec.ofNat_add]
  congr 1
  omega

theorem encPendingMem_length_bv_ts_zero (g : TailVecGhost) (p : PendingPreKey)
    (hts : p.timestamp = 0#64) :
    (BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length +
      BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length) +
    BitVec.ofNat 64 (int32Field 3 p.signedPreKeyId).length =
    BitVec.ofNat 64 (encPendingMem g p).length := by
  rw [← encPendingMem_length_bv g p, hts, uint64Field4_zero_eq]
  simp

theorem lenField9_eq (g : TailVecGhost) (p : PendingPreKey) :
    [0x4a#8] ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length) ++
      optUint32Field 1 p.preKeyId ++ bytesField 2 g.vec.bytes ++
      int32Field 3 p.signedPreKeyId ++ uint64Field 4 p.timestamp =
    encPendingFieldMem (some g) (some p) := by
  unfold encPendingFieldMem lenField encPendingMem
  have hk : encodeKey 9 .lengthDelimited = [0x4a#8] := by decide +kernel
  rw [hk]
  simp only [List.append_assoc]

/-! ## `optTailVecAt 48` decomposition for `PendingPreKey` -/

def optU32ValAt (a : BitVec 64) (bs : List (BitVec 8)) : Option (BitVec 32) → SepProp
  | none => a ↦ₛ (bs.drop 4).take 4
  | some pkId => a ↦₃₂ pkId

theorem optU32ValAt_some (a : BitVec 64) (bs : List (BitVec 8)) (pkId : BitVec 32) :
    optU32ValAt a bs (some pkId) = (a ↦₃₂ pkId) := rfl

def pendingTailRest (ss : BitVec 64) (g : TailVecGhost) : SepProp :=
  (ss + 292#64) ↦ₛ g.tail.drop 20

theorem pointsToBytes_pending_pkId_eq (ss : BitVec 64) {bs : List (BitVec 8)}
    {opt : Option (BitVec 32)} (hopt : OptU32Rel bs opt) :
    ((ss + 276#64) ↦ₛ (bs.drop 4).take 4) = optU32ValAt (ss + 276#64) bs opt := by
  cases opt with
  | none => rfl
  | some pkId =>
    dsimp [optU32ValAt]
    rw [hopt.2, pointsToBytes_leBytes_4]

def pendingOpenAt (A : RustAlloc) (ss : BitVec 64) (g : TailVecGhost) (p : PendingPreKey) : SepProp :=
  ((ss + 248#64) ↦₆₄ g.vec.cap) ∗
  ((ss + 256#64) ↦₆₄ g.vec.ptr) ∗
  ((ss + 264#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
  ((ss + 272#64) ↦₃₂ optU32Tag p.preKeyId) ∗
  optU32ValAt (ss + 276#64) g.tail p.preKeyId ∗
  ((ss + 280#64) ↦₆₄ p.timestamp) ∗
  ((ss + 288#64) ↦₃₂ p.signedPreKeyId) ∗
  (g.vec.ptr ↦ₛ g.vec.bytes) ∗
  vecSrcRest A g.vec.cap g.vec.ptr g.vec.bytes ∗
  pendingTailRest ss g

theorem optTailVecAt_pending_some_eq_open (A : RustAlloc) (ss : BitVec 64)
    (g : TailVecGhost) (p : PendingPreKey)
    (hlen24 : g.tail.length = 24) (hle : g.vec.bytes.length ≤ g.vec.cap.toNat)
    (hrel : PendingRel (some g) (some p)) :
    optTailVecAt A 48 (ss + 248#64) (some g) = pendingOpenAt A ss g p := by
  obtain ⟨hdes, hopt, hts, hspk, _⟩ := hrel
  have hne := publicKey_deserialize_ne_nil hdes
  have hpure : (g.tail.length = 48 - 24) = True := eq_true hlen24
  have hadd : (ss + 248#64) + 24#64 = ss + 272#64 := by bv_lin
  dsimp only [optTailVecAt, vecGhostAt]
  rw [hpure, pure_true, emp_sepConj, hadd,
      vecU8At_open_src_off' A ss 248#64 256#64 264#64 g.vec.cap g.vec.ptr g.vec.bytes hne hle,
      pointsToBytes_pending_tail_eq ss hlen24 hopt hts hspk,
      pointsToBytes_pending_pkId_eq ss hopt]
  unfold pendingOpenAt pendingTailRest
  ac_rfl

theorem sepWPp_extract_pending_some {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {ss : BitVec 64} {g : TailVecGhost} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfocus : P = optTailVecAt A 48 (ss + 248#64) (some g) ∗ F := by sep_focus)
    (h : g.tail.length = 24 → g.vec.bytes.length ≤ g.vec.cap.toNat →
      g.vec.cap.toNat < 2 ^ 63 → g.vec.ptr ≠ 0#64 →
      SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hfocus1 : P = ⌜g.tail.length = 24⌝ ∗
      (vecU8At A (ss + 248#64) g.vec.cap g.vec.ptr g.vec.bytes ∗
        ((ss + 248#64 + 24#64) ↦ₛ g.tail) ∗ F) := by
    rw [hfocus]; dsimp only [optTailVecAt, vecGhostAt]; ac_rfl
  intro R hm hL
  have hm1 := hm
  rw [hfocus1, sepConj_assoc, satisfies_pure_sepConj] at hm1
  have hfocus2 : P = vecU8At A (ss + 248#64) g.vec.cap g.vec.ptr g.vec.bytes ∗
      (⌜g.tail.length = 24⌝ ∗ ((ss + 248#64 + 24#64) ↦ₛ g.tail) ∗ F) := by
    rw [hfocus]; dsimp only [optTailVecAt, vecGhostAt]; ac_rfl
  exact sepWPp_extract_vecU8At_bounds (hfocus := hfocus2)
    (fun hle hcap hptr => h hm1.1 hle hcap hptr) R hm hL

private theorem or_one_ne_zero_er (v : BitVec 64) : v ||| 1#64 ≠ 0#64 := by
  intro h
  have h0 := congrArg (fun x : BitVec 64 => x.getLsbD 0) h
  simp at h0

private theorem or_one_clz_toNat_lt_er (v : BitVec 64) : (v ||| 1#64).clz.toNat < 64 := by
  have hle : (v ||| 1#64).clz ≤ 64#64 := BitVec.clz_le
  have hne : (v ||| 1#64).clz ≠ 64#64 :=
    mt BitVec.clz_eq_iff_eq_zero.mp (or_one_ne_zero_er v)
  have hle_nat : (v ||| 1#64).clz.toNat ≤ 64 := hle
  have hne_nat : (v ||| 1#64).clz.toNat ≠ 64 := by
    intro h
    apply hne
    apply BitVec.eq_of_toNat_eq
    exact h
  omega

private theorem shiftRight_lt_128_iff_er (v : BitVec 64) (s : Nat) :
    ((v >>> s).toNat < 128) ↔ 64 - (v ||| 1#64).clz.toNat ≤ s + 7 := by
  have hxne : v ||| 1#64 ≠ 0#64 := or_one_ne_zero_er v
  have hlo : 2 ^ (63 - (v ||| 1#64).clz.toNat) ≤ (v ||| 1#64).clz.toNat * 0 + (v ||| 1#64).toNat := by
    simpa using BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by decide) hxne
  have hhi : (v ||| 1#64).toNat < 2 ^ (64 - (v ||| 1#64).clz.toNat) :=
    BitVec.toNat_lt_two_pow_sub_clz
  have h1 : (v >>> s).toNat < 128 ↔ v.toNat >>> (s + 7) = 0 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.pow_add, ← Nat.div_div_eq_div_mul]
    exact (Nat.div_eq_zero_iff_lt (by decide)).symm
  have h2 : (v ||| 1#64).toNat >>> (s + 7) = v.toNat >>> (s + 7) := by
    change (v.toNat ||| 1) >>> (s + 7) = v.toNat >>> (s + 7)
    rw [Nat.shiftRight_or_distrib]
    have h1z : 1 >>> (s + 7) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      have : 2 ^ 7 ≤ 2 ^ (s + 7) := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.div_eq_of_lt (by omega)
    rw [h1z, Nat.or_zero]
  rw [h1, ← h2, Nat.shiftRight_eq_div_pow]
  constructor
  · intro hdiv
    by_contra hgt
    have hle : s + 7 ≤ 63 - (v ||| 1#64).clz.toNat := by omega
    have hpow : 2 ^ (s + 7) ≤ 2 ^ (63 - (v ||| 1#64).clz.toNat) := Nat.pow_le_pow_right (by decide) hle
    have hlt := (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos (s + 7))).mp hdiv
    omega
  · intro hle
    have hpow : 2 ^ (64 - (v ||| 1#64).clz.toNat) ≤ 2 ^ (s + 7) := Nat.pow_le_pow_right (by decide) hle
    exact Nat.div_eq_of_lt (by omega)

private def clzTree_er (c : BitVec 64) : Nat :=
  if 64 - c.toNat ≤ 7 then 1
  else if 64 - c.toNat ≤ 14 then 2
  else if 64 - c.toNat ≤ 21 then 3
  else if 64 - c.toNat ≤ 28 then 4
  else if 64 - c.toNat ≤ 35 then 5
  else if 64 - c.toNat ≤ 42 then 6
  else if 64 - c.toNat ≤ 49 then 7
  else if 64 - c.toNat ≤ 56 then 8
  else if 64 - c.toNat ≤ 63 then 9
  else 10

private theorem hwFormula_eq_clzTree_of_lt_er :
    ∀ k : Fin 64,
      let c := BitVec.ofNat 64 k.val
      ((((c ^^^ 0x3f#64) + ((c ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
        BitVec.ofNat 64 (clzTree_er c)) := by
  decide

private theorem ushiftRight_add_64_er (w : BitVec 64) (a b : Nat) :
    (w >>> a) >>> b = w >>> (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    ← Nat.pow_add]

private theorem encodeVarint_length_eq_clzTree_er (v : BitVec 64) :
    (encodeVarint v).length = clzTree_er (v ||| 1#64).clz := by
  unfold encodeVarint clzTree_er
  dsimp only [encodeVarintAux]
  have h0_eq : (v.toNat < 128) ↔ 64 - (v ||| 1#64).clz.toNat ≤ 7 := by
    simpa using shiftRight_lt_128_iff_er v 0
  simp only [ushiftRight_add_64_er, Nat.reduceAdd, h0_eq, shiftRight_lt_128_iff_er]
  have h10 : 64 - (v ||| 1#64).clz.toNat ≤ 70 := by omega
  by_cases c1 : 64 - (v ||| 1#64).clz.toNat ≤ 7 <;> simp only [c1, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c2 : 64 - (v ||| 1#64).clz.toNat ≤ 14 <;> simp only [c2, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c3 : 64 - (v ||| 1#64).clz.toNat ≤ 21 <;> simp only [c3, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c4 : 64 - (v ||| 1#64).clz.toNat ≤ 28 <;> simp only [c4, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c5 : 64 - (v ||| 1#64).clz.toNat ≤ 35 <;> simp only [c5, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c6 : 64 - (v ||| 1#64).clz.toNat ≤ 42 <;> simp only [c6, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c7 : 64 - (v ||| 1#64).clz.toNat ≤ 49 <;> simp only [c7, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c8 : 64 - (v ||| 1#64).clz.toNat ≤ 56 <;> simp only [c8, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c9 : 64 - (v ||| 1#64).clz.toNat ≤ 63 <;> simp only [c9, ↓reduceIte, List.length_cons, List.length_nil, h10]

theorem erHwVarintLen_eq_encodeVarint_length (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 0x3f#64) + (((v ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
      BitVec.ofNat 64 (encodeVarint v).length := by
  have hlt := or_one_clz_toNat_lt_er v
  have hfin := hwFormula_eq_clzTree_of_lt_er ⟨(v ||| 1#64).clz.toNat, hlt⟩
  have hclz : BitVec.ofNat 64 (v ||| 1#64).clz.toNat = (v ||| 1#64).clz := by
    apply BitVec.eq_of_toNat_eq; simp
  dsimp only at hfin
  rw [hclz] at hfin
  rw [hfin, encodeVarint_length_eq_clzTree_er]

theorem erHwVarintLen_bvShift_eq_encodeVarint_length (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 63#64) + (((v ||| 1#64).clz ^^^ 63#64) <<< 3#64)) + 73#64) >>> 6#64 =
      BitVec.ofNat 64 (encodeVarint v).length :=
  erHwVarintLen_eq_encodeVarint_length v

theorem er_truncate32_zext64_lsr6 (x : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 x >>> 6) = x >>> 6 := by
  ext i hi
  simp
  omega

set_option allowUnsafeReducibility true
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local irreducible] stackAt vecRest vecU8Buf vecSrcRest vecCopyDone
attribute [local irreducible] optU32ValAt pendingTailRest
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  Prost.ofNat_countLeadingZeros_64
  Prost.ofNat_countLeadingZeros_32
  Prost.truncate32_ofNat64
  er_truncate32_zext64_lsr6
  erHwVarintLen_eq_encodeVarint_length
  erHwVarintLen_bvShift_eq_encodeVarint_length

@[local arm64_norm]
theorem bv_add_neg80_3a (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 :=
  (BitVec.sub_eq_add_neg x 80#64).symm

set_option maxHeartbeats 400000

/-! ## Outer tag `0x4a` (`+0x218..+0x254/+0x2fc`) -/

theorem optU32Tag_bne1_pc (entry : BitVec 64) (opt : Option (BitVec 32)) :
    (if (optU32Tag opt != 1#32) = true then entry + bv% (764) else entry + bv% (596)) =
      entry + (if opt.isSome then 596#64 else 764#64) := by
  cases opt <;> rfl

theorem step_tag9_write_tag {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hcap_g : g.vec.cap.toNat < 2 ^ 63)
    (hlen_lt : bs.length + 1 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 536#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A ss g p ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName +
        (if p.preKeyId.isSome then 596#64 else 764#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      EncRawUpperSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs ++ [0x4a#8]) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf b C A ctl abs hDR
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 536 596
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 2124 2152
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
    (h := fun hle _ _ => ?_)
  have hcmn1 := cmn1_beq_zero_false hcap_g
  have hcmn2 := cap_beq_noneCap_false hcap_g
  by_cases hlt : bs.length < cap.toNat
  · have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_one A v cap ptr bs hlt]
    unfold pendingOpenAt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun old => ?_
    apply SepWPp.of_sepWP (mid := entry + (if p.preKeyId.isSome then 596#64 else 764#64))
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
      (by simp only [arm64_norm, *])
    refine SepWPp.weaken_pre ?_ (hnext _ cap ptr
      (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    rw [← vecU8At_close_one A v cap ptr bs 0x4a#8 hlt]
    unfold pendingOpenAt
    exact entails_of_sep_focus (by sep_focus)
  · have hcap_eq : cap.toNat = bs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
    unfold pendingOpenAt
    simp only [vecHeader, sepConj_assoc]
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine hCallDR sp0 v cap ptr (entry + bv% (2144)) bs 1
      (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm]
    · simp only [arm64_norm]
    · intro s1 newCap p1 hpc1 hrun1 hsp1 htr1 hcs1 hnew_ge _
      have hx19_1 : s1.readReg64 .x19 = v := by
        have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by
        have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      have hlt_new : bs.length < newCap.toNat := by omega
      rw [vecU8At_open_one A v newCap p1 bs hlt_new]
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_elim fun old => ?_
      apply SepWPp.of_sepWP (mid := entry + (if p.preKeyId.isSome then 596#64 else 764#64))
      wp_steps
      apply SepWP.done
        (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
        (by simp only [arm64_norm, *])
      refine SepWPp.weaken_pre ?_ (hnext _ newCap p1
        (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [← vecU8At_close_one A v newCap p1 bs 0x4a#8 hlt_new]
      unfold pendingOpenAt
      exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 1 length (`pre_key_id`, `596/764..636`) -/

theorem ofNat64_len_bne_zero_true {bs : List (BitVec 8)} (hne : bs ≠ []) (hlt : bs.length < 2 ^ 63) :
    (BitVec.ofNat 64 bs.length != 0#64) = true := by
  simp only [bne, ofNat64_len_beq_zero_false hne hlt, Bool.not_false]

theorem step_tag9_len1 {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (ss v sp0 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (hne_vec : g.vec.bytes ≠ []) (hlt_vec : g.vec.bytes.length < 2 ^ 63)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName +
      (if p.preKeyId.isSome then 596#64 else 764#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId))
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = pendingOpenAt A ss g p ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 636#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      EncRawUpperSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm (pendingOpenAt A ss g p ∗ F) Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 596 636
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 764 776
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
  examples_hide_fetches
  have hbeq0 := ofNat64_len_beq_zero_false hne_vec hlt_vec
  have hbne0 := ofNat64_len_bne_zero_true hne_vec hlt_vec
  rw [hP]
  unfold pendingOpenAt
  cases hpk : p.preKeyId with
  | none =>
    simp only [hpk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    simp only [sepConj_assoc]
    apply SepWPp.of_sepWP (mid := entry + bv% (636))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPp.weaken_pre ?_ (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hpk, optUint32Field1_none_eq])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    unfold pendingOpenAt
    simp only [hpk]
    exact entails_of_sep_focus (by sep_focus)
  | some pkId =>
    simp only [hpk, Option.isSome_some, ↓reduceIte] at hpc
    have hpk_val : optU32ValAt (ss + 276#64) g.tail (some pkId) = ((ss + 276#64) ↦₃₂ pkId) :=
      optU32ValAt_some _ _ _
    rw [hpk_val]
    simp only [sepConj_assoc]
    apply SepWPp.of_sepWP (mid := entry + bv% (636))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPp.weaken_pre ?_ (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, ← optUint32Field1_some_length_bv pkId, *])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    unfold pendingOpenAt
    simp only [hpk, hpk_val]
    exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 2 length (`base_key`, `636..672/788`) -/

theorem zext64_beq_zero_eq (v : BitVec 32) :
    (BitVec.zeroExtend 64 v == 0#64) = (v == 0#32) := by
  by_cases hv : v = 0#32
  · subst hv; rfl
  · rw [beq_false_of_ne hv, beq_eq_false_iff_ne]
    intro heq
    exact hv (by rw [← truncate32_zeroExtend64 v, heq]; rfl)

theorem spk_cbz_pc (entry : BitVec 64) (v : BitVec 32) :
    (if (BitVec.zeroExtend 64 v == 0#64) = true then entry + bv% (788) else entry + bv% (672)) =
      entry + (if v == 0#32 then 788#64 else 672#64) := by
  rw [zext64_beq_zero_eq v]
  cases v == 0#32 <;> rfl

theorem step_tag9_len2 {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (ss v sp0 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (hne_vec : g.vec.bytes ≠ [])
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName + 636#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = pendingOpenAt A ss g p ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName +
        (if p.signedPreKeyId == 0#32 then 788#64 else 672#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length →
      sm.readReg64 .x9 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      EncRawUpperSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm (pendingOpenAt A ss g p ∗ F) Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 636 672
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  unfold pendingOpenAt
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := entry + (if p.signedPreKeyId == 0#32 then 788#64 else 672#64))
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, spk_cbz_pc, *])
    (by simp only [arm64_norm, *])
  refine SepWPp.weaken_pre ?_ (hnext _
    (by simp only [arm64_norm, spk_cbz_pc, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, ← bytesField2_nonempty_length_bv hne_vec, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
  unfold pendingOpenAt
  exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 3 length (`signed_pre_key_id`, `672/788..708/800`) -/

theorem ts_cbz_pc (entry : BitVec 64) (v : BitVec 64) :
    (if (v == 0#64) = true then entry + bv% (800) else entry + bv% (708)) =
      entry + (if v == 0#64 then 800#64 else 708#64) := by
  cases v == 0#64 <;> rfl

theorem ts_cbnz_pc (entry : BitVec 64) (v : BitVec 64) :
    (if ¬(v == 0#64) = true then entry + bv% (708) else entry + bv% (800)) =
      entry + (if v == 0#64 then 800#64 else 708#64) := by
  cases v == 0#64 <;> rfl

theorem step_tag9_len3 {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (ss v sp0 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName +
      (if p.signedPreKeyId == 0#32 then 788#64 else 672#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length)
    (hx22 : s.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = pendingOpenAt A ss g p ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName +
        (if p.timestamp == 0#64 then 800#64 else 708#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length →
      sm.readReg64 .x9 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length →
      sm.readReg64 .x10 = BitVec.ofNat 64 (int32Field 3 p.signedPreKeyId).length →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm (pendingOpenAt A ss g p ∗ F) Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 672 708
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 788 800
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  unfold pendingOpenAt
  simp only [sepConj_assoc]
  by_cases hspk : p.signedPreKeyId = 0#32
  · simp only [hspk, beq_self_eq_true, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP (mid := entry + (if p.timestamp == 0#64 then 800#64 else 708#64))
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm, ts_cbnz_pc, *])
      (by simp only [arm64_norm, *])
    refine SepWPp.weaken_pre ?_ (hnext _
      (by simp only [arm64_norm, ts_cbnz_pc, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hspk, int32Field3_zero_eq])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    unfold pendingOpenAt
    exact entails_of_sep_focus (by sep_focus)
  · have hspk_beq : (p.signedPreKeyId == 0#32) = false := bv32_beq_zero_false hspk
    simp only [hspk_beq, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP (mid := entry + (if p.timestamp == 0#64 then 800#64 else 708#64))
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm, ts_cbz_pc, *])
      (by simp only [arm64_norm, *])
    refine SepWPp.weaken_pre ?_ (hnext _
      (by simp only [arm64_norm, ts_cbz_pc, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, ← int32Field3_nonzero_length_bv hspk, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    unfold pendingOpenAt
    exact entails_of_sep_focus (by sep_focus)

/-! ## Subfield 4 length and outer varint (`708/800..824/872`) -/

theorem optU32Tag_cbz_pc (entry : BitVec 64) (opt : Option (BitVec 32)) :
    (if (optU32Tag opt == 0#32) = true then entry + bv% (872) else entry + bv% (824)) =
      entry + (if opt.isSome then 824#64 else 872#64) := by
  cases opt <;> rfl

theorem step_tag9_len4 {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 11 < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName +
      (if p.timestamp == 0#64 then 800#64 else 708#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (int32Field 3 p.signedPreKeyId).length)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length)
    (hx22 : s.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId)
    (hx21 : s.readReg64 .x21 = p.timestamp)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A ss g p ∗ vecU8At A v cap ptr (bs ++ [0x4a#8]) ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName +
        (if p.preKeyId.isSome then 824#64 else 872#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((pendingOpenAt A ss g p ∗
          vecU8At A v cap' ptr'
            (bs ++ [0x4a#8] ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint b C A ctl abs hEV
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 708 764
  encraw_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 800 824
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  by_cases hts : p.timestamp = 0#64
  · simp only [hts, beq_self_eq_true, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallEV sp0 (BitVec.ofNat 64 (encPendingMem g p).length) v cap ptr (entry + bv% (820))
      (bs ++ [0x4a#8]) (by simp; omega)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm, ← encPendingMem_length_bv_ts_zero g p hts, *]
    · simp only [arm64_norm, *]
    · intro sm cap' ptr' hpcm hrunm hspm htrm hcsm
      have hx19m : sm.readReg64 .x19 = v := by
        have := hcsm.1; simp only [arm64_norm, *] at this; exact this
      have hx20m : sm.readReg64 .x20 = ss := by
        have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21m : sm.readReg64 .x21 = p.timestamp := by
        have := hcsm.2.2.1; simp only [arm64_norm, *] at this; rw [hts]; exact this
      have hx22m : sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId := by
        have := hcsm.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length := by
        have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx24m : sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) := by
        have := hcsm.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      cases hpk : p.preKeyId with
      | none =>
        simp only [hpk, optU32Tag] at hx24m
        apply SepWPp.of_sepWP (mid := entry + bv% (872))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPp.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact entails_of_sep_focus (by sep_focus)
      | some pkId =>
        simp only [hpk, optU32Tag] at hx24m
        apply SepWPp.of_sepWP (mid := entry + bv% (824))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPp.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, ↓reduceIte, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact entails_of_sep_focus (by sep_focus)
  · have hts_beq : (p.timestamp == 0#64) = false := bv64_beq_zero_false hts
    simp only [hts_beq, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallEV sp0 (BitVec.ofNat 64 (encPendingMem g p).length) v cap ptr (entry + bv% (756))
      (bs ++ [0x4a#8]) (by simp; omega)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm, ← uint64Field4_nonzero_length_bv hts, ← encPendingMem_length_bv g p, *]
    · simp only [arm64_norm, *]
    · intro sm cap' ptr' hpcm hrunm hspm htrm hcsm
      have hx19m : sm.readReg64 .x19 = v := by
        have := hcsm.1; simp only [arm64_norm, *] at this; exact this
      have hx20m : sm.readReg64 .x20 = ss := by
        have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21m : sm.readReg64 .x21 = p.timestamp := by
        have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22m : sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId := by
        have := hcsm.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length := by
        have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx24m : sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) := by
        have := hcsm.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      cases hpk : p.preKeyId with
      | none =>
        simp only [hpk, optU32Tag] at hx24m
        apply SepWPp.of_sepWP (mid := entry + bv% (872))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPp.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact entails_of_sep_focus (by sep_focus)
      | some pkId =>
        simp only [hpk, optU32Tag] at hx24m
        apply SepWPp.of_sepWP (mid := entry + bv% (824))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPp.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, ↓reduceIte, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact entails_of_sep_focus (by sep_focus)

/-! ## Relocatable `[LibsignalPlacement]` proofs (block `14`) -/

section Placed

set_option allowUnsafeReducibility false

open CryptoVerification CryptoVerification.E2E.Record.Placed

variable [LibsignalPlacement]

theorem step_tag9_write_tag_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDR : subroutine_ok (lsProg_13 H) (blkPl_13).base (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hcap_g : g.vec.cap.toNat < 2 ^ 63)
    (hlen_lt : bs.length + 1 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 536#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A ss g p ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + (if p.preKeyId.isSome then 596#64 else 764#64) →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs ++ [0x4a#8]) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf_placed _ A H hDR
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
    (h := fun hle _ _ => ?_)
  have hcmn1 := cmn1_beq_zero_false hcap_g
  have hcmn2 := cap_beq_noneCap_false hcap_g
  by_cases hlt : bs.length < cap.toNat
  · have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_one A v cap ptr bs hlt]
    unfold pendingOpenAt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun old => ?_
    apply sepWPp_of_sepWP_lscl_er hcl
      (mid := (blkPl_14).base + (if p.preKeyId.isSome then 596#64 else 764#64))
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
      (by simp only [arm64_norm, *])
    intro hcl_end
    refine SepWPp.weaken_pre ?_ (hnext _ cap ptr
      (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
      (by simp only [arm64_norm, *])
      hcl_end
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    rw [← vecU8At_close_one A v cap ptr bs 0x4a#8 hlt]
    unfold pendingOpenAt
    exact entails_of_sep_focus (by sep_focus)
  · have hcap_eq : cap.toNat = bs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
    unfold pendingOpenAt
    simp only [vecHeader, sepConj_assoc]
    apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl_call
    have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2144#64) bs 1
      (by omega) (by omega) ?_ ?_ hcl_call ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm]
    · simp only [arm64_norm]
    · intro s1 newCap p1 hpc1 hrun1 hcl1 hsp1 htr1 hcs1 hnew_ge _
      have hx19_1 : s1.readReg64 .x19 = v := by
        have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by
        have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      have hlt_new : bs.length < newCap.toNat := by omega
      rw [vecU8At_open_one A v newCap p1 bs hlt_new]
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_elim fun old => ?_
      apply sepWPp_of_sepWP_lscl_er hcl1
        (mid := (blkPl_14).base + (if p.preKeyId.isSome then 596#64 else 764#64))
      wp_steps
      apply SepWP.done
        (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
        (by simp only [arm64_norm, *])
      intro hcl_end
      refine SepWPp.weaken_pre ?_ (hnext _ newCap p1
        (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
        (by simp only [arm64_norm, *])
        hcl_end
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [← vecU8At_close_one A v newCap p1 bs 0x4a#8 hlt_new]
      unfold pendingOpenAt
      exact entails_of_sep_focus (by sep_focus)

theorem step_tag9_len1_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (ss v sp0 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (hne_vec : g.vec.bytes ≠ []) (hlt_vec : g.vec.bytes.length < 2 ^ 63)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + (if p.preKeyId.isSome then 596#64 else 764#64))
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId))
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = pendingOpenAt A ss g p ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_14).base + 636#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm (pendingOpenAt A ss g p ∗ F) Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hbeq0 := ofNat64_len_beq_zero_false hne_vec hlt_vec
  have hbne0 := ofNat64_len_bne_zero_true hne_vec hlt_vec
  rw [hP]
  unfold pendingOpenAt
  cases hpk : p.preKeyId with
  | none =>
    simp only [hpk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    simp only [sepConj_assoc]
    apply sepWPp_of_sepWP_lscl_er hcl (mid := (blkPl_14).base + 636#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl_end
    refine SepWPp.weaken_pre ?_ (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hcl_end
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hpk, optUint32Field1_none_eq])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    unfold pendingOpenAt
    simp only [hpk]
    exact entails_of_sep_focus (by sep_focus)
  | some pkId =>
    simp only [hpk, Option.isSome_some, ↓reduceIte] at hpc
    have hpk_val : optU32ValAt (ss + 276#64) g.tail (some pkId) = ((ss + 276#64) ↦₃₂ pkId) :=
      optU32ValAt_some _ _ _
    rw [hpk_val]
    simp only [sepConj_assoc]
    apply sepWPp_of_sepWP_lscl_er hcl (mid := (blkPl_14).base + 636#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl_end
    refine SepWPp.weaken_pre ?_ (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hcl_end
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, ← optUint32Field1_some_length_bv pkId, *])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    unfold pendingOpenAt
    simp only [hpk, hpk_val]
    exact entails_of_sep_focus (by sep_focus)

theorem step_tag9_len2_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (ss v sp0 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (hne_vec : g.vec.bytes ≠ [])
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 636#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = pendingOpenAt A ss g p ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_14).base + (if p.signedPreKeyId == 0#32 then 788#64 else 672#64) →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length →
      sm.readReg64 .x9 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm (pendingOpenAt A ss g p ∗ F) Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  rw [hP]
  unfold pendingOpenAt
  simp only [sepConj_assoc]
  apply sepWPp_of_sepWP_lscl_er hcl
    (mid := (blkPl_14).base + (if p.signedPreKeyId == 0#32 then 788#64 else 672#64))
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, spk_cbz_pc, *])
    (by simp only [arm64_norm, *])
  intro hcl_end
  refine SepWPp.weaken_pre ?_ (hnext _
    (by simp only [arm64_norm, spk_cbz_pc, *])
    (by simp only [arm64_norm, *])
    hcl_end
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, ← bytesField2_nonempty_length_bv hne_vec, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
  unfold pendingOpenAt
  exact entails_of_sep_focus (by sep_focus)

theorem step_tag9_len3_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (ss v sp0 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + (if p.signedPreKeyId == 0#32 then 788#64 else 672#64))
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length)
    (hx22 : s.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = pendingOpenAt A ss g p ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_14).base + (if p.timestamp == 0#64 then 800#64 else 708#64) →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length →
      sm.readReg64 .x9 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length →
      sm.readReg64 .x10 = BitVec.ofNat 64 (int32Field 3 p.signedPreKeyId).length →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm (pendingOpenAt A ss g p ∗ F) Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  rw [hP]
  unfold pendingOpenAt
  simp only [sepConj_assoc]
  by_cases hspk : p.signedPreKeyId = 0#32
  · simp only [hspk, beq_self_eq_true, ↓reduceIte] at hpc
    apply sepWPp_of_sepWP_lscl_er hcl
      (mid := (blkPl_14).base + (if p.timestamp == 0#64 then 800#64 else 708#64))
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm, ts_cbnz_pc, *])
      (by simp only [arm64_norm, *])
    intro hcl_end
    refine SepWPp.weaken_pre ?_ (hnext _
      (by simp only [arm64_norm, ts_cbnz_pc, *])
      (by simp only [arm64_norm, *])
      hcl_end
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hspk, int32Field3_zero_eq])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    unfold pendingOpenAt
    exact entails_of_sep_focus (by sep_focus)
  · have hspk_beq : (p.signedPreKeyId == 0#32) = false := bv32_beq_zero_false hspk
    simp only [hspk_beq, Bool.false_eq_true, ↓reduceIte] at hpc
    apply sepWPp_of_sepWP_lscl_er hcl
      (mid := (blkPl_14).base + (if p.timestamp == 0#64 then 800#64 else 708#64))
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm, ts_cbz_pc, *])
      (by simp only [arm64_norm, *])
    intro hcl_end
    refine SepWPp.weaken_pre ?_ (hnext _
      (by simp only [arm64_norm, ts_cbz_pc, *])
      (by simp only [arm64_norm, *])
      hcl_end
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, ← int32Field3_nonzero_length_bv hspk, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    unfold pendingOpenAt
    exact entails_of_sep_focus (by sep_focus)

theorem step_tag9_len4_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (hEV : subroutine_ok (lsProg_10 H) (blkPl_10).base (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 11 < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + (if p.timestamp == 0#64 then 800#64 else 708#64))
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (int32Field 3 p.signedPreKeyId).length)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length)
    (hx22 : s.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId)
    (hx21 : s.readReg64 .x21 = p.timestamp)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A ss g p ∗ vecU8At A v cap ptr (bs ++ [0x4a#8]) ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + (if p.preKeyId.isSome then 824#64 else 872#64) →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPp (lsProg_14 H) ret sm
        ((pendingOpenAt A ss g p ∗
          vecU8At A v cap' ptr'
            (bs ++ [0x4a#8] ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPp (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint_placed _ A H hEV
  rw [hP]
  by_cases hts : p.timestamp = 0#64
  · simp only [hts, beq_self_eq_true, ↓reduceIte] at hpc
    apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl_call
    refine hCallEV sp0 (BitVec.ofNat 64 (encPendingMem g p).length) v cap ptr
      ((blkPl_14).base + 820#64) (bs ++ [0x4a#8]) (by simp; omega)
      ?_ ?_ hcl_call ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm, ← encPendingMem_length_bv_ts_zero g p hts, *]
    · simp only [arm64_norm, *]
    · intro sm cap' ptr' hpcm hrunm hclm hspm htrm hcsm
      have hx19m : sm.readReg64 .x19 = v := by
        have := hcsm.1; simp only [arm64_norm, *] at this; exact this
      have hx20m : sm.readReg64 .x20 = ss := by
        have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21m : sm.readReg64 .x21 = p.timestamp := by
        have := hcsm.2.2.1; simp only [arm64_norm, *] at this; rw [hts]; exact this
      have hx22m : sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId := by
        have := hcsm.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length := by
        have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx24m : sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) := by
        have := hcsm.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      cases hpk : p.preKeyId with
      | none =>
        simp only [hpk, optU32Tag] at hx24m
        apply sepWPp_of_sepWP_lscl_er hclm (mid := (blkPl_14).base + 872#64)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hcl_end
        refine SepWPp.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
          (by simp only [arm64_norm, *])
          hcl_end
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact entails_of_sep_focus (by sep_focus)
      | some pkId =>
        simp only [hpk, optU32Tag] at hx24m
        apply sepWPp_of_sepWP_lscl_er hclm (mid := (blkPl_14).base + 824#64)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hcl_end
        refine SepWPp.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, ↓reduceIte, *])
          (by simp only [arm64_norm, *])
          hcl_end
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact entails_of_sep_focus (by sep_focus)
  · have hts_beq : (p.timestamp == 0#64) = false := bv64_beq_zero_false hts
    simp only [hts_beq, Bool.false_eq_true, ↓reduceIte] at hpc
    apply sepWPp_of_sepWP_lscl_er hcl (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl_call
    refine hCallEV sp0 (BitVec.ofNat 64 (encPendingMem g p).length) v cap ptr
      ((blkPl_14).base + 756#64) (bs ++ [0x4a#8]) (by simp; omega)
      ?_ ?_ hcl_call ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm, ← uint64Field4_nonzero_length_bv hts, ← encPendingMem_length_bv g p, *]
    · simp only [arm64_norm, *]
    · intro sm cap' ptr' hpcm hrunm hclm hspm htrm hcsm
      have hx19m : sm.readReg64 .x19 = v := by
        have := hcsm.1; simp only [arm64_norm, *] at this; exact this
      have hx20m : sm.readReg64 .x20 = ss := by
        have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21m : sm.readReg64 .x21 = p.timestamp := by
        have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22m : sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId := by
        have := hcsm.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length := by
        have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx24m : sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) := by
        have := hcsm.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      cases hpk : p.preKeyId with
      | none =>
        simp only [hpk, optU32Tag] at hx24m
        apply sepWPp_of_sepWP_lscl_er hclm (mid := (blkPl_14).base + 872#64)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hcl_end
        refine SepWPp.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
          (by simp only [arm64_norm, *])
          hcl_end
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact entails_of_sep_focus (by sep_focus)
      | some pkId =>
        simp only [hpk, optU32Tag] at hx24m
        apply sepWPp_of_sepWP_lscl_er hclm (mid := (blkPl_14).base + 824#64)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hcl_end
        refine SepWPp.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, ↓reduceIte, *])
          (by simp only [arm64_norm, *])
          hcl_end
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact entails_of_sep_focus (by sep_focus)

end Placed

end CryptoVerification.E2E.Record.Serialization.EncodeRawAux
