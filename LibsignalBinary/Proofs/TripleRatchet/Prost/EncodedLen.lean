/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
public import LibsignalBinary.Proofs.CodeLayout
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

-- Instruction decode lemmas for `encoded_len` (`0x28f50`) and `encode_varint` (`0x30a0`).
gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len") → (ls_off% "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len" + 160), (ls_off% "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len" + 168) → (ls_off% "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len" + 304),
    (ls_off% "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len" + 312) → (ls_off% "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len" + 384), (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") → (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]" + 1060)]

/-- Threshold decision tree equivalent to `(encodeVarint v).length`. -/
def varintLenBV (v : BitVec 64) : BitVec 64 :=
  if v < 0x80#64 then 1#64
  else if v >>> 7 < 0x80#64 then 2#64
  else if v >>> 14 < 0x80#64 then 3#64
  else if v >>> 21 < 0x80#64 then 4#64
  else if v >>> 28 < 0x80#64 then 5#64
  else if v >>> 35 < 0x80#64 then 6#64
  else if v >>> 42 < 0x80#64 then 7#64
  else if v >>> 49 < 0x80#64 then 8#64
  else if v >>> 56 < 0x80#64 then 9#64
  else 10#64

private theorem or_one_ne_zero (x : BitVec 64) : (x ||| 1#64) ≠ 0#64 := by
  bv_bits

private theorem or_one_div_two (x : BitVec 64) :
    (x ||| 1#64).toNat / 2 = x.toNat / 2 := by
  have h : (x ||| 1#64) >>> 1 = x >>> 1 := by bv_bits
  have h1 : ((x ||| 1#64) >>> 1).toNat = (x >>> 1).toNat := congrArg BitVec.toNat h
  simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using h1

private theorem shr_lt_128_iff_clz_gt (v : BitVec 64) (s : Nat) (hs : s ≤ 56) :
    (v >>> s < 0x80#64) ↔ BitVec.ofNat 64 (56 - s) < (v ||| 1#64).clz := by
  have hc_le : (v ||| 1#64).clz.toNat ≤ 63 := ProofLib.clz_or_one_toNat_le v
  have hlo : 2 ^ (64 - 1 - (v ||| 1#64).clz.toNat) ≤ (v ||| 1#64).toNat :=
    BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by decide : 0 < 64) (or_one_ne_zero v)
  have hhi : (v ||| 1#64).toNat < 2 ^ (64 - (v ||| 1#64).clz.toNat) :=
    BitVec.toNat_lt_two_pow_sub_clz
  have hdiv := or_one_div_two v
  have hpow_s : 2 ^ (s + 7) = 128 * 2 ^ s := by rw [Nat.pow_add, Nat.mul_comm]
  have hpow_even : 2 ^ (s + 7) = 2 * 2 ^ (s + 6) := by
    rw [show s + 7 = (s + 6) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  have h1 : (v >>> s < 0x80#64) ↔ v.toNat < 2 ^ (s + 7) := by
    rw [BitVec.lt_def, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    change v.toNat / 2 ^ s < 128 ↔ v.toNat < 2 ^ (s + 7)
    rw [hpow_s]
    have : 0 < 2 ^ s := Nat.two_pow_pos s
    exact Nat.div_lt_iff_lt_mul this
  have h2 : v.toNat < 2 ^ (s + 7) ↔ (v ||| 1#64).toNat < 2 ^ (s + 7) := by
    omega
  have h3 : (v ||| 1#64).toNat < 2 ^ (s + 7) ↔ 56 - s < (v ||| 1#64).clz.toNat := by
    constructor
    · intro hlt
      have hpow_lt : 2 ^ (64 - 1 - (v ||| 1#64).clz.toNat) < 2 ^ (s + 7) :=
        Nat.lt_of_le_of_lt hlo hlt
      have hexp : 64 - 1 - (v ||| 1#64).clz.toNat < s + 7 :=
        (Nat.pow_lt_pow_iff_right (by decide)).mp hpow_lt
      omega
    · intro hgt
      have hexp : 64 - (v ||| 1#64).clz.toNat ≤ s + 7 := by omega
      exact Nat.lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by decide) hexp)
  have h4 : 56 - s < (v ||| 1#64).clz.toNat ↔ BitVec.ofNat 64 (56 - s) < (v ||| 1#64).clz := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact h1.trans (h2.trans (h3.trans h4))

private theorem hwVarintLen_eq_varintLenBV (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 0x3f#64) + (((v ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
      varintLenBV v := by
  unfold varintLenBV
  have hv0 : (v < 0x80#64) ↔ (v >>> 0 < 0x80#64) := by simp
  simp only [hv0,
      shr_lt_128_iff_clz_gt v 0 (by decide),
      shr_lt_128_iff_clz_gt v 7 (by decide),
      shr_lt_128_iff_clz_gt v 14 (by decide),
      shr_lt_128_iff_clz_gt v 21 (by decide),
      shr_lt_128_iff_clz_gt v 28 (by decide),
      shr_lt_128_iff_clz_gt v 35 (by decide),
      shr_lt_128_iff_clz_gt v 42 (by decide),
      shr_lt_128_iff_clz_gt v 49 (by decide),
      shr_lt_128_iff_clz_gt v 56 (by decide)]
  have hle : (v ||| 1#64).clz ≤ 63#64 := ProofLib.clz_or_one_le v
  generalize (v ||| 1#64).clz = c at hle ⊢
  have hc : c = (c.truncate 8).zeroExtend 64 := by bv_bits
  have hc8 : c.truncate 8 ≤ 63#8 := by bv_bits
  rw [hc]
  generalize c.truncate 8 = b at hc8 ⊢
  revert b hc8; decide

private theorem hwVarintLen_bvShift_eq_varintLenBV (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 63#64) + (((v ||| 1#64).clz ^^^ 63#64) <<< 3#64)) + 73#64) >>> 6#64 =
      varintLenBV v :=
  hwVarintLen_eq_varintLenBV v

private theorem shr_63_lt_128 (v : BitVec 64) : (v >>> 63).toNat < 128 := by
  have h : v >>> 63 < 0x80#64 := by bv_bits
  exact h

private theorem ushiftRight_add (w : BitVec 64) (a b : Nat) :
    (w >>> a) >>> b = w >>> (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    ← Nat.pow_add]

private theorem toNat_lt_128_eq (w : BitVec 64) : (w.toNat < 128) = (w < 0x80#64) := rfl

theorem varintLenBV_eq_encodeVarint_length (v : BitVec 64) :
    varintLenBV v = BitVec.ofNat 64 (encodeVarint v).length := by
  unfold varintLenBV encodeVarint
  dsimp only [encodeVarintAux]
  simp only [ushiftRight_add, Nat.reduceAdd, toNat_lt_128_eq]
  by_cases h0 : v < 0x80#64 <;> simp only [h0, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  by_cases h1 : v >>> 7 < 0x80#64 <;> simp only [h1, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h2 : v >>> 14 < 0x80#64 <;> simp only [h2, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h3 : v >>> 21 < 0x80#64 <;> simp only [h3, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h4 : v >>> 28 < 0x80#64 <;> simp only [h4, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h5 : v >>> 35 < 0x80#64 <;> simp only [h5, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h6 : v >>> 42 < 0x80#64 <;> simp only [h6, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h7 : v >>> 49 < 0x80#64 <;> simp only [h7, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h8 : v >>> 56 < 0x80#64 <;> simp only [h8, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  have h9 : v >>> 63 < 0x80#64 := by bv_bits
  simp only [h9, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]

@[local arm64_norm]
theorem hwVarintLen_eq_encodeVarint_length (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 0x3f#64) + (((v ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
      BitVec.ofNat 64 (encodeVarint v).length := by
  rw [hwVarintLen_eq_varintLenBV, varintLenBV_eq_encodeVarint_length]

@[local arm64_norm]
theorem hwVarintLen_bvShift_eq_encodeVarint_length (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 63#64) + (((v ||| 1#64).clz ^^^ 63#64) <<< 3#64)) + 73#64) >>> 6#64 =
      BitVec.ofNat 64 (encodeVarint v).length := by
  rw [hwVarintLen_bvShift_eq_varintLenBV, varintLenBV_eq_encodeVarint_length]

private theorem encodeVarintAux_length_le (n : Nat) (v : BitVec 64) :
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

private theorem encodeVarintAux_succ_length_pos (n : Nat) (v : BitVec 64) :
    1 ≤ (encodeVarintAux (n + 1) v).length := by
  unfold encodeVarintAux
  split <;> simp

theorem encodeVarint_length_bounds (v : BitVec 64) :
    1 ≤ (encodeVarint v).length ∧ (encodeVarint v).length ≤ 10 :=
  ⟨encodeVarintAux_succ_length_pos 9 v, encodeVarintAux_length_le 10 v⟩

theorem encodeVarint_length_eq_varintLen (v : BitVec 64) :
    (encodeVarint v).length = varintLen v := by
  have h1 := hwVarintLen_eq_encodeVarint_length v
  have hb := encodeVarint_length_bounds v
  have h2 : (((((v ||| 1#64).clz ^^^ 0x3f#64) + (((v ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6).toNat =
      varintLen v := by
    unfold varintLen
    have hbv : ((((v ||| 1#64).clz ^^^ 0x3f#64) + (((v ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
        (((v ||| 1#64).clz ^^^ 0x3f#64) * 9#64 + 73#64) >>> 6 := by
      have hle : (v ||| 1#64).clz ≤ 63#64 := ProofLib.clz_or_one_le v
      generalize (v ||| 1#64).clz = c at hle ⊢
      have hc : c = (c.truncate 8).zeroExtend 64 := by bv_bits
      have hc8 : c.truncate 8 ≤ 63#8 := by bv_bits
      rw [hc]
      generalize c.truncate 8 = b at hc8 ⊢
      revert b hc8; decide
    rw [hbv, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hlt : ((v ||| 1#64).clz ^^^ 0x3f#64).toNat < 64 := by
      have hle : (v ||| 1#64).clz ≤ 63#64 := ProofLib.clz_or_one_le v
      have : ((v ||| 1#64).clz ^^^ 0x3f#64) < 64#64 := by bv_bits
      exact this
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    have hm1 : ((v ||| 1#64).clz ^^^ 0x3f#64).toNat * 9 % 2 ^ 64 =
        ((v ||| 1#64).clz ^^^ 0x3f#64).toNat * 9 := Nat.mod_eq_of_lt (by omega)
    rw [hm1, Nat.mod_eq_of_lt (by omega)]
  have h3 := congrArg BitVec.toNat h1
  rw [h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h3
  exact h3.symm

@[local simp, local arm64_norm]
theorem ofNat_countLeadingZeros_64 (x : BitVec 64) :
    BitVec.ofNat 64 (countLeadingZeros x) = x.clz :=
  countLeadingZeros_loop_eq_clzAuxRec x 63

@[local simp, local arm64_norm]
theorem ofNat_countLeadingZeros_32 (x : BitVec 32) :
    BitVec.ofNat 32 (countLeadingZeros x) = x.clz :=
  countLeadingZeros_loop_eq_clzAuxRec x 31

@[local simp, local arm64_norm]
theorem truncate32_ofNat64 (n : Nat) :
    BitVec.truncate 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp

@[local simp, local arm64_norm]
theorem truncate32_zext64_lsr6 (x : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 x >>> 6) = x >>> 6 := by
  bv_bits

open Lean Elab Tactic in
/-- Fetch instructions in the range `[kStart, kEnd)` (byte offsets from function start `off`). -/
elab "tripleRatchetProgAt_fetches_range " b:term:max H:term:max hfn:term:max
    off:term:max kStart:num kEnd:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "fetches"
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let dec := mkIdent (`CryptoVerification.LibsignalTripleRatchet.Prost |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

/-- Close a `CalleeSavedPreserved s0 sf` goal after straight-line execution. -/
macro "encodedLen_cc_close" : tactic => `(tactic| (
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, applyWriteback,
    State.advancePC_eq_setPC, State.setPC_setPC, State.writeReg64_setPC, State.setPState_setPC,
    State.setPState_setPState, State.writeReg64_setPState, State.setMem_setPC, State.setMem_setMem,
    State.writeReg64_setMem, State.setPState_setMem, State.writeReg64_writeReg64_same,
    arm64_norm, *]
  done))

/-! ## Field layout decomposition for `wireSignalMessageAt` -/

/-- First 64-bit word of `optVecU8At`: `noneCap` when `none`, `pin.cap` when `some`. -/
def optVecCap (pin : VecPin) : Option (List (BitVec 8)) → BitVec 64
  | none => noneCap
  | some _ => pin.cap

/-- The heap buffer of a `Vec<u8>` (capacity `cap`, pointer `ptr`, bytes `bs`), detached from its
24-byte `vecHeader`. -/
def vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_header_sep_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs = vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8At vecU8Buf
  ac_rfl

/-- Remaining 16 header bytes + heap buffer of `optVecU8At`. -/
def optVecPayload (A : RustAlloc) (pin : VecPin) (p : BitVec 64) :
    Option (List (BitVec 8)) → SepProp
  | none => memRegion (p + 8#64) 16
  | some bs =>
    ((p + 8#64) ↦₆₄ pin.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A pin.cap pin.ptr bs

theorem optVecU8At_eq (A : RustAlloc) (pin : VecPin) (p : BitVec 64)
    (opt : Option (List (BitVec 8))) :
    optVecU8At A pin p opt = (p ↦₆₄ optVecCap pin opt) ∗ optVecPayload A pin p opt := by
  cases opt with
  | none => rfl
  | some bs =>
    simp only [optVecU8At, optVecCap, optVecPayload, vecU8At_eq_header_sep_buf, vecHeader, sepConj_assoc]

/-- First 32-bit word of `optU32At`: `0#32` when `none`, `1#32` when `some`. -/
def optU32Tag : Option (BitVec 32) → BitVec 32
  | none => 0#32
  | some _ => 1#32

/-- Second 32-bit word of `optU32At`. -/
def optU32Payload (p : BitVec 64) : Option (BitVec 32) → SepProp
  | none => memRegion (p + 4#64) 4
  | some v => (p + 4#64) ↦₃₂ v

theorem optU32At_eq (p : BitVec 64) (opt : Option (BitVec 32)) :
    optU32At p opt = (p ↦₃₂ optU32Tag opt) ∗ optU32Payload p opt := by
  cases opt <;> rfl

theorem vecU8Buf_cap_lt {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hm : m ⊨ vecU8Buf A cap ptr bs ∗ R) :
    cap.toNat < 2 ^ 63 := by
  unfold vecU8Buf at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact hm.1.2.1

theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1
  omega

theorem cap_add_one_bne_zero_true {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 != 0#64) = true := by
  simp [bne, cap_add_one_beq_zero_false h]

theorem optVecCap_bounds {A : RustAlloc} {pin : VecPin} {p : BitVec 64}
    {opt : Option (List (BitVec 8))} {R : SepProp} {m : Memory}
    (hm : m ⊨ optVecPayload A pin p opt ∗ R) :
    (optVecCap pin opt + 1#64 == 0#64) = !opt.isSome ∧
      (optVecCap pin opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none =>
    dsimp [optVecCap]
    exact ⟨rfl, rfl⟩
  | some bs =>
    simp only [optVecPayload] at hm
    have hhm : m ⊨ vecU8Buf A pin.cap pin.ptr bs ∗
        (((p + 8#64) ↦₆₄ pin.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ R) := by
      convert hm using 1; ac_rfl
    have hlt := vecU8Buf_cap_lt hhm
    exact ⟨cap_add_one_beq_zero_false hlt, cap_add_one_bne_zero_true hlt⟩

@[local simp, local arm64_norm]
theorem noneCap_add_one_beq_zero : (noneCap + 1#64 == 0#64) = true := rfl

@[local simp, local arm64_norm]
theorem noneCap_add_one_bne_zero : (noneCap + 1#64 != 0#64) = false := rfl

@[local simp, local arm64_norm]
theorem optU32Tag_beq_one (opt : Option (BitVec 32)) :
    (optU32Tag opt == 1#32) = opt.isSome := by
  cases opt <;> rfl

@[local simp, local arm64_norm]
theorem optU32Tag_bne_one (opt : Option (BitVec 32)) :
    (optU32Tag opt != 1#32) = !opt.isSome := by
  cases opt <;> rfl

@[local simp, local arm64_norm]
theorem zext64_optU32Tag_truncate32 (opt : Option (BitVec 32)) :
    (BitVec.zeroExtend 64 (optU32Tag opt)).truncate 32 = optU32Tag opt := by
  cases opt <;> rfl

/-! ## Field encoded-length arithmetic and non-overflow lemmas -/

theorem bv_encodeBytesField_some_length {t : Nat} {bs : List (BitVec 8)}
    (hkey : (encodeKey t .lengthDelimited).length = 1) :
    BitVec.ofNat 64 bs.length +
      BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 bs.length)).length + 1#64 =
      BitVec.ofNat 64 (encodeBytesField t (some bs)).length := by
  simp only [encodeBytesField, List.length_append, hkey, ← BitVec.ofNat_add]
  congr 1
  omega

@[local simp, local arm64_norm]
theorem hwVarintLen_w32_eq_encodeVarint_length (v : BitVec 32) :
    BitVec.zeroExtend 64
      (((((BitVec.zeroExtend 64 v ||| 1#64).clz.truncate 32 ^^^ 63#32) +
        (((BitVec.zeroExtend 64 v ||| 1#64).clz.truncate 32 ^^^ 63#32) <<< 3#32)) + 73#32)) >>> 6#64 =
      BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 v)).length := by
  rw [← hwVarintLen_bvShift_eq_encodeVarint_length]
  have hle : (BitVec.zeroExtend 64 v ||| 1#64).clz ≤ 63#64 := ProofLib.clz_or_one_le (BitVec.zeroExtend 64 v)
  generalize (BitVec.zeroExtend 64 v ||| 1#64).clz = c at hle ⊢
  have hc : c = (c.truncate 8).zeroExtend 64 := by bv_bits
  have hc8 : c.truncate 8 ≤ 63#8 := by bv_bits
  rw [hc]
  generalize c.truncate 8 = b at hc8 ⊢
  revert b hc8; decide

@[local simp, local arm64_norm]
theorem hwVarintLen_w32_natShift_eq_encodeVarint_length (v : BitVec 32) :
    BitVec.zeroExtend 64
      (((((BitVec.zeroExtend 64 v ||| 1#64).clz.truncate 32 ^^^ 0x3f#32) +
        (((BitVec.zeroExtend 64 v ||| 1#64).clz.truncate 32 ^^^ 0x3f#32) <<< 3)) + 0x49#32)) >>> 6 =
      BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 v)).length := by
  rw [← hwVarintLen_eq_encodeVarint_length]
  have hle : (BitVec.zeroExtend 64 v ||| 1#64).clz ≤ 63#64 := ProofLib.clz_or_one_le (BitVec.zeroExtend 64 v)
  generalize (BitVec.zeroExtend 64 v ||| 1#64).clz = c at hle ⊢
  have hc : c = (c.truncate 8).zeroExtend 64 := by bv_bits
  have hc8 : c.truncate 8 ≤ 63#8 := by bv_bits
  rw [hc]
  generalize c.truncate 8 = b at hc8 ⊢
  revert b hc8; decide

theorem bv_encodeUint32Field_some_length {t : Nat} {v : BitVec 32}
    (hkey : (encodeKey t .varint).length = 1) :
    BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 v)).length + 1#64 =
      BitVec.ofNat 64 (encodeUint32Field t (some v)).length := by
  simp only [encodeUint32Field, List.length_append, hkey, ← BitVec.ofNat_add, Nat.add_comm]

theorem bv_add_ofNat_comm (a b : Nat) :
    BitVec.ofNat 64 b + BitVec.ofNat 64 a = BitVec.ofNat 64 (a + b) := by
  rw [← BitVec.ofNat_add, Nat.add_comm]

theorem bv_add_ofNat_eq (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [← BitVec.ofNat_add]

@[local simp, local arm64_norm]
theorem ule_zero_64 (x : BitVec 64) : BitVec.ule 0#64 x = true := by
  bv_bits

@[local simp, local arm64_norm]
theorem ult_zero_64 (x : BitVec 64) : BitVec.ult x 0#64 = false := by
  bv_bits

theorem ule_ofNat_add_of_lt {a b : Nat} (h : a + b < 2 ^ 64) :
    BitVec.ule (BitVec.ofNat 64 b) (BitVec.ofNat 64 (a + b)) = true := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem ult_ofNat_add_of_lt {a b : Nat} (h : a + b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 (a + b)) (BitVec.ofNat 64 b) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## Unpacked message layout and per-field step lemmas for `encoded_len` (`0x28f50`) -/

def EncLenCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 .x19 = s0.readReg64 .x19 ∧
  s.readReg64 .x20 = s0.readReg64 .x20 ∧
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem EncLenCalleeSaved.trans {s0 s1 s2 : State}
    (h1 : EncLenCalleeSaved s0 s1) (h2 : EncLenCalleeSaved s1 s2) :
    EncLenCalleeSaved s0 s2 := by
  reg_chain

def wireMsgUnpacked (A : RustAlloc) (g : WireSignalMessageGhost) (a : BitVec 64)
    (m : ProtoSignalMessage) : SepProp :=
  (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
    ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
    ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
    ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
    ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
    ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter

theorem wireSignalMessageAt_eq_unpacked (A : RustAlloc) (g : WireSignalMessageGhost) (a : BitVec 64)
    (m : ProtoSignalMessage) :
    wireSignalMessageAt A g a m = wireMsgUnpacked A g a m := by
  unfold wireSignalMessageAt wireMsgUnpacked
  rw [optVecU8At_eq A g.rk a, optVecU8At_eq A g.ct (a + 24#64),
      optVecU8At_eq A g.pq (a + 48#64), optVecU8At_eq A g.addr (a + 72#64),
      optU32At_eq (a + 96#64), optU32At_eq (a + 104#64)]
  ac_rfl

/-- Prologue, tag 1 (`ratchetKey` at `x0 + 0x00`), and tag 2 test (`counter` at `x0 + 0x60`),
from `entry` to `entry + 64#64` (`+0x040`) or `entry + 184#64` (`+0x0b8`). -/
theorem step_encLen_f1 (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State))
    (g : WireSignalMessageGhost) (a sp v16 v8 : BitVec 64) (m : ProtoSignalMessage)
    (hrk_beq : (optVecCap g.rk m.ratchetKey + 1#64 == 0#64) = !m.ratchetKey.isSome)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodedLenName)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (wireMsgUnpacked A g a m ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.counter.isSome then
        (tripleRatchetProgAtExt b abs).fnAddr encodedLenName + 64#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodedLenName + 184#64) →
      sm.status = .Running →
      sm.sp = sp - 16#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (encodeBytesField 1 m.ratchetKey).length →
      EncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm
        ((wireMsgUnpacked A g a m ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  tripleRatchetProgAt_fetches_range b (Rust.withPanics abs)
    (ls_lemma% fnOff "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len") 167988 0 64
  tripleRatchetProgAt_fetches_range b (Rust.withPanics abs)
    (ls_lemma% fnOff "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len") 167988 168 184
  generalize_entry (tripleRatchetProgAtExt b abs).fnAddr encodedLenName = entry
  subst hP
  cases hrk : m.ratchetKey with
  | none =>
    have hP1 : wireMsgUnpacked A g a m =
        (a ↦₆₄ noneCap) ∗ optVecPayload A g.rk a none ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hrk, optVecCap]
    rw [hP1]
    apply SepWPp.of_sepWP (mid := if m.counter.isSome then entry + bv% (64) else entry + bv% (184))
    wp_steps
    apply SepWP.done (by cases m.counter <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases m.counter <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [encodeBytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    have hrk_beq' : (g.rk.cap + 1#64 == 0#64) = false := by
      rwa [hrk, Option.isSome_some, Bool.not_true, optVecCap] at hrk_beq
    have henc := bv_encodeBytesField_some_length (t := 1) (bs := bs) rfl
    have hP1 : wireMsgUnpacked A g a m =
        (a ↦₆₄ g.rk.cap) ∗ ((a + 8#64) ↦₆₄ g.rk.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A g.rk.cap g.rk.ptr bs ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hrk, optVecCap, optVecPayload, sepConj_assoc]
    rw [hP1]
    apply SepWPp.of_sepWP (mid := if m.counter.isSome then entry + bv% (64) else entry + bv% (184))
    wp_steps
    apply SepWP.done (by cases m.counter <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases m.counter <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

/-- Tag 2 (`counter` at `x0 + 0x60`) and tag 3 test (`previousCounter` at `x0 + 0x68`),
from `entry + 64#64` / `entry + 184#64` to `entry + 200#64` (`+0x0c8`) or `entry + 108#64` (`+0x06c`). -/
theorem step_encLen_f2 (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State))
    (g : WireSignalMessageGhost) (a : BitVec 64) (m : ProtoSignalMessage) (s1 : Nat)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.counter.isSome then
      (tripleRatchetProgAtExt b abs).fnAddr encodedLenName + 64#64
    else
      (tripleRatchetProgAtExt b abs).fnAddr encodedLenName + 184#64))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1)
    (hP : P = wireMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.previousCounter.isSome then
        (tripleRatchetProgAtExt b abs).fnAddr encodedLenName + 200#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodedLenName + 108#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1 + (encodeUint32Field 2 m.counter).length) →
      EncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  tripleRatchetProgAt_fetches_range b (Rust.withPanics abs)
    (ls_lemma% fnOff "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len") 167988 64 108
  tripleRatchetProgAt_fetches_range b (Rust.withPanics abs)
    (ls_lemma% fnOff "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len") 167988 184 200
  generalize_entry (tripleRatchetProgAtExt b abs).fnAddr encodedLenName = entry
  subst hP
  cases hcnt : m.counter with
  | none =>
    simp only [hcnt, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    have hP2 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 96#64) none ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hcnt]
    rw [hP2]
    apply SepWPp.of_sepWP (mid := if m.previousCounter.isSome then entry + bv% (200) else entry + bv% (108))
    wp_steps
    apply SepWP.done (by cases m.previousCounter <;> simp_all) (by simp_all)
    rw [← hP2]
    exact hnext _ (by cases m.previousCounter <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [encodeUint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    simp only [hcnt, Option.isSome_some, ↓reduceIte] at hpc
    have henc := bv_encodeUint32Field_some_length (t := 2) (v := v) rfl
    have hadd := bv_add_ofNat_comm s1 (encodeUint32Field 2 (some v)).length
    have hP2 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ 1#32) ∗ ((a + 100#64) ↦₃₂ v) ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hcnt, optU32Tag, optU32Payload, arm64_norm]
    rw [hP2]
    apply SepWPp.of_sepWP (mid := if m.previousCounter.isSome then entry + bv% (200) else entry + bv% (108))
    wp_steps
    apply SepWP.done (by cases m.previousCounter <;> simp_all) (by simp_all)
    rw [← hP2]
    exact hnext _ (by cases m.previousCounter <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

/-- Tag 3 (`previousCounter` at `x0 + 0x68`) and tag 4 test (`ciphertext` at `x0 + 0x18`),
from `entry + 200#64` / `entry + 108#64` to `entry + 124#64` (`+0x07c`) or `entry + 248#64` (`+0x0f8`). -/
theorem step_encLen_f3 (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State))
    (g : WireSignalMessageGhost) (a : BitVec 64) (m : ProtoSignalMessage) (s12 : Nat)
    (hct_beq : (optVecCap g.ct m.ciphertext + 1#64 == 0#64) = !m.ciphertext.isSome)
    (hct_bne : (optVecCap g.ct m.ciphertext + 1#64 != 0#64) = m.ciphertext.isSome)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.previousCounter.isSome then
      (tripleRatchetProgAtExt b abs).fnAddr encodedLenName + 200#64
    else
      (tripleRatchetProgAtExt b abs).fnAddr encodedLenName + 108#64))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12)
    (hP : P = wireMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.ciphertext.isSome then
        (tripleRatchetProgAtExt b abs).fnAddr encodedLenName + 124#64
      else
        (tripleRatchetProgAtExt b abs).fnAddr encodedLenName + 248#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s12 + (encodeUint32Field 3 m.previousCounter).length) →
      EncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  tripleRatchetProgAt_fetches_range b (Rust.withPanics abs)
    (ls_lemma% fnOff "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len") 167988 108 124
  tripleRatchetProgAt_fetches_range b (Rust.withPanics abs)
    (ls_lemma% fnOff "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len") 167988 200 248
  generalize_entry (tripleRatchetProgAtExt b abs).fnAddr encodedLenName = entry
  subst hP
  cases hprev : m.previousCounter with
  | none =>
    simp only [hprev, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    have hP3 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 104#64) none := by
      simp only [wireMsgUnpacked, hprev]
    rw [hP3]
    apply SepWPp.of_sepWP (mid := if m.ciphertext.isSome then entry + bv% (124) else entry + bv% (248))
    wp_steps
    apply SepWP.done (by cases m.ciphertext <;> simp_all) (by simp_all)
    rw [← hP3]
    exact hnext _ (by cases m.ciphertext <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [encodeUint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    simp only [hprev, Option.isSome_some, ↓reduceIte] at hpc
    have henc := bv_encodeUint32Field_some_length (t := 3) (v := v) rfl
    have hadd := bv_add_ofNat_eq s12 (encodeUint32Field 3 (some v)).length
    have hP3 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ 1#32) ∗ ((a + 108#64) ↦₃₂ v) := by
      simp only [wireMsgUnpacked, hprev, optU32Tag, optU32Payload, arm64_norm]
    rw [hP3]
    apply SepWPp.of_sepWP (mid := if m.ciphertext.isSome then entry + bv% (124) else entry + bv% (248))
    wp_steps
    apply SepWP.done (by cases m.ciphertext <;> simp_all) (by simp_all)
    rw [← hP3]
    exact hnext _ (by cases m.ciphertext <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

/-- Tag 4 (`ciphertext` at `x0 + 0x18`), from `entry + 124#64` / `entry + 248#64`
to `entry + 256#64` (`+0x100`). -/
theorem step_encLen_f4 (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State))
    (g : WireSignalMessageGhost) (a : BitVec 64) (m : ProtoSignalMessage) (s123 : Nat)
    (hfit : s123 + (encodeBytesField 4 m.ciphertext).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.ciphertext.isSome then
      (tripleRatchetProgAtExt b abs).fnAddr encodedLenName + 124#64
    else
      (tripleRatchetProgAtExt b abs).fnAddr encodedLenName + 248#64))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s123)
    (hP : P = wireMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b abs).fnAddr encodedLenName + 256#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s123 + (encodeBytesField 4 m.ciphertext).length) →
      EncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  tripleRatchetProgAt_fetches_range b (Rust.withPanics abs)
    (ls_lemma% fnOff "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len") 167988 124 164
  tripleRatchetProgAt_fetches_range b (Rust.withPanics abs)
    (ls_lemma% fnOff "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len") 167988 248 256
  generalize_entry (tripleRatchetProgAtExt b abs).fnAddr encodedLenName = entry
  subst hP
  cases hct : m.ciphertext with
  | none =>
    simp only [hct, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP (mid := entry + bv% (256))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [encodeBytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    simp only [hct, Option.isSome_some, ↓reduceIte] at hpc
    rw [hct] at hfit
    have henc := bv_encodeBytesField_some_length (t := 4) (bs := bs) rfl
    have hcc := ule_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s123 (encodeBytesField 4 (some bs)).length
    have hP4 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ g.ct.cap) ∗ ((a + 32#64) ↦₆₄ g.ct.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.ct.cap g.ct.ptr bs ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hct, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP4]
    apply SepWPp.of_sepWP (mid := entry + bv% (256))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP4]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

/-- Tag 5 (`pqRatchet` at `x0 + 0x30`), from `entry + 256#64` (`+0x100`)
to `entry + 320#64` (`+0x140`). -/
theorem step_encLen_f5 (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State))
    (g : WireSignalMessageGhost) (a : BitVec 64) (m : ProtoSignalMessage) (s1234 : Nat)
    (hpq_beq : (optVecCap g.pq m.pqRatchet + 1#64 == 0#64) = !m.pqRatchet.isSome)
    (hfit : s1234 + (encodeBytesField 5 m.pqRatchet).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodedLenName + 256#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1234)
    (hP : P = wireMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b abs).fnAddr encodedLenName + 320#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1234 + (encodeBytesField 5 m.pqRatchet).length) →
      EncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  tripleRatchetProgAt_fetches_range b (Rust.withPanics abs)
    (ls_lemma% fnOff "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len") 167988 256 308
  tripleRatchetProgAt_fetches_range b (Rust.withPanics abs)
    (ls_lemma% fnOff "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len") 167988 312 320
  generalize_entry (tripleRatchetProgAtExt b abs).fnAddr encodedLenName = entry
  subst hP
  cases hpq : m.pqRatchet with
  | none =>
    have hP5 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ noneCap) ∗ optVecPayload A g.pq (a + 48#64) none ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hpq, optVecCap]
    rw [hP5]
    apply SepWPp.of_sepWP (mid := entry + bv% (320))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP5]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [encodeBytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    have hpq_beq' : (g.pq.cap + 1#64 == 0#64) = false := by
      rwa [hpq, Option.isSome_some, Bool.not_true, optVecCap] at hpq_beq
    rw [hpq] at hfit
    have henc := bv_encodeBytesField_some_length (t := 5) (bs := bs) rfl
    have hcc := ule_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1234 (encodeBytesField 5 (some bs)).length
    have hP5 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ g.pq.cap) ∗ ((a + 56#64) ↦₆₄ g.pq.ptr) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.pq.cap g.pq.ptr bs ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hpq, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP5]
    apply SepWPp.of_sepWP (mid := entry + bv% (320))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP5]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

/-- Tag 6 (`addresses` at `x0 + 0x48`) and epilogue (`ldp x29, x30, [sp], #0x10; ret`),
from `entry + 320#64` (`+0x140`) to `s0.readReg64 .lr`. -/
theorem step_encLen_f6 (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State))
    (g : WireSignalMessageGhost) (a sp : BitVec 64) (m : ProtoSignalMessage) (s12345 : Nat)
    (haddr_beq : (optVecCap g.addr m.addresses + 1#64 == 0#64) = !m.addresses.isSome)
    (hfit : s12345 + (encodeBytesField 6 m.addresses).length < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b abs).fnAddr encodedLenName + 320#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12345)
    (hcs : EncLenCalleeSaved s0 s)
    (hP : P = (wireMsgUnpacked A g a m ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (s12345 + (encodeBytesField 6 m.addresses).length) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  tripleRatchetProgAt_fetches_range b (Rust.withPanics abs)
    (ls_lemma% fnOff "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len") 167988 320 388
  generalize_entry (tripleRatchetProgAtExt b abs).fnAddr encodedLenName = entry
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hvregs⟩
  subst hP
  cases haddr : m.addresses with
  | none =>
    have hP6 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ noneCap) ∗ optVecPayload A g.addr (a + 72#64) none ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, haddr, optVecCap]
    rw [hP6]
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP6]
    apply SepWPp.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [encodeBytesField]) (by encodedLen_cc_close)
  | some bs =>
    have haddr_beq' : (g.addr.cap + 1#64 == 0#64) = false := by
      rwa [haddr, Option.isSome_some, Bool.not_true, optVecCap] at haddr_beq
    rw [haddr] at hfit
    have henc := bv_encodeBytesField_some_length (t := 6) (bs := bs) rfl
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s12345 (encodeBytesField 6 (some bs)).length
    have hP6 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ g.addr.cap) ∗ ((a + 80#64) ↦₆₄ g.addr.ptr) ∗
        ((a + 88#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.addr.cap g.addr.ptr bs ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, haddr, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP6]
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP6]
    apply SepWPp.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by encodedLen_cc_close)

/-! ## Top-level `encodedLen_ok_ext` and `encodedLen_ok` theorems -/

theorem encode_length_eq (m : ProtoSignalMessage) :
    (LibsignalProtoCodec.encode m).length =
      (encodeBytesField 1 m.ratchetKey).length +
      (encodeUint32Field 2 m.counter).length +
      (encodeUint32Field 3 m.previousCounter).length +
      (encodeBytesField 4 m.ciphertext).length +
      (encodeBytesField 5 m.pqRatchet).length +
      (encodeBytesField 6 m.addresses).length := by
  simp only [LibsignalProtoCodec.encode, List.length_append]

theorem stackAt_encodedLen_eq (sp : BitVec 64) :
    stackAt sp encodedLenStack = ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) := by
  simp only [stackAt, encodedLenStack]
  change memRegion (sp - 16#64) (8 * 2) = _
  rw [memRegion_cells (sp - 16#64) 2 (by decide)]
  cells_unfold

theorem wireMsgUnpacked_bounds {A : RustAlloc} {g : WireSignalMessageGhost} {a : BitVec 64}
    {m : ProtoSignalMessage} {R : SepProp} {mem : Memory}
    (hm : mem ⊨ wireMsgUnpacked A g a m ∗ R) :
    (optVecCap g.rk m.ratchetKey + 1#64 == 0#64) = !m.ratchetKey.isSome ∧
    (optVecCap g.ct m.ciphertext + 1#64 == 0#64) = !m.ciphertext.isSome ∧
    (optVecCap g.ct m.ciphertext + 1#64 != 0#64) = m.ciphertext.isSome ∧
    (optVecCap g.pq m.pqRatchet + 1#64 == 0#64) = !m.pqRatchet.isSome ∧
    (optVecCap g.addr m.addresses + 1#64 == 0#64) = !m.addresses.isSome := by
  unfold wireMsgUnpacked at hm
  have hrk : (optVecCap g.rk m.ratchetKey + 1#64 == 0#64) = !m.ratchetKey.isSome ∧
      (optVecCap g.rk m.ratchetKey + 1#64 != 0#64) = m.ratchetKey.isSome := by
    refine optVecCap_bounds (A := A) (pin := g.rk) (p := a) (opt := m.ratchetKey) (m := mem)
      (R := ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter ∗
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ R) ?_
    convert hm using 1; ac_rfl
  have hct : (optVecCap g.ct m.ciphertext + 1#64 == 0#64) = !m.ciphertext.isSome ∧
      (optVecCap g.ct m.ciphertext + 1#64 != 0#64) = m.ciphertext.isSome := by
    refine optVecCap_bounds (A := A) (pin := g.ct) (p := a + 24#64) (opt := m.ciphertext) (m := mem)
      (R := (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ R) ?_
    convert hm using 1; ac_rfl
  have hpq : (optVecCap g.pq m.pqRatchet + 1#64 == 0#64) = !m.pqRatchet.isSome ∧
      (optVecCap g.pq m.pqRatchet + 1#64 != 0#64) = m.pqRatchet.isSome := by
    refine optVecCap_bounds (A := A) (pin := g.pq) (p := a + 48#64) (opt := m.pqRatchet) (m := mem)
      (R := (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ R) ?_
    convert hm using 1; ac_rfl
  have haddr : (optVecCap g.addr m.addresses + 1#64 == 0#64) = !m.addresses.isSome ∧
      (optVecCap g.addr m.addresses + 1#64 != 0#64) = m.addresses.isSome := by
    refine optVecCap_bounds (A := A) (pin := g.addr) (p := a + 72#64) (opt := m.addresses) (m := mem)
      (R := (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ R) ?_
    convert hm using 1; ac_rfl
  exact ⟨hrk.1, hct.1, hct.2, hpq.1, haddr.1⟩

/-- `<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len`
(`0x28f50`, 100 instructions) meets `encodedLenSpec A` on `tripleRatchetProgAtExt b ext`. -/
theorem encodedLen_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) :
    EncodedLenOkExt b A ext := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, m⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [encodedLenSpec, wireSignalMessageAt_eq_unpacked, stackAt_encodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, ⟨hx0, hfit⟩, hpre⟩
  unfold WireLengthsFit at hfit
  rw [encode_length_eq] at hfit
  have hmem0 : s0.mem ⊨
      (wireMsgUnpacked A g a m ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R := by
    convert hpre using 1; ac_rfl
  have hmem0' : s0.mem ⊨
      wireMsgUnpacked A g a m ∗ (((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R) :=
    hpre
  obtain ⟨hrk_beq, hct_beq, hct_bne, hpq_beq, haddr_beq⟩ := wireMsgUnpacked_bounds hmem0'
  refine ⟨(wireMsgUnpacked A g a m ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R, emp,
      by rwa [sepConj_emp], ?_⟩
  refine step_encLen_f1 (F := R) b A ext g a s0.sp v16 v8 m hrk_beq
    hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr) ∗ R
  have hP_save :
      (wireMsgUnpacked A g a m ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ R =
      wireMsgUnpacked A g a m ∗ FSave := by
    dsimp [FSave]; ac_rfl
  refine step_encLen_f2 (F := FSave) b A ext g a m
    (encodeBytesField 1 m.ratchetKey).length
    hpc1 hrun1 hx0_1 hx8_1 hP_save ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
  refine step_encLen_f3 (F := FSave) b A ext g a m
    ((encodeBytesField 1 m.ratchetKey).length + (encodeUint32Field 2 m.counter).length)
    hct_beq hct_bne
    hpc2 hrun2 hx0_2 hx8_2 hP_save ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
  refine step_encLen_f4 (F := FSave) b A ext g a m
    ((encodeBytesField 1 m.ratchetKey).length + (encodeUint32Field 2 m.counter).length +
      (encodeUint32Field 3 m.previousCounter).length)
    (by omega) hpc3 hrun3 hx0_3 hx8_3 hP_save ?_
  intro s4 hpc4 hrun4 hsp4 htr4 hx0_4 hx8_4 hcs4
  refine step_encLen_f5 (F := FSave) b A ext g a m
    ((encodeBytesField 1 m.ratchetKey).length + (encodeUint32Field 2 m.counter).length +
      (encodeUint32Field 3 m.previousCounter).length + (encodeBytesField 4 m.ciphertext).length)
    hpq_beq (by omega) hpc4 hrun4 hx0_4 hx8_4 hP_save ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx8_5 hcs5
  have hsp5' : s5.sp = s0.sp - 16#64 := by rw [hsp5, hsp4, hsp3, hsp2, hsp1]
  have hcs5' : EncLenCalleeSaved s0 s5 :=
    hcs1.trans (hcs2.trans (hcs3.trans (hcs4.trans hcs5)))
  refine step_encLen_f6 (F := R) b A ext g a s0.sp m
    ((encodeBytesField 1 m.ratchetKey).length + (encodeUint32Field 2 m.counter).length +
      (encodeUint32Field 3 m.previousCounter).length + (encodeBytesField 4 m.ciphertext).length +
      (encodeBytesField 5 m.pqRatchet).length)
    haddr_beq (by omega) hpc5 hrun5 hsp5' halign hx0_5 hx8_5 hcs5' rfl ?_
  intro sf hpcf hrunf hspf htrf hx0_f hcsf
  have htr_all : sf.trace = s0.trace := by reg_chain
  rw [← encode_length_eq] at hx0_f
  refine ⟨?_, hspf, hcsf⟩
  intro hm_f
  rw [sepConj_emp] at hm_f
  simp only [encodedLenSpec, wireSignalMessageAt_eq_unpacked, stackAt_encodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, htr_all⟩, ?_⟩
  convert hm_f using 1
  ac_rfl

/-- `<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len`
(`0x28f50`, 100 instructions) meets `encodedLenSpec A`. -/
theorem encodedLen_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    EncodedLenOk b C A ctl abs :=
  encodedLen_ok_ext b A (tripleRatchetExterns C ctl abs)

/-! ## Relocatable per-block contract (block 108) -/

private theorem step_encLen_f1_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (g : WireSignalMessageGhost) (a sp v16 v8 : BitVec 64) (m : ProtoSignalMessage)
    (hrk_beq : (optVecCap g.rk m.ratchetKey + 1#64 == 0#64) = !m.ratchetKey.isSome)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_108).base)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (wireMsgUnpacked A g a m ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.counter.isSome then (blkPl_108).base + 64#64 else (blkPl_108).base + 184#64) →
      sm.status = .Running →
      sm.sp = sp - 16#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (encodeBytesField 1 m.ratchetKey).length →
      EncLenCalleeSaved s sm →
      SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret sm
        ((wireMsgUnpacked A g a m ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret s P Q Qp := by
  subst hP
  cases hrk : m.ratchetKey with
  | none =>
    have hP1 : wireMsgUnpacked A g a m =
        (a ↦₆₄ noneCap) ∗ optVecPayload A g.rk a none ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hrk, optVecCap]
    rw [hP1]
    apply SepWPp.of_sepWP (mid := if m.counter.isSome then (blkPl_108).base + 64#64 else (blkPl_108).base + 184#64)
    wp_steps
    apply SepWP.done (by cases m.counter <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases m.counter <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [encodeBytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    have hrk_beq' : (g.rk.cap + 1#64 == 0#64) = false := by
      rwa [hrk, Option.isSome_some, Bool.not_true, optVecCap] at hrk_beq
    have henc := bv_encodeBytesField_some_length (t := 1) (bs := bs) rfl
    have hP1 : wireMsgUnpacked A g a m =
        (a ↦₆₄ g.rk.cap) ∗ ((a + 8#64) ↦₆₄ g.rk.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A g.rk.cap g.rk.ptr bs ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hrk, optVecCap, optVecPayload, sepConj_assoc]
    rw [hP1]
    apply SepWPp.of_sepWP (mid := if m.counter.isSome then (blkPl_108).base + 64#64 else (blkPl_108).base + 184#64)
    wp_steps
    apply SepWP.done (by cases m.counter <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases m.counter <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

private theorem step_encLen_f2_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (g : WireSignalMessageGhost) (a : BitVec 64) (m : ProtoSignalMessage) (s1 : Nat)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.counter.isSome then (blkPl_108).base + 64#64 else (blkPl_108).base + 184#64))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1)
    (hP : P = wireMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.previousCounter.isSome then (blkPl_108).base + 200#64 else (blkPl_108).base + 108#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1 + (encodeUint32Field 2 m.counter).length) →
      EncLenCalleeSaved s sm →
      SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret sm P Q Qp) :
    SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret s P Q Qp := by
  subst hP
  cases hcnt : m.counter with
  | none =>
    simp only [hcnt, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    have hP2 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 96#64) none ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hcnt]
    rw [hP2]
    apply SepWPp.of_sepWP (mid := if m.previousCounter.isSome then (blkPl_108).base + 200#64 else (blkPl_108).base + 108#64)
    wp_steps
    apply SepWP.done (by cases m.previousCounter <;> simp_all) (by simp_all)
    rw [← hP2]
    exact hnext _ (by cases m.previousCounter <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [encodeUint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    simp only [hcnt, Option.isSome_some, ↓reduceIte] at hpc
    have henc := bv_encodeUint32Field_some_length (t := 2) (v := v) rfl
    have hadd := bv_add_ofNat_comm s1 (encodeUint32Field 2 (some v)).length
    have hP2 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ 1#32) ∗ ((a + 100#64) ↦₃₂ v) ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hcnt, optU32Tag, optU32Payload, arm64_norm]
    rw [hP2]
    apply SepWPp.of_sepWP (mid := if m.previousCounter.isSome then (blkPl_108).base + 200#64 else (blkPl_108).base + 108#64)
    wp_steps
    apply SepWP.done (by cases m.previousCounter <;> simp_all) (by simp_all)
    rw [← hP2]
    exact hnext _ (by cases m.previousCounter <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

private theorem step_encLen_f3_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (g : WireSignalMessageGhost) (a : BitVec 64) (m : ProtoSignalMessage) (s12 : Nat)
    (hct_beq : (optVecCap g.ct m.ciphertext + 1#64 == 0#64) = !m.ciphertext.isSome)
    (hct_bne : (optVecCap g.ct m.ciphertext + 1#64 != 0#64) = m.ciphertext.isSome)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.previousCounter.isSome then (blkPl_108).base + 200#64 else (blkPl_108).base + 108#64))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12)
    (hP : P = wireMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.ciphertext.isSome then (blkPl_108).base + 124#64 else (blkPl_108).base + 248#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s12 + (encodeUint32Field 3 m.previousCounter).length) →
      EncLenCalleeSaved s sm →
      SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret sm P Q Qp) :
    SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret s P Q Qp := by
  subst hP
  cases hprev : m.previousCounter with
  | none =>
    simp only [hprev, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    have hP3 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 104#64) none := by
      simp only [wireMsgUnpacked, hprev]
    rw [hP3]
    apply SepWPp.of_sepWP (mid := if m.ciphertext.isSome then (blkPl_108).base + 124#64 else (blkPl_108).base + 248#64)
    wp_steps
    apply SepWP.done (by cases m.ciphertext <;> simp_all) (by simp_all)
    rw [← hP3]
    exact hnext _ (by cases m.ciphertext <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [encodeUint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    simp only [hprev, Option.isSome_some, ↓reduceIte] at hpc
    have henc := bv_encodeUint32Field_some_length (t := 3) (v := v) rfl
    have hadd := bv_add_ofNat_eq s12 (encodeUint32Field 3 (some v)).length
    have hP3 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ 1#32) ∗ ((a + 108#64) ↦₃₂ v) := by
      simp only [wireMsgUnpacked, hprev, optU32Tag, optU32Payload, arm64_norm]
    rw [hP3]
    apply SepWPp.of_sepWP (mid := if m.ciphertext.isSome then (blkPl_108).base + 124#64 else (blkPl_108).base + 248#64)
    wp_steps
    apply SepWP.done (by cases m.ciphertext <;> simp_all) (by simp_all)
    rw [← hP3]
    exact hnext _ (by cases m.ciphertext <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

private theorem step_encLen_f4_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (g : WireSignalMessageGhost) (a : BitVec 64) (m : ProtoSignalMessage) (s123 : Nat)
    (hfit : s123 + (encodeBytesField 4 m.ciphertext).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.ciphertext.isSome then (blkPl_108).base + 124#64 else (blkPl_108).base + 248#64))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s123)
    (hP : P = wireMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_108).base + 256#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s123 + (encodeBytesField 4 m.ciphertext).length) →
      EncLenCalleeSaved s sm →
      SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret sm P Q Qp) :
    SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret s P Q Qp := by
  subst hP
  cases hct : m.ciphertext with
  | none =>
    simp only [hct, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP (mid := (blkPl_108).base + 256#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [encodeBytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    simp only [hct, Option.isSome_some, ↓reduceIte] at hpc
    rw [hct] at hfit
    have henc := bv_encodeBytesField_some_length (t := 4) (bs := bs) rfl
    have hcc := ule_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s123 (encodeBytesField 4 (some bs)).length
    have hP4 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ g.ct.cap) ∗ ((a + 32#64) ↦₆₄ g.ct.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.ct.cap g.ct.ptr bs ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hct, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP4]
    apply SepWPp.of_sepWP (mid := (blkPl_108).base + 256#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP4]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

private theorem step_encLen_f5_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (g : WireSignalMessageGhost) (a : BitVec 64) (m : ProtoSignalMessage) (s1234 : Nat)
    (hpq_beq : (optVecCap g.pq m.pqRatchet + 1#64 == 0#64) = !m.pqRatchet.isSome)
    (hfit : s1234 + (encodeBytesField 5 m.pqRatchet).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_108).base + 256#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1234)
    (hP : P = wireMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_108).base + 320#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1234 + (encodeBytesField 5 m.pqRatchet).length) →
      EncLenCalleeSaved s sm →
      SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret sm P Q Qp) :
    SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret s P Q Qp := by
  subst hP
  cases hpq : m.pqRatchet with
  | none =>
    have hP5 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ noneCap) ∗ optVecPayload A g.pq (a + 48#64) none ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hpq, optVecCap]
    rw [hP5]
    apply SepWPp.of_sepWP (mid := (blkPl_108).base + 320#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP5]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [encodeBytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    have hpq_beq' : (g.pq.cap + 1#64 == 0#64) = false := by
      rwa [hpq, Option.isSome_some, Bool.not_true, optVecCap] at hpq_beq
    rw [hpq] at hfit
    have henc := bv_encodeBytesField_some_length (t := 5) (bs := bs) rfl
    have hcc := ule_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1234 (encodeBytesField 5 (some bs)).length
    have hP5 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ g.pq.cap) ∗ ((a + 56#64) ↦₆₄ g.pq.ptr) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.pq.cap g.pq.ptr bs ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hpq, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP5]
    apply SepWPp.of_sepWP (mid := (blkPl_108).base + 320#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP5]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

private theorem step_encLen_f6_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (g : WireSignalMessageGhost) (a sp : BitVec 64) (m : ProtoSignalMessage) (s12345 : Nat)
    (haddr_beq : (optVecCap g.addr m.addresses + 1#64 == 0#64) = !m.addresses.isSome)
    (hfit : s12345 + (encodeBytesField 6 m.addresses).length < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_108).base + 320#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12345)
    (hcs : EncLenCalleeSaved s0 s)
    (hP : P = (wireMsgUnpacked A g a m ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (s12345 + (encodeBytesField 6 m.addresses).length) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp ((blkPC_108).rebase (blkPl_108).base H) (s0.readReg64 .lr) s P Q Qp := by
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hvregs⟩
  subst hP
  cases haddr : m.addresses with
  | none =>
    have hP6 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ noneCap) ∗ optVecPayload A g.addr (a + 72#64) none ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, haddr, optVecCap]
    rw [hP6]
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP6]
    apply SepWPp.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [encodeBytesField]) (by encodedLen_cc_close)
  | some bs =>
    have haddr_beq' : (g.addr.cap + 1#64 == 0#64) = false := by
      rwa [haddr, Option.isSome_some, Bool.not_true, optVecCap] at haddr_beq
    rw [haddr] at hfit
    have henc := bv_encodeBytesField_some_length (t := 6) (bs := bs) rfl
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s12345 (encodeBytesField 6 (some bs)).length
    have hP6 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ g.addr.cap) ∗ ((a + 80#64) ↦₆₄ g.addr.ptr) ∗
        ((a + 88#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.addr.cap g.addr.ptr bs ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, haddr, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP6]
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP6]
    apply SepWPp.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by encodedLen_cc_close)

theorem encoded_len_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_108).rebase (blkPl_108).base H) (blkPl_108).base
      (encodedLenSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, m⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [encodedLenSpec, wireSignalMessageAt_eq_unpacked, stackAt_encodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, ⟨hx0, hfit⟩, hpre⟩
  unfold WireLengthsFit at hfit
  rw [encode_length_eq] at hfit
  have hmem0 : s0.mem ⊨
      (wireMsgUnpacked A g a m ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R := by
    convert hpre using 1; ac_rfl
  have hmem0' : s0.mem ⊨
      wireMsgUnpacked A g a m ∗ (((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R) :=
    hpre
  obtain ⟨hrk_beq, hct_beq, hct_bne, hpq_beq, haddr_beq⟩ := wireMsgUnpacked_bounds hmem0'
  refine ⟨(wireMsgUnpacked A g a m ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R, emp,
      by rwa [sepConj_emp], ?_⟩
  refine step_encLen_f1_placed (F := R) A H g a s0.sp v16 v8 m hrk_beq
    hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr) ∗ R
  have hP_save :
      (wireMsgUnpacked A g a m ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ R =
      wireMsgUnpacked A g a m ∗ FSave := by
    dsimp [FSave]; ac_rfl
  refine step_encLen_f2_placed (F := FSave) A H g a m
    (encodeBytesField 1 m.ratchetKey).length
    hpc1 hrun1 hx0_1 hx8_1 hP_save ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
  refine step_encLen_f3_placed (F := FSave) A H g a m
    ((encodeBytesField 1 m.ratchetKey).length + (encodeUint32Field 2 m.counter).length)
    hct_beq hct_bne
    hpc2 hrun2 hx0_2 hx8_2 hP_save ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
  refine step_encLen_f4_placed (F := FSave) A H g a m
    ((encodeBytesField 1 m.ratchetKey).length + (encodeUint32Field 2 m.counter).length +
      (encodeUint32Field 3 m.previousCounter).length)
    (by omega) hpc3 hrun3 hx0_3 hx8_3 hP_save ?_
  intro s4 hpc4 hrun4 hsp4 htr4 hx0_4 hx8_4 hcs4
  refine step_encLen_f5_placed (F := FSave) A H g a m
    ((encodeBytesField 1 m.ratchetKey).length + (encodeUint32Field 2 m.counter).length +
      (encodeUint32Field 3 m.previousCounter).length + (encodeBytesField 4 m.ciphertext).length)
    hpq_beq (by omega) hpc4 hrun4 hx0_4 hx8_4 hP_save ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx8_5 hcs5
  have hsp5' : s5.sp = s0.sp - 16#64 := by rw [hsp5, hsp4, hsp3, hsp2, hsp1]
  have hcs5' : EncLenCalleeSaved s0 s5 :=
    hcs1.trans (hcs2.trans (hcs3.trans (hcs4.trans hcs5)))
  refine step_encLen_f6_placed (F := R) A H g a s0.sp m
    ((encodeBytesField 1 m.ratchetKey).length + (encodeUint32Field 2 m.counter).length +
      (encodeUint32Field 3 m.previousCounter).length + (encodeBytesField 4 m.ciphertext).length +
      (encodeBytesField 5 m.pqRatchet).length)
    haddr_beq (by omega) hpc5 hrun5 hsp5' halign hx0_5 hx8_5 hcs5' rfl ?_
  intro sf hpcf hrunf hspf htrf hx0_f hcsf
  have htr_all : sf.trace = s0.trace := by reg_chain
  rw [← encode_length_eq] at hx0_f
  refine ⟨?_, hspf, hcsf⟩
  intro hm_f
  rw [sepConj_emp] at hm_f
  simp only [encodedLenSpec, wireSignalMessageAt_eq_unpacked, stackAt_encodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, htr_all⟩, ?_⟩
  convert hm_f using 1
  ac_rfl

end CryptoVerification.LibsignalTripleRatchet.Prost
