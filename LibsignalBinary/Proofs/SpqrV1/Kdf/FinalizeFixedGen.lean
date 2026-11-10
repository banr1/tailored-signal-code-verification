/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.GenDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon

/-!
# Generalized `Hmac<Sha256>::finalize_fixed [local#3]` (`0x6ce50`)

Proves `finalize_fixed3_gen_runsTo_ext` covering both the `< 56` one-block
padding branch (`0x6cea0 → 0x6ced4`) and the `[56, 64)` two-block padding branch
(`0x6cea0 → 0x6cea4 .. 0x6cf04`) for `pfx.length % 64 = 0` and `tail.length < 64`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.CodeLayout

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

@[simp, arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [0x67a58 → 0x67c14]

private theorem mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

/-! ## 1. Two-Block Inner Padding (`56 ≤ tail.length < 64`) and `hmacWith_pfx_two_blocks` -/

/-- First 64-byte inner padding block when `56 ≤ tail.length < 64`:
`tail ‖ 0x80 ‖ 0 × (63 - |tail|)`. -/
def innerPadBlock1 (tail : List (BitVec 8)) : List (BitVec 8) :=
  tail ++ [0x80#8] ++ List.replicate (63 - tail.length) 0#8

/-- Second 64-byte inner padding block when `56 ≤ tail.length < 64`:
`0 × 56 ‖ BE64(8 · (64 · nBlocks + |tail|))`. -/
def innerPadBlock2 (nBlocks : ℕ) (tail : List (BitVec 8)) : List (BitVec 8) :=
  List.replicate 56 0#8 ++ toBEBytes 8 (BitVec.ofNat 64 (8 * (64 * nBlocks + tail.length)))

theorem innerPadBlock1_length {tail : List (BitVec 8)} (hlt : tail.length < 64) :
    (innerPadBlock1 tail).length = 64 := by
  unfold innerPadBlock1
  simp
  omega

theorem innerPadBlock2_length (nBlocks : ℕ) (tail : List (BitVec 8)) :
    (innerPadBlock2 nBlocks tail).length = 64 := by
  unfold innerPadBlock2
  simp [toBEBytes]

@[local simp] private theorem chunks64_length (bs : List (BitVec 8)) :
    (chunks64 bs).length = bs.length / 64 := by
  simp [chunks64]

@[local simp] private theorem chunks64_getElem (bs : List (BitVec 8)) (i : ℕ)
    (hi : i < (chunks64 bs).length) :
    (chunks64 bs)[i] = (bs.drop (64 * i)).take 64 := by
  simp [chunks64]

private theorem chunks64_of_lt {bs : List (BitVec 8)} (h : bs.length < 64) :
    chunks64 bs = [] := by
  rw [← List.length_eq_zero_iff, chunks64_length]
  omega

private theorem chunks64_append_64 {a b : List (BitVec 8)} (ha : a.length = 64) :
    chunks64 (a ++ b) = a :: chunks64 b := by
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · simp [ha]
  · cases i with
    | zero =>
      simp [ha]
    | succ j =>
      simp only [chunks64_getElem, List.getElem_cons_succ]
      have hdrop : 64 * (j + 1) = a.length + 64 * j := by omega
      rw [hdrop, ← List.drop_drop, List.drop_left]

private theorem chunks64_single {a : List (BitVec 8)} (ha : a.length = 64) :
    chunks64 a = [a] := by
  conv_lhs => rw [← List.append_nil a]
  rw [chunks64_append_64 ha, chunks64_of_lt (by simp)]

private theorem chunks64_append_mul {a b : List (BitVec 8)} (ha : a.length % 64 = 0) :
    chunks64 (a ++ b) = chunks64 a ++ chunks64 b := by
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · simp; omega
  · rw [chunks64_getElem]
    by_cases hi : i < (chunks64 a).length
    · rw [List.getElem_append_left hi, chunks64_getElem]
      have hle : 64 * i + 64 ≤ a.length := by
        simp only [chunks64_length] at hi
        omega
      rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
    · rw [List.getElem_append_right (by omega), chunks64_getElem]
      simp only [chunks64_length] at hi ⊢
      have hdrop : 64 * i = a.length + 64 * (i - a.length / 64) := by omega
      rw [hdrop, ← List.drop_drop, List.drop_left]

private theorem bitlen_and_zero (b p : ℕ) (hp : p < 64) :
    ((BitVec.ofNat 64 b <<< 9) &&& (BitVec.ofNat 64 p <<< 3)) = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    hi, decide_true, Bool.true_and]
  by_cases h9 : i < 9
  · simp [h9]
  · have hpow : 2 ^ 6 ≤ 2 ^ (i - 3) := Nat.pow_le_pow_right (by decide) (by omega)
    have hlt : p < 2 ^ (i - 3) := by omega
    simp [Nat.testBit_lt_two_pow hlt]

theorem bit_len_innerN_eq_lt64 {b n : ℕ} (hn : n < 64) :
    (BitVec.ofNat 64 b <<< 9#64) ||| (BitVec.ofNat 64 n <<< 3#64) =
      BitVec.ofNat 64 (8 * (64 * b + n)) ∧
    (BitVec.ofNat 64 b <<< 9) ||| (BitVec.ofNat 64 n <<< 3) =
      BitVec.ofNat 64 (8 * (64 * b + n)) := by
  have h : (BitVec.ofNat 64 b <<< 9) ||| (BitVec.ofNat 64 n <<< 3) =
      BitVec.ofNat 64 (8 * (64 * b + n)) := by
    rw [← BitVec.add_eq_or_of_and_eq_zero _ _ (bitlen_and_zero b n hn),
      BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow]
    have hdiv : 8 * (64 * b + n) = b * 512 + n * 8 := by omega
    rw [hdiv, BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_mul]
    rfl
  exact ⟨h, h⟩

/-- HMAC with a 64-byte-aligned prefix `pfx` and two-block padded tail `tail` (`56 ≤ |tail| < 64`). -/
theorem hmacWith_pfx_two_blocks (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8))
    (hk : key.length ≤ 64) (hpfx : pfx.length % 64 = 0)
    (htail_ge : 56 ≤ tail.length) (htail_lt : tail.length < 64) :
    hmacWith F key (pfx ++ tail) =
      digestBytes (F (hmacOuterInit F key)
        (outerBlock (digestBytes (F (F ((chunks64 pfx).foldl F (hmacInnerInit F key))
          (innerPadBlock1 tail))
          (innerPadBlock2 (1 + pfx.length / 64) tail))))) := by
  unfold hmacWith
  have hk_not_gt : ¬ (64 < key.length) := by omega
  simp only [hk_not_gt, ↓reduceIte]
  set ipad := (hmacKeyBlock key).map (· ^^^ 0x36)
  set opad := (hmacKeyBlock key).map (· ^^^ 0x5c)
  change sha256With F (opad ++ sha256With F (ipad ++ (pfx ++ tail))) = _
  have hkb_len : (hmacKeyBlock key).length = 64 := by
    simp [hmacKeyBlock]; omega
  have hipad_len : ipad.length = 64 := by simp [ipad, hkb_len]
  have hopad_len : opad.length = 64 := by simp [opad, hkb_len]
  set nB := 1 + pfx.length / 64
  have hblk1_len : (innerPadBlock1 tail).length = 64 := innerPadBlock1_length htail_lt
  have hblk2_len : (innerPadBlock2 nB tail).length = 64 := innerPadBlock2_length nB tail
  have hinner_pad : sha256Pad (ipad ++ (pfx ++ tail)) =
      ipad ++ (pfx ++ (innerPadBlock1 tail ++ innerPadBlock2 nB tail)) := by
    unfold sha256Pad innerPadBlock1 innerPadBlock2
    have hlen : (ipad ++ (pfx ++ tail)).length = 64 * nB + tail.length := by
      simp [hipad_len, nB]; omega
    have hmod : (119 - (64 * nB + tail.length) % 64) % 64 = (63 - tail.length) + 56 := by omega
    rw [hlen, hmod, List.replicate_add]
    simp only [List.append_assoc]
    rfl
  have hinner : sha256With F (ipad ++ (pfx ++ tail)) =
      digestBytes (F (F ((chunks64 pfx).foldl F (hmacInnerInit F key))
        (innerPadBlock1 tail)) (innerPadBlock2 nB tail)) := by
    unfold sha256With digestBytes
    rw [hinner_pad, chunks64_append_64 hipad_len, chunks64_append_mul hpfx,
      chunks64_append_64 hblk1_len, chunks64_single hblk2_len,
      List.foldl_cons, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil]
    rfl
  rw [hinner]
  set d := digestBytes (F (F ((chunks64 pfx).foldl F (hmacInnerInit F key))
    (innerPadBlock1 tail)) (innerPadBlock2 nB tail))
  have hd_len : d.length = 32 := digestBytes_length _
  have houter_blk_len : (outerBlock d).length = 64 := by
    simp [outerBlock, hd_len]
  have houter_pad : sha256Pad (opad ++ d) = opad ++ outerBlock d := by
    unfold sha256Pad outerBlock
    have hlen : (opad ++ d).length = 96 := by
      simp [hopad_len, hd_len]
    rw [hlen]
    simp only [List.append_assoc]
  unfold sha256With digestBytes
  rw [houter_pad, chunks64_append_64 hopad_len, chunks64_single houter_blk_len]
  rfl

/-! ## 2. Memory and Arithmetic Helpers for `56 ≤ tail.length < 64` -/

theorem readBytes_64_after_pad_memset_lt64 (m : Memory) (hm : BitVec 64) (msg : List (BitVec 8))
    (hmsg : m.readBytes hm msg.length = msg) (hlt : msg.length < 64) :
    ((m.write8 (hm + BitVec.ofNat 64 msg.length) 0x80#8).writeBytes
      (hm + BitVec.ofNat 64 msg.length + 1#64) (List.replicate (63 - msg.length) 0#8)).readBytes hm 64 =
      msg ++ [0x80#8] ++ List.replicate (63 - msg.length) 0#8 := by
  have hw8 : m.write8 (hm + BitVec.ofNat 64 msg.length) 0x80#8 =
      m.writeBytes (hm + BitVec.ofNat 64 msg.length) [0x80#8] := rfl
  have h1 : hm + BitVec.ofNat 64 msg.length + 1#64 =
      (hm + BitVec.ofNat 64 msg.length) + BitVec.ofNat 64 ([0x80#8] : List (BitVec 8)).length := rfl
  rw [hw8, h1, ← Bytes.writeBytes_append]
  set pad := [0x80#8] ++ List.replicate (63 - msg.length) 0#8
  have hpad_len : pad.length = 64 - msg.length := by simp [pad]; omega
  have hsplit : (m.writeBytes (hm + BitVec.ofNat 64 msg.length) pad).readBytes hm 64 =
      (m.writeBytes (hm + BitVec.ofNat 64 msg.length) pad).readBytes hm msg.length ++
      (m.writeBytes (hm + BitVec.ofNat 64 msg.length) pad).readBytes
        (hm + BitVec.ofNat 64 msg.length) (64 - msg.length) := by
    rw [← Bytes.readBytes_add]
    congr 1
    omega
  rw [hsplit]
  have hleft : (m.writeBytes (hm + BitVec.ofNat 64 msg.length) pad).readBytes hm msg.length = msg := by
    by_cases h0 : msg.length = 0
    · simp [h0] at hmsg ⊢; exact hmsg
    · rw [Bytes.readBytes_writeBytes_disjoint m hm msg.length (hm + BitVec.ofNat 64 msg.length) pad]
      · exact hmsg
      · rw [hpad_len]; unfold DisjointRegions; bv_omega
  have hright : (m.writeBytes (hm + BitVec.ofNat 64 msg.length) pad).readBytes
      (hm + BitVec.ofNat 64 msg.length) (64 - msg.length) = pad := by
    rw [← hpad_len]
    exact Bytes.readBytes_writeBytes_same m _ pad (by omega)
  rw [hleft, hright]
  simp [pad, List.append_assoc]

theorem agreesOutside_pad_memset_lt64 (m : Memory) (hm : BitVec 64) (msg : List (BitVec 8))
    (hlt : msg.length < 64) :
    AgreesOutside m
      ((m.write8 (hm + BitVec.ofNat 64 msg.length) 0x80#8).writeBytes
        (hm + BitVec.ofNat 64 msg.length + 1#64) (List.replicate (63 - msg.length) 0#8))
      hm 64 := by
  have hw8 : m.write8 (hm + BitVec.ofNat 64 msg.length) 0x80#8 =
      m.writeBytes (hm + BitVec.ofNat 64 msg.length) [0x80#8] := rfl
  have h1 : hm + BitVec.ofNat 64 msg.length + 1#64 =
      (hm + BitVec.ofNat 64 msg.length) + BitVec.ofNat 64 ([0x80#8] : List (BitVec 8)).length := rfl
  rw [hw8, h1, ← Bytes.writeBytes_append]
  refine ProofLib.AgreesOutside.writeBytes _
    (AgreesOutside.rfl' m hm 64) ?_
  simp only [List.length_append, List.length_singleton, List.length_replicate]
  bv_omega

theorem ult_7_of_ge_56 {n : ℕ} (hge : 56 ≤ n) (hlt : n < 64) :
    (7#64).ult (BitVec.ofNat 64 (63 - n)) = false := by
  simp [BitVec.ult, Nat.mod_eq_of_lt (by omega : 63 - n < 18446744073709551616)]
  omega

theorem read64_fsp32_hm (m : Memory) (hm fsp : BitVec 64)
    (u0 u1 u2 u3 off : BitVec 64)
    (hoff : off.toNat + 8 ≤ 64)
    (hd : DisjointRegions hm 64 fsp 64) :
    ((((m.write64 fsp u0).write64 (fsp + 8#64) u1).write64
      (fsp + 16#64) u2).write64 (fsp + 24#64) u3).read64 (hm + off) = m.read64 (hm + off) := by
  let m_lo := (((m.write64 fsp u0).write64 (fsp + 8#64) u1).write64
    (fsp + 16#64) u2).write64 (fsp + 24#64) u3
  have hag_lo : AgreesOutside m m_lo fsp 32 := by
    dsimp only [m_lo]; agrees_outside_writes
  have hd_lo : DisjointRegions fsp 32 (hm + off) 8 :=
    (hd.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  exact hag_lo.read64_eq hd_lo

theorem readBytes_fsp_64_copy (m : Memory) (fsp : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64) :
    ((((((((m.write64 fsp v0).write64 (fsp + 8#64) v1).write64
      (fsp + 16#64) v2).write64 (fsp + 24#64) v3).write64
      (fsp + 32#64) v4).write64 (fsp + 40#64) v5).write64
      (fsp + 48#64) v6).write64 (fsp + 56#64) v7).readBytes fsp 64 =
      toLEBytes 8 v0 ++ toLEBytes 8 v1 ++ toLEBytes 8 v2 ++ toLEBytes 8 v3 ++
      toLEBytes 8 v4 ++ toLEBytes 8 v5 ++ toLEBytes 8 v6 ++ toLEBytes 8 v7 := by
  let m_lo := (((m.write64 fsp v0).write64 (fsp + 8#64) v1).write64
    (fsp + 16#64) v2).write64 (fsp + 24#64) v3
  let m_hi := (((m_lo.write64 (fsp + 32#64) v4).write64 (fsp + 40#64) v5).write64
    (fsp + 48#64) v6).write64 (fsp + 56#64) v7
  change m_hi.readBytes fsp (32 + 32) = _
  rw [Bytes.readBytes_add m_hi fsp 32 32]
  have h_hi : m_hi.readBytes (fsp + 32#64) 32 =
      toLEBytes 8 v4 ++ toLEBytes 8 v5 ++ toLEBytes 8 v6 ++ toLEBytes 8 v7 := by
    have h1 : fsp + 40#64 = (fsp + 32#64) + 8#64 := by bv_lin
    have h2 : fsp + 48#64 = (fsp + 32#64) + 16#64 := by bv_lin
    have h3 : fsp + 56#64 = (fsp + 32#64) + 24#64 := by bv_lin
    dsimp only [m_hi]
    rw [h1, h2, h3, readBytes_write64_4]
  have hag_hi : AgreesOutside m_lo m_hi (fsp + 32#64) 32 := by
    dsimp only [m_hi]; agrees_outside_writes
  have h_lo_eq : m_hi.readBytes fsp 32 = m_lo.readBytes fsp 32 :=
    hag_hi.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)
  rw [h_lo_eq, readBytes_write64_4, h_hi]
  simp only [List.append_assoc]

theorem readBytes_64_eq_append_8 (m : Memory) (hm : BitVec 64) :
    m.readBytes hm 8 ++ m.readBytes (hm + 8#64) 8 ++ m.readBytes (hm + 16#64) 8 ++
      m.readBytes (hm + 24#64) 8 ++ m.readBytes (hm + 32#64) 8 ++
      m.readBytes (hm + 40#64) 8 ++ m.readBytes (hm + 48#64) 8 ++
      m.readBytes (hm + 56#64) 8 =
      m.readBytes hm 64 := by
  rw [readBytes_56_eq_append_8 m hm, ← Bytes.readBytes_add m hm 56 8]

theorem toLEBytes_8_zero_7 :
    toLEBytes 8 0#64 ++ toLEBytes 8 0#64 ++ toLEBytes 8 0#64 ++ toLEBytes 8 0#64 ++
      toLEBytes 8 0#64 ++ toLEBytes 8 0#64 ++ toLEBytes 8 0#64 =
      List.replicate 56 0#8 := by
  decide

/-! ## 3. Generalized Segment Proofs for `finalize_fixed [local#3]` (`0x6ce50 .. 0x6d00c`) -/

/-- Bundled preconditions of `finalize_fixed [local#3]` (`0x6ce50`) with a 64-byte-aligned prefix `pfx`
and tail `tail` (`|tail| < 64`, covering both `< 56` and `[56, 64)`). -/
structure FinPre3PfxGen (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 : State) : Prop where
  pc_eq        : s0.pc = b + 0x67a58#64
  status       : s0.status = .Running
  key_le       : key.length ≤ 64
  tail_lt      : tail.length < 64
  hmac_st      : HmacStN s0.mem (s0.readReg64 .x1) F key pfx tail
  rw_out       : RW s0.mem (s0.readReg64 .x0) 32
  rw_hm        : RW s0.mem (s0.readReg64 .x1) 0x90
  rw_fsp       : RW s0.mem (s0.sp - 144#64) 144
  disj_out_hm  : DisjointRegions (s0.readReg64 .x0) 32 (s0.readReg64 .x1) 0x90
  disj_out_fsp : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64) 144
  disj_hm_fsp  : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64) 144
  sp_aligned   : (s0.sp &&& 0b1111#64) = 0#64

namespace FinalizeFixed3GenProof

open FinalizeFixedProof (FinCommon FinPost)

variable {C : Crypto} {ext : String → Option (State → State)}

@[local simp, local arm64_norm]
private theorem extractLsb'_0_64_zero128 : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl

@[local simp, local arm64_norm]
private theorem extractLsb'_64_64_zero128 : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl

/-- Cut `F0p` at `b + 0x6ce6c` (7 steps after entry): prologue complete. -/
private structure StateF0p (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x67a74#64
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x0
  x1_eq   : s.readReg64 .x1 = s0.readReg64 .x1
  hmac_st : HmacStN s.mem (s0.readReg64 .x1) F key pfx tail

set_option hygiene false in
local macro "seg1a_gen_body" : tactic => `(tactic| (
  have hpc := hpre.pc_eq
  have hstat := hpre.status
  have hal0 : (s0.sp &&& 15#64) = 0#64 := hpre.sp_aligned
  have hal_fsp : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hrw_fsp : s0.mem.RW (s0.sp - 144#64) 144 := hpre.rw_fsp
  iterate 7 fin3_step
  refine RunsTo.refl ?_
  have hag : AgreesOutside s0.mem
      (((((((((s0.mem.write64 (s0.sp - 144#64 + 64#64) (s0.readReg64 .x29)).write64
        (s0.sp - 144#64 + 72#64) (s0.readReg64 .lr)).write64
        (s0.sp - 144#64 + 80#64) (s0.readReg64 .x25)).write64
        (s0.sp - 144#64 + 96#64) (s0.readReg64 .x24)).write64
        (s0.sp - 144#64 + 104#64) (s0.readReg64 .x23)).write64
        (s0.sp - 144#64 + 112#64) (s0.readReg64 .x22)).write64
        (s0.sp - 144#64 + 120#64) (s0.readReg64 .x21)).write64
        (s0.sp - 144#64 + 128#64) (s0.readReg64 .x20)).write64
        (s0.sp - 144#64 + 136#64) (s0.readReg64 .x19))
      (s0.sp - 144#64) 144 := by agrees_outside_writes
  refine ⟨by fin3_reg,
    ⟨by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      ⟨by solve_fin3_saved, by solve_fin3_saved, by solve_fin3_saved,
       by solve_fin3_saved, by solve_fin3_saved, by solve_fin3_saved,
       by solve_fin3_saved, by solve_fin3_saved, by solve_fin3_saved⟩,
      by rw [mem_setMem]; exact Frame.trans_agreesOutside (Frame.refl s0.mem _) (by simp) hag⟩,
    by fin3_reg, by fin3_reg,
    by rw [mem_setMem]; exact HmacStN.of_agreesOutside hpre.hmac_st hag hpre.disj_hm_fsp.symm⟩))

set_option maxHeartbeats 1600000 in
private theorem seg1a_runsTo [HkdfHooks C.F ext] {b : BitVec 64} {key pfx tail : List (BitVec 8)} {s0 : State}
    (hpre : FinPre3PfxGen b C.F key pfx tail s0) :
    RunsTo (tripleRatchetProgAtExt b ext) s0 (StateF0p b C.F key pfx tail s0) := by
  seg1a_gen_body

set_option maxHeartbeats 1600000 in
private theorem seg1a_runsTo_placed [LibsignalPlacement] {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    {key pfx tail : List (BitVec 8)} {s0 : State}
    (hpre : FinPre3PfxGen fin3PlacedFakeB C.F key pfx tail s0) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s0 (StateF0p fin3PlacedFakeB C.F key pfx tail s0) := by
  seg1a_gen_body

/-- Cut `F1` at `b + 0x6ce9c` (after `memsetHook`): buffer `hm[0..64]` holds `innerPadBlock1 tail`. -/
private structure StateF1 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x67aa4#64
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 tail.length
  x24_eq  : s.readReg64 .x24 = BitVec.ofNat 64 (1 + pfx.length / 64)
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 (63 - tail.length)
  buf_eq  : s.mem.readBytes (s0.readReg64 .x1) 64 = innerPadBlock1 tail
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes ((chunks64 pfx).foldl F (hmacInnerInit F key))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

set_option hygiene false in
local macro "seg1b_gen_body " bTerm:term:max memsetLem:term:max : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx0, hx1, hhmac⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  rcases hhmac with ⟨hpfx_mod, hmsg_lt64, hmsg_eq, hpos_eq, hin_eq, hibl_eq, hout_eq, hobl_eq⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hcw_pos : s.mem.canWrite (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) 1 = true :=
    hrw_hm.canWrite_sub (by bv_omega) (by decide)
  have hze32 := zeroExtend64_truncate32_ofNat64 hmsg_lt64
  have hze64 := zeroExtend64_ofNat8 hmsg_lt64
  have hxor63 := xor_63_of_lt_64 hmsg_lt64
  iterate 12 fin3_step
  have htoNat_sub : (BitVec.ofNat 64 (63 - tail.length)).toNat = 63 - tail.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrw_memset :
      (s.mem.write8 (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) 128#8).RW
        (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length + 1#64) (63 - tail.length) := by
    refine Memory.RW.of_perm_eq (by simp) (fun _ => Memory.isLazyFree_write8_of_false _ _) (hrw_hm.sub ?_)
    have := hpre.tail_lt; bv_omega
  refine $memsetLem
    hstat rfl
    ((by simp only [arm64_norm]) : _ = s0.readReg64 .x1 + BitVec.ofNat 64 tail.length + 1#64)
    (by simp (config := { decide := true }) only [arm64_norm]) htoNat_sub
    ((by fin3_reg) : _ = $bTerm + 0x67aa4#64) hrw_memset ?_
  refine RunsTo.refl ?_
  have hag := agreesOutside_pad_memset_lt64 s.mem (s0.readReg64 .x1) tail hpre.tail_lt
  have hd_hm64_fsp : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine ⟨rfl,
    ⟨by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      FinSaved.of_agreesOutside hsaved hag hd_hm64_fsp,
      Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
        (by simp) (by bv_omega) hag⟩,
    by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
    readBytes_64_after_pad_memset_lt64 s.mem (s0.readReg64 .x1) tail hmsg_eq hpre.tail_lt,
    (hag.readBytes_eq hd_hm64_ist (by decide)).trans hin_eq,
    (hag.readBytes_eq hd_hm64_ost (by decide)).trans hout_eq,
    (hag.read64_eq hd_hm64_obl).trans hobl_eq⟩))

set_option maxHeartbeats 1600000 in
private theorem seg1b_runsTo [HkdfHooks C.F ext] {b : BitVec 64} {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen b C.F key pfx tail s0)
    (hs : StateF0p b C.F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateF1 b C.F key pfx tail s0) := by
  seg1b_gen_body b (s2_memset_step_ext b C ext)

set_option maxHeartbeats 1600000 in
private theorem seg1b_runsTo_placed [LibsignalPlacement] {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF0p fin3PlacedFakeB C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF1 fin3PlacedFakeB C.F key pfx tail s0) := by
  seg1b_gen_body fin3PlacedFakeB (FinalizeFixed3Proof.s2_memset_step_425 C H)

/-- Cut `F2a` at `b + 0x6cec0` (right before first `bl compress256` on the `[56, 64)` path). -/
private structure StateF2a (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x67ac8#64
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 tail.length
  x24_eq  : s.readReg64 .x24 = BitVec.ofNat 64 (1 + pfx.length / 64)
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 = innerPadBlock1 tail
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes ((chunks64 pfx).foldl F (hmacInnerInit F key))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

set_option hygiene false in
local macro "seg2_two_a_body" : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hult_7 := ult_7_of_ge_56 hge hpre.tail_lt
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  iterate 7 fin3_step
  have hread32 := fun u0 u1 u2 u3 => read64_fsp32_hm s.mem _ _ u0 u1 u2 u3 32#64 (by decide) hd_hm64_fsp64
  have hread40 := fun u0 u1 u2 u3 => read64_fsp32_hm s.mem _ _ u0 u1 u2 u3 40#64 (by decide) hd_hm64_fsp64
  have hread48 := fun u0 u1 u2 u3 => read64_fsp32_hm s.mem _ _ u0 u1 u2 u3 48#64 (by decide) hd_hm64_fsp64
  have hread56 := fun u0 u1 u2 u3 => read64_fsp32_hm s.mem _ _ u0 u1 u2 u3 56#64 (by decide) hd_hm64_fsp64
  iterate 2 fin3_step
  clear hread32 hread40 hread48 hread56
  refine RunsTo.refl ?_
  have hag : AgreesOutside s.mem
      ((((((((s.mem.write64 (s0.sp - 144#64) (s.mem.read64 (s0.readReg64 .x1))).write64
        (s0.sp - 144#64 + 8#64) (s.mem.read64 (s0.readReg64 .x1 + 8#64))).write64
        (s0.sp - 144#64 + 16#64) (s.mem.read64 (s0.readReg64 .x1 + 16#64))).write64
        (s0.sp - 144#64 + 24#64) (s.mem.read64 (s0.readReg64 .x1 + 24#64))).write64
        (s0.sp - 144#64 + 32#64) (s.mem.read64 (s0.readReg64 .x1 + 32#64))).write64
        (s0.sp - 144#64 + 40#64) (s.mem.read64 (s0.readReg64 .x1 + 40#64))).write64
        (s0.sp - 144#64 + 48#64) (s.mem.read64 (s0.readReg64 .x1 + 48#64))).write64
        (s0.sp - 144#64 + 56#64) (s.mem.read64 (s0.readReg64 .x1 + 56#64)))
      (s0.sp - 144#64) 64 := by agrees_outside_writes
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_ist : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x40#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_obl : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x88#64) 8 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  refine ⟨by fin3_reg,
    ⟨by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      by rw [mem_setMem]; exact FinSaved.of_agreesOutside hsaved hag hd_fsp64_saved,
      by rw [mem_setMem]; exact Frame.trans_agreesOutside_sub hframe (rbase := s0.sp - 144#64) (rlen := 144) (by simp) (by bv_omega) hag⟩,
    by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
    by fin3_reg, by fin3_reg,
    by rw [mem_setMem]; refine (readBytes_fsp_64_copy _ _ _ _ _ _ _ _ _ _).trans ?_
       rw [toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
           toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
           readBytes_64_eq_append_8 s.mem (s0.readReg64 .x1), hbuf],
    by rw [mem_setMem]; exact (hag.readBytes_eq hd_fsp64_ist (by decide)).trans hist,
    by rw [mem_setMem]; exact (hag.readBytes_eq hd_fsp64_ost (by decide)).trans host,
    by rw [mem_setMem]; exact (hag.read64_eq hd_fsp64_obl).trans hobl⟩))

set_option maxHeartbeats 1600000 in
private theorem seg2_two_a_runsTo [HkdfHooks C.F ext] {b : BitVec 64}
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen b C.F key pfx tail s0)
    (hge : 56 ≤ tail.length)
    (hs : StateF1 b C.F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateF2a b C.F key pfx tail s0) := by
  seg2_two_a_body

set_option maxHeartbeats 1600000 in
private theorem seg2_two_a_runsTo_placed [LibsignalPlacement] {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen fin3PlacedFakeB C.F key pfx tail s0)
    (hge : 56 ≤ tail.length)
    (hs : StateF1 fin3PlacedFakeB C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF2a fin3PlacedFakeB C.F key pfx tail s0) := by
  seg2_two_a_body

/-- Cut `F2b` at `b + 0x6cec4` (after first `compress256Hook` on the `[56, 64)` path). -/
private structure StateF2b (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x67acc#64
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 tail.length
  x24_eq  : s.readReg64 .x24 = BitVec.ofNat 64 (1 + pfx.length / 64)
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes (F ((chunks64 pfx).foldl F (hmacInnerInit F key)) (innerPadBlock1 tail))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

set_option hygiene false in
local macro "seg2_two_b_body " compLem:term:max : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hx23, hx24, hblk, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_ist : s.mem.RW (s0.readReg64 .x1 + 0x40#64) 32 := hrw_hm.sub (by bv_omega)
  fin3_step
  refine $compLem
    hstat rfl (by fin3_reg) (by fin3_reg) (by fin3_reg) rfl
    hist hblk (innerPadBlock1_length hpre.tail_lt) hrw_ist ?_
  refine RunsTo.refl ?_
  set blk_in := shaStateBytes (C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key)) (innerPadBlock1 tail))
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x40#64) blk_in)
      (s0.readReg64 .x1 + 0x40#64) 32 := by
    have hlen : blk_in.length = 32 := shaStateBytes_length _
    rw [← hlen]; exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_in
  have hd_ist_saved : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_ist_ost : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_ist_obl : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine ⟨by fin3_reg,
    ⟨by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      FinSaved.of_agreesOutside hsaved hag_comp hd_ist_saved,
      Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90) (by simp) (by bv_omega) hag_comp⟩,
    by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
    by have hlen : blk_in.length = 32 := shaStateBytes_length _
       rw [← hlen]; exact Bytes.readBytes_writeBytes_same s.mem _ blk_in (by rw [hlen]; decide),
    (hag_comp.readBytes_eq hd_ist_ost (by decide)).trans host,
    (hag_comp.read64_eq hd_ist_obl).trans hobl⟩))

set_option maxHeartbeats 1600000 in
private theorem seg2_two_b_runsTo [HkdfHooks C.F ext] {b : BitVec 64}
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen b C.F key pfx tail s0)
    (hs : StateF2a b C.F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateF2b b C.F key pfx tail s0) := by
  seg2_two_b_body (@s2_compress256_step_ext b C ext _)

set_option maxHeartbeats 1600000 in
private theorem seg2_two_b_runsTo_placed [LibsignalPlacement] {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF2a fin3PlacedFakeB C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF2b fin3PlacedFakeB C.F key pfx tail s0) := by
  seg2_two_b_body (FinalizeFixed3Proof.s2_compress256_step_425 C H)

/-- Cut `F2c` at `b + 0x6cf00` (right before second `bl compress256` on the `[56, 64)` path). -/
private structure StateF2c (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x67b08#64
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 = innerPadBlock2 (1 + pfx.length / 64) tail
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes (F ((chunks64 pfx).foldl F (hmacInnerInit F key)) (innerPadBlock1 tail))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

set_option hygiene false in
local macro "seg2_two_c_body" : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  obtain ⟨hbit_len1, hbit_len2⟩ := bit_len_innerN_eq_lt64 (b := 1 + pfx.length / 64) hpre.tail_lt
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  iterate 8 fin3_step
  let mz := ((((((s.mem.write64 (s0.readReg64 .x1 + 48#64) 0#64).write64
    (s0.readReg64 .x1 + 16#64) 0#64).write64
    (s0.readReg64 .x1 + 24#64) 0#64).write64
    (s0.readReg64 .x1 + 32#64) 0#64).write64
    (s0.readReg64 .x1 + 40#64) 0#64).write64
    (s0.readReg64 .x1) 0#64).write64
    (s0.readReg64 .x1 + 8#64) 0#64
  have hread32 := fun u0 u1 u2 u3 w56 => read64_seg2a_mid mz _ _ u0 u1 u2 u3 w56 32#64 (by decide) hd_hm64_fsp64
  have hread40 := fun u0 u1 u2 u3 w56 => read64_seg2a_mid mz _ _ u0 u1 u2 u3 w56 40#64 (by decide) hd_hm64_fsp64
  have hread48 := fun u0 u1 u2 u3 w56 => read64_seg2a_mid mz _ _ u0 u1 u2 u3 w56 48#64 (by decide) hd_hm64_fsp64
  iterate 7 fin3_step
  clear hread32 hread40 hread48
  refine RunsTo.refl ?_
  have hag0 : AgreesOutside s.mem mz (s0.readReg64 .x1) 64 := by dsimp only [mz]; agrees_outside_writes
  obtain ⟨hag1, hag2, hag3⟩ := agreesOutside_seg2a mz (s0.readReg64 .x1) (s0.sp - 144#64)
    0#64 0#64 0#64 0#64 _ 0#64 0#64 0#64 _
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_ist : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x40#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_obl : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x88#64) 8 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  have hsaved0 : FinSaved s0 (s0.sp - 144#64) mz := FinSaved.of_agreesOutside hsaved hag0 hd_hm64_saved
  have hframe0 : Frame s0.mem mz [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)] :=
    Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90) (by simp) (by bv_omega) hag0
  refine ⟨by fin3_reg,
    ⟨by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      by rw [mem_setMem]
         exact FinSaved.of_agreesOutside
           (FinSaved.of_agreesOutside (FinSaved.of_agreesOutside hsaved0 hag1 hd_fsp64_saved)
             hag2 hd_hm64_saved) hag3 hd_fsp64_saved,
      by rw [mem_setMem]; exact frame_seg2a hframe0 hag1 hag2 hag3⟩,
    by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
    by rw [mem_setMem]; refine (readBytes_fsp_64_seg2 mz _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
       rw [toLEBytes_8_zero_7, toLEBytes_8_rev64]; rfl,
    by rw [mem_setMem]
       exact (hag3.readBytes_eq hd_fsp64_ist (by decide)).trans
         ((hag2.readBytes_eq hd_hm64_ist (by decide)).trans
           ((hag1.readBytes_eq hd_fsp64_ist (by decide)).trans
             ((hag0.readBytes_eq hd_hm64_ist (by decide)).trans hist))),
    by rw [mem_setMem]
       exact (hag3.readBytes_eq hd_fsp64_ost (by decide)).trans
         ((hag2.readBytes_eq hd_hm64_ost (by decide)).trans
           ((hag1.readBytes_eq hd_fsp64_ost (by decide)).trans
             ((hag0.readBytes_eq hd_hm64_ost (by decide)).trans host))),
    by rw [mem_setMem]
       exact (hag3.read64_eq hd_fsp64_obl).trans
         ((hag2.read64_eq hd_hm64_obl).trans
           ((hag1.read64_eq hd_fsp64_obl).trans
             ((hag0.read64_eq hd_hm64_obl).trans hobl)))⟩))

set_option maxHeartbeats 1600000 in
private theorem seg2_two_c_runsTo [HkdfHooks C.F ext] {b : BitVec 64}
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen b C.F key pfx tail s0)
    (hs : StateF2b b C.F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateF2c b C.F key pfx tail s0) := by
  seg2_two_c_body

set_option maxHeartbeats 1600000 in
private theorem seg2_two_c_runsTo_placed [LibsignalPlacement] {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF2b fin3PlacedFakeB C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF2c fin3PlacedFakeB C.F key pfx tail s0) := by
  seg2_two_c_body

/-- Cut `F3_two` at `b + 0x6cf04` (after second `compress256Hook` on the `[56, 64)` path). -/
private structure StateF3_two (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x67b0c#64
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes (F (F ((chunks64 pfx).foldl F (hmacInnerInit F key)) (innerPadBlock1 tail))
      (innerPadBlock2 (1 + pfx.length / 64) tail))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

set_option hygiene false in
local macro "seg2_two_d_body " compLem:term:max : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hblk, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_ist : s.mem.RW (s0.readReg64 .x1 + 0x40#64) 32 := hrw_hm.sub (by bv_omega)
  fin3_step
  refine $compLem
    hstat rfl (by fin3_reg) (by fin3_reg) (by fin3_reg) rfl
    hist hblk (innerPadBlock2_length (1 + pfx.length / 64) tail) hrw_ist ?_
  refine RunsTo.refl ?_
  set blk_in := shaStateBytes (C.F (C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key))
    (innerPadBlock1 tail)) (innerPadBlock2 (1 + pfx.length / 64) tail))
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x40#64) blk_in)
      (s0.readReg64 .x1 + 0x40#64) 32 := by
    have hlen : blk_in.length = 32 := shaStateBytes_length _
    rw [← hlen]; exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_in
  have hd_ist_saved : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_ist_ost : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_ist_obl : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine ⟨by fin3_reg,
    ⟨by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      FinSaved.of_agreesOutside hsaved hag_comp hd_ist_saved,
      Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90) (by simp) (by bv_omega) hag_comp⟩,
    by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
    by have hlen : blk_in.length = 32 := shaStateBytes_length _
       rw [← hlen]; exact Bytes.readBytes_writeBytes_same s.mem _ blk_in (by rw [hlen]; decide),
    (hag_comp.readBytes_eq hd_ist_ost (by decide)).trans host,
    (hag_comp.read64_eq hd_ist_obl).trans hobl⟩))

set_option maxHeartbeats 1600000 in
private theorem seg2_two_d_runsTo [HkdfHooks C.F ext] {b : BitVec 64}
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen b C.F key pfx tail s0)
    (hs : StateF2c b C.F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateF3_two b C.F key pfx tail s0) := by
  seg2_two_d_body (@s2_compress256_step_ext b C ext _)

set_option maxHeartbeats 1600000 in
private theorem seg2_two_d_runsTo_placed [LibsignalPlacement] {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF2c fin3PlacedFakeB C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF3_two fin3PlacedFakeB C.F key pfx tail s0) := by
  seg2_two_d_body (FinalizeFixed3Proof.s2_compress256_step_425 C H)

/-- Cut `F3b_two` at `b + 0x6cf80` (right before outer `bl compress256`). -/
private structure StateF3b_two (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x67b88#64
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 =
    outerBlock (digestBytes (F (F ((chunks64 pfx).foldl F (hmacInnerInit F key))
      (innerPadBlock1 tail))
      (innerPadBlock2 (1 + pfx.length / 64) tail)))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)

/-- Cut `F4_two` at `b + 0x6cf84` (after outer `compress256Hook`). -/
private structure StateF4_two (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x67b8c#64
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 =
    shaStateBytes (F (hmacOuterInit F key)
      (outerBlock (digestBytes (F (F ((chunks64 pfx).foldl F (hmacInnerInit F key))
        (innerPadBlock1 tail))
        (innerPadBlock2 (1 + pfx.length / 64) tail)))))

set_option hygiene false in
local macro "seg3a_two_body" : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_in := C.F (C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key)) (innerPadBlock1 tail))
    (innerPadBlock2 (1 + pfx.length / 64) tail)
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_64_of_shaStateBytes s.mem (s0.readReg64 .x1) h_in hist
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hrev768 : rev64 (256#64 ||| 512#64) = 0x0003000000000000#64 := by decide
  have hread32 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
    read64_seg3a_pad_32 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
  have hread40 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
    read64_seg3a_pad_40 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
  iterate 31 fin3_step
  clear hread32 hread40
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg3a s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
    _ _ _ _ _ _ _ _ _ _ _ _ 0#64 0x0003000000000000#64 0x80#64 0#64 0#64 0x0003000000000000#64
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  refine ⟨by fin3_reg,
    ⟨by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      by rw [mem_setMem]; exact finSaved_seg3a hsaved hag1 hag2 hag3 hag4 hd_hm64_saved hd_fsp64_saved,
      by rw [mem_setMem]; exact frame_seg3a hframe hag1 hag2 hag3 hag4⟩,
    by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
    by rw [mem_setMem]; refine (readBytes_fsp_64_seg3 _ _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
       rw [toLEBytes_8_rev32_append, toLEBytes_8_rev32_append,
           toLEBytes_8_rev32_append, toLEBytes_8_rev32_append]
       have htail : toLEBytes 8 0x80#64 ++ toLEBytes 8 0#64 ++ toLEBytes 8 0#64 ++
           toLEBytes 8 (rev64 768#64) =
           [0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 768#64 := by decide
       unfold outerBlock; rw [digestBytes_eq_append h_in]
       simp only [List.append_assoc] at htail ⊢; rw [htail]; rfl,
    by rw [mem_setMem]; exact ost_eq_seg3a host hag1 hag2 hag3 hag4 hd_hm64_ost hd_fsp64_ost⟩))

set_option maxHeartbeats 1600000 in
private theorem seg3a_two_runsTo [HkdfHooks C.F ext] {b : BitVec 64}
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen b C.F key pfx tail s0)
    (hs : StateF3_two b C.F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateF3b_two b C.F key pfx tail s0) := by
  seg3a_two_body

set_option maxHeartbeats 1600000 in
private theorem seg3a_two_runsTo_placed [LibsignalPlacement] {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF3_two fin3PlacedFakeB C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF3b_two fin3PlacedFakeB C.F key pfx tail s0) := by
  seg3a_two_body

set_option hygiene false in
local macro "seg3b_two_body " compLem:term:max : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hblk, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_ost : s.mem.RW (s0.readReg64 .x1 + 0x68#64) 32 := hrw_hm.sub (by bv_omega)
  set h_in := C.F (C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key)) (innerPadBlock1 tail))
    (innerPadBlock2 (1 + pfx.length / 64) tail)
  fin3_step
  refine $compLem
    hstat rfl (by fin3_reg) (by fin3_reg) (by fin3_reg) rfl
    host hblk (outerBlock_digestBytes_length h_in) hrw_ost ?_
  refine RunsTo.refl ?_
  set blk_out := shaStateBytes (C.F (hmacOuterInit C.F key) (outerBlock (digestBytes h_in)))
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x68#64) blk_out)
      (s0.readReg64 .x1 + 0x68#64) 32 := by
    have hlen : blk_out.length = 32 := shaStateBytes_length _
    rw [← hlen]; exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_out
  have hd_ost_saved : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  refine ⟨by fin3_reg,
    ⟨by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      FinSaved.of_agreesOutside hsaved hag_comp hd_ost_saved,
      Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90) (by simp) (by bv_omega) hag_comp⟩,
    by fin3_reg, by fin3_reg,
    by have hlen : blk_out.length = 32 := shaStateBytes_length _
       rw [← hlen]; exact Bytes.readBytes_writeBytes_same s.mem _ blk_out (by rw [hlen]; decide)⟩))

set_option maxHeartbeats 1600000 in
private theorem seg3b_two_runsTo [HkdfHooks C.F ext] {b : BitVec 64}
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen b C.F key pfx tail s0)
    (hs : StateF3b_two b C.F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateF4_two b C.F key pfx tail s0) := by
  seg3b_two_body (@s2_compress256_step_ext b C ext _)

set_option maxHeartbeats 1600000 in
private theorem seg3b_two_runsTo_placed [LibsignalPlacement] {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF3b_two fin3PlacedFakeB C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF4_two fin3PlacedFakeB C.F key pfx tail s0) := by
  seg3b_two_body (FinalizeFixed3Proof.s2_compress256_step_425 C H)

/-- Cut `F5` at `b + 0x6cff4` (right before the 7-instruction epilogue). -/
private structure StateF5 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = b + 0x67bfc#64
  common : FinCommon s0 s
  out_eq : s.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key (pfx ++ tail)

private theorem read32_seg4a_mid (m : Memory) (hm fsp off : BitVec 64) (w : BitVec 32)
    (hoff : off = 128#64 ∨ off = 132#64)
    (hd : DisjointRegions fsp 64 hm 0x90)
    (hw : m.read32 (hm + off) = w) :
    (((((((((m.write8 (hm + 63#64) 0#8).write64
      fsp 0#64).write64 (fsp + 8#64) 0#64).write64
      (fsp + 16#64) 0#64).write64 (fsp + 24#64) 0#64).write64
      (fsp + 32#64) 0#64).write64 (fsp + 40#64) 0#64).write64
      (fsp + 48#64) 0#64).write64 (fsp + 56#64) 0#64).read32
      (hm + off) = w := by
  have hag_fsp : AgreesOutside (m.write8 (hm + 63#64) 0#8)
      (((((((((m.write8 (hm + 63#64) 0#8).write64
        fsp 0#64).write64 (fsp + 8#64) 0#64).write64
        (fsp + 16#64) 0#64).write64 (fsp + 24#64) 0#64).write64
        (fsp + 32#64) 0#64).write64 (fsp + 40#64) 0#64).write64
        (fsp + 48#64) 0#64).write64 (fsp + 56#64) 0#64)
      fsp 64 := by agrees_outside_writes
  have hag_63 : AgreesOutside m (m.write8 (hm + 63#64) 0#8) (hm + 63#64) 1 := by agrees_outside_writes
  rcases hoff with rfl | rfl <;>
    rw [hag_fsp.read32_eq (hd.sub_right _ ⟨by decide, by bv_omega⟩),
        hag_63.read32_eq (by unfold DisjointRegions; bv_omega), hw]

private theorem seg4a_disj {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {key pfx tail : List (BitVec 8)} {s0 : State} (hpre : FinPre3PfxGen b F key pfx tail s0) :
    DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1) 0x90 ∧
    DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64 + 0x40#64) 0x50 ∧
    DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 ∧
    DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
  ⟨hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩,
   hpre.disj_hm_fsp.sub_right _ ⟨by decide, by bv_omega⟩,
   by unfold DisjointRegions; bv_omega,
   hpre.disj_out_fsp.sub_right _ ⟨by decide, by bv_omega⟩⟩

set_option hygiene false in
local macro "seg4a_two_body" : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx19, hx20, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 32 := rw_of_perm_eq hframe.2 hpre.rw_out
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_out := C.F (hmacOuterInit C.F key)
    (outerBlock (digestBytes (C.F (C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key))
      (innerPadBlock1 tail))
      (innerPadBlock2 (1 + pfx.length / 64) tail))))
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_104_of_shaStateBytes s.mem (s0.readReg64 .x1) h_out host
  have hzero64 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
  iterate 11 fin3_step
  have hd_fsp64_hm := (seg4a_disj hpre).1
  have hread128 := read32_seg4a_mid s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 128#64 (h_out.get 6)
    (Or.inl rfl) hd_fsp64_hm hw6
  have hread132 := read32_seg4a_mid s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 132#64 (h_out.get 7)
    (Or.inr rfl) hd_fsp64_hm hw7
  iterate 2 fin3_step
  clear hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hread128 hread132 hd_fsp64_hm host
  iterate 15 fin3_step
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg4a s.mem
    (s0.readReg64 .x0) (s0.readReg64 .x1) (s0.sp - 144#64) _ _ _ _ _ _ _ _
  obtain ⟨_, hd_hm_saved, hd_fsp64_saved, hd_out_saved⟩ := seg4a_disj hpre
  refine ⟨by fin3_reg,
    ⟨by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      by rw [mem_setMem]; exact finSaved_seg4a hsaved hag1 hag2 hag3 hag4 hd_hm_saved hd_fsp64_saved hd_out_saved,
      by rw [mem_setMem]; exact frame_seg4a hframe hag1 hag2 hag3 hag4⟩,
    by rw [mem_setMem]
       exact (readBytes_write32_8_digestBytes _ (s0.readReg64 .x0) h_out _ _ _ _ _ _ _ _
         (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
         (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)).trans
         (hmacWith_pfx_two_blocks C.F key pfx tail hpre.key_le hpre.hmac_st.1 hge hpre.tail_lt).symm⟩))

set_option maxHeartbeats 1600000 in
private theorem seg4a_two_runsTo [HkdfHooks C.F ext] {b : BitVec 64}
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen b C.F key pfx tail s0)
    (hge : 56 ≤ tail.length)
    (hs : StateF4_two b C.F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateF5 b C.F key pfx tail s0) := by
  seg4a_two_body

set_option maxHeartbeats 1600000 in
private theorem seg4a_two_runsTo_placed [LibsignalPlacement] {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen fin3PlacedFakeB C.F key pfx tail s0)
    (hge : 56 ≤ tail.length)
    (hs : StateF4_two fin3PlacedFakeB C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF5 fin3PlacedFakeB C.F key pfx tail s0) := by
  seg4a_two_body

set_option hygiene false in
local macro "seg4b_two_body" : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hout⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  rcases hsaved with ⟨hs29, hslr, hs25, hs24, hs23, hs22, hs21, hs20, hs19⟩
  have hs29' : s.mem.read64 (s0.sp - 144#64 + 64#64) = s0.readReg64 .x29 := hs29
  have hslr' : s.mem.read64 (s0.sp - 144#64 + 72#64) = s0.readReg64 .lr := hslr
  have hs25' : s.mem.read64 (s0.sp - 144#64 + 80#64) = s0.readReg64 .x25 := hs25
  have hs24' : s.mem.read64 (s0.sp - 144#64 + 96#64) = s0.readReg64 .x24 := hs24
  have hs23' : s.mem.read64 (s0.sp - 144#64 + 104#64) = s0.readReg64 .x23 := hs23
  have hs22' : s.mem.read64 (s0.sp - 144#64 + 112#64) = s0.readReg64 .x22 := hs22
  have hs21' : s.mem.read64 (s0.sp - 144#64 + 120#64) = s0.readReg64 .x21 := hs21
  have hs20' : s.mem.read64 (s0.sp - 144#64 + 128#64) = s0.readReg64 .x20 := hs20
  have hs19' : s.mem.read64 (s0.sp - 144#64 + 136#64) = s0.readReg64 .x19 := hs19
  iterate 7 fin3_step
  refine RunsTo.refl ⟨by simp (config := { decide := true }) only [arm64_norm], hstat,
    ⟨by simp (config := { decide := true }) only [arm64_norm], fun r hr => ?_⟩, hout, hframe⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [arm64_norm, hx26, hx27, hx28]))

set_option maxHeartbeats 1600000 in
private theorem seg4b_two_runsTo [HkdfHooks C.F ext] {b : BitVec 64}
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen b C.F key pfx tail s0)
    (hs : StateF5 b C.F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (FinPost C.F key (pfx ++ tail) s0) := by
  seg4b_two_body

set_option maxHeartbeats 1600000 in
private theorem seg4b_two_runsTo_placed [LibsignalPlacement] {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF5 fin3PlacedFakeB C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (FinPost C.F key (pfx ++ tail) s0) := by
  seg4b_two_body

/-- Full `RunsTo` contract of `finalize_fixed [local#3]` (`0x6ce50 → s0.readReg64 .lr`)
for any `tail.length < 64` (both `< 56` and `[56, 64)`) and `key.length ≤ 64`. -/
theorem finalize_fixed3_pfx_lt64_runsTo_ext [HkdfHooks C.F ext] {b : BitVec 64}
    {key pfx tail : List (BitVec 8)} {s0 : State}
    (hpre : FinPre3PfxGen b C.F key pfx tail s0) :
    RunsTo (tripleRatchetProgAtExt b ext) s0 (FinPost C.F key (pfx ++ tail) s0) := by
  by_cases hlt56 : tail.length < 56
  · exact FinalizeFixed3Proof.finalize_fixed3_pfx_runsTo_ext
      { pc_eq := hpre.pc_eq, status := hpre.status, key_le := hpre.key_le, tail_lt := hlt56,
        hmac_st := hpre.hmac_st, rw_out := hpre.rw_out, rw_hm := hpre.rw_hm, rw_fsp := hpre.rw_fsp,
        disj_out_hm := hpre.disj_out_hm, disj_out_fsp := hpre.disj_out_fsp,
        disj_hm_fsp := hpre.disj_hm_fsp, sp_aligned := hpre.sp_aligned }
  · have hge56 : 56 ≤ tail.length := Nat.le_of_not_lt hlt56
    exact
      (seg1a_runsTo hpre).trans fun _ hs1 => (seg1b_runsTo hpre hs1).trans fun _ hs2 =>
      (seg2_two_a_runsTo hpre hge56 hs2).trans fun _ hs3 => (seg2_two_b_runsTo hpre hs3).trans fun _ hs4 =>
      (seg2_two_c_runsTo hpre hs4).trans fun _ hs5 => (seg2_two_d_runsTo hpre hs5).trans fun _ hs6 =>
      (seg3a_two_runsTo hpre hs6).trans fun _ hs7 => (seg3b_two_runsTo hpre hs7).trans fun _ hs8 =>
      (seg4a_two_runsTo hpre hge56 hs8).trans fun _ hs9 => seg4b_two_runsTo hpre hs9

theorem finalize_fixed3_pfx_lt64_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    {key pfx tail : List (BitVec 8)} {s0 : State}
    (hpre : FinPre3PfxGen fin3PlacedFakeB C.F key pfx tail s0) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s0 (FinPost C.F key (pfx ++ tail) s0) := by
  by_cases hlt56 : tail.length < 56
  · exact FinalizeFixed3Proof.finalize_fixed3_pfx_placed_runsTo
      { pc_eq := hpre.pc_eq, status := hpre.status, key_le := hpre.key_le, tail_lt := hlt56,
        hmac_st := hpre.hmac_st, rw_out := hpre.rw_out, rw_hm := hpre.rw_hm, rw_fsp := hpre.rw_fsp,
        disj_out_hm := hpre.disj_out_hm, disj_out_fsp := hpre.disj_out_fsp,
        disj_hm_fsp := hpre.disj_hm_fsp, sp_aligned := hpre.sp_aligned }
  · have hge56 : 56 ≤ tail.length := Nat.le_of_not_lt hlt56
    exact
      (seg1a_runsTo_placed hpre).trans fun _ hs1 => (seg1b_runsTo_placed hpre hs1).trans fun _ hs2 =>
      (seg2_two_a_runsTo_placed hpre hge56 hs2).trans fun _ hs3 => (seg2_two_b_runsTo_placed hpre hs3).trans fun _ hs4 =>
      (seg2_two_c_runsTo_placed hpre hs4).trans fun _ hs5 => (seg2_two_d_runsTo_placed hpre hs5).trans fun _ hs6 =>
      (seg3a_two_runsTo_placed hpre hs6).trans fun _ hs7 => (seg3b_two_runsTo_placed hpre hs7).trans fun _ hs8 =>
      (seg4a_two_runsTo_placed hpre hge56 hs8).trans fun _ hs9 => seg4b_two_runsTo_placed hpre hs9

theorem finalize_fixed3_pfx_lt64_placed_runsTo_of_other_block [LibsignalPlacement] {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H] {callerProg : Program} {i : Nat} [hcaller : IsLsBlockProg callerProg i H]
    {key pfx tail : List (BitVec 8)} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpre : FinPre3PfxGen fin3PlacedFakeB C.F key pfx tail s0)
    (hi : i < 619 := by decide) :
    RunsTo callerProg s0 (FinPost C.F key (pfx ++ tail) s0) :=
  RunsTo.of_other_block hcl (finalize_fixed3_pfx_lt64_placed_runsTo hpre) hi (by decide) (by decide)

end FinalizeFixed3GenProof

/-- Generalized `RunsTo` contract of `finalize_fixed [local#3]` (`0x6ce50`) on
`tripleRatchetProgAtExt b ext` over `HmacStN` (`tail.length < 64`, arbitrary `key`). -/
theorem finalize_fixed3_gen_runsTo_ext (b : BitVec 64) (C : Crypto)
    (ext : String → Option (State → State)) [HkdfHooks C.F ext] :
    Fin3GenRunsToExt b C.F ext := by
  intro key pfx tail s₀ hpre
  have hpre' : FinPre3PfxGen b C.F (effectiveHmacKey C.F key) pfx tail s₀ :=
    { pc_eq := hpre.pc_eq, status := hpre.status, key_le := effectiveHmacKey_length_le C.F key,
      tail_lt := hpre.tail_lt, hmac_st := hpre.hmac_st, rw_out := hpre.rw_out, rw_hm := hpre.rw_hm,
      rw_fsp := hpre.rw_fsp, disj_out_hm := hpre.disj_out_hm, disj_out_fsp := hpre.disj_out_fsp,
      disj_hm_fsp := hpre.disj_hm_fsp, sp_aligned := hpre.sp_aligned }
  refine (FinalizeFixed3GenProof.finalize_fixed3_pfx_lt64_runsTo_ext (ext := ext) hpre').mono
    fun s' ⟨hpc', hstat', hcs', hout', hfr'⟩ => ?_
  rw [hmacWith_effectiveHmacKey] at hout'
  exact ⟨hpc', hstat', hcs', hout', hfr'⟩

theorem finalize_fixed3_gen_placed_runsTo [LibsignalPlacement] (C : Crypto) (H : LibsignalHooks)
    [HkdfPlacedHooks C.F H] (key pfx tail : List (BitVec 8)) (s₀ : State)
    (hpc : s₀.pc = lsmpl.base 425) (hstat : s₀.status = .Running)
    (htail : tail.length < 64)
    (hhmac : HmacStN s₀.mem (s₀.readReg64 .x1) C.F (effectiveHmacKey C.F key) pfx tail)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 32)
    (hrw_hm : RW s₀.mem (s₀.readReg64 .x1) 0x90)
    (hrw_fsp : RW s₀.mem (s₀.sp - 144#64) 144)
    (hd_out_hm : DisjointRegions (s₀.readReg64 .x0) 32 (s₀.readReg64 .x1) 0x90)
    (hd_out_fsp : DisjointRegions (s₀.readReg64 .x0) 32 (s₀.sp - 144#64) 144)
    (hd_hm_fsp : DisjointRegions (s₀.readReg64 .x1) 0x90 (s₀.sp - 144#64) 144)
    (hsp : (s₀.sp &&& 0b1111#64) = 0#64) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.readBytes (s₀.readReg64 .x0) 32 = hmacWith C.F key (pfx ++ tail) ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 32), (s₀.readReg64 .x1, 0x90), (s₀.sp - 144#64, 144)]) := by
  have hpc' : s₀.pc = fin3PlacedFakeB + 0x67a58#64 := by rw [fin3PlacedFakeB_off_0]; exact hpc
  have hpre' : FinPre3PfxGen fin3PlacedFakeB C.F (effectiveHmacKey C.F key) pfx tail s₀ :=
    { pc_eq := hpc', status := hstat, key_le := effectiveHmacKey_length_le C.F key,
      tail_lt := htail, hmac_st := hhmac, rw_out := hrw_out, rw_hm := hrw_hm,
      rw_fsp := hrw_fsp, disj_out_hm := hd_out_hm, disj_out_fsp := hd_out_fsp,
      disj_hm_fsp := hd_hm_fsp, sp_aligned := hsp }
  refine (FinalizeFixed3GenProof.finalize_fixed3_pfx_lt64_placed_runsTo hpre').mono
    fun s' ⟨hpc'', hstat', hcs', hout', hfr'⟩ => ?_
  rw [hmacWith_effectiveHmacKey] at hout'
  exact ⟨hpc'', hstat', hcs', hout', hfr'⟩

theorem finalize_fixed3_gen_placed_runsTo_of_other_block [LibsignalPlacement] (C : Crypto) (H : LibsignalHooks)
    [HkdfPlacedHooks C.F H] {callerProg : Program} {i : Nat} [hcaller : IsLsBlockProg callerProg i H]
    (key pfx tail : List (BitVec 8)) (s₀ : State)
    (hcl : LibsignalCodeLoaded lsmpl s₀.mem)
    (hpc : s₀.pc = lsmpl.base 425) (hstat : s₀.status = .Running)
    (htail : tail.length < 64)
    (hhmac : HmacStN s₀.mem (s₀.readReg64 .x1) C.F (effectiveHmacKey C.F key) pfx tail)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 32)
    (hrw_hm : RW s₀.mem (s₀.readReg64 .x1) 0x90)
    (hrw_fsp : RW s₀.mem (s₀.sp - 144#64) 144)
    (hd_out_hm : DisjointRegions (s₀.readReg64 .x0) 32 (s₀.readReg64 .x1) 0x90)
    (hd_out_fsp : DisjointRegions (s₀.readReg64 .x0) 32 (s₀.sp - 144#64) 144)
    (hd_hm_fsp : DisjointRegions (s₀.readReg64 .x1) 0x90 (s₀.sp - 144#64) 144)
    (hsp : (s₀.sp &&& 0b1111#64) = 0#64)
    (hi : i < 619 := by decide) :
    RunsTo callerProg s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.readBytes (s₀.readReg64 .x0) 32 = hmacWith C.F key (pfx ++ tail) ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 32), (s₀.readReg64 .x1, 0x90), (s₀.sp - 144#64, 144)]) :=
  RunsTo.of_other_block hcl
    (finalize_fixed3_gen_placed_runsTo C H key pfx tail s₀ hpc hstat htail hhmac hrw_out hrw_hm hrw_fsp
      hd_out_hm hd_out_fsp hd_hm_fsp hsp)
    hi (by decide) (by decide)

end CryptoVerification.SpqrV1.Kdf
