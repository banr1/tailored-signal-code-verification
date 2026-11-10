/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.Defs
public import LibsignalBinary.Proofs.SpqrV1.Kdf.KdfCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes

/-!
# Verification of `Hmac<Sha256>::finalize_fixed` (`0x6ce50`, Block `425`)

Proves `RunsTo` and separation-logic contracts for
`<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#2]` (`0x6ce50`, 112
instructions) over `HmacStN` (`pfx.length % 64 = 0`, `tail.length < 56`), covering both single-block
and multi-block HMAC finalizations in `spqr::kdf::hkdf_to_slice`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

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

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

@[simp, arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [0x67a58 → 0x67c14]

abbrev fin3PlacedFakeB [LibsignalPlacement] : BitVec 64 :=
  (blkPl_425).base - bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#2]")

@[simp, arm64_norm] theorem fin3PlacedFakeB_off_0 [LibsignalPlacement] :
    fin3PlacedFakeB + 0x67a58#64 = (blkPl_425).base := BitVec.sub_add_cancel _ _
@[simp, arm64_norm] theorem fin3PlacedFakeB_off_28 [LibsignalPlacement] :
    fin3PlacedFakeB + 0x67a74#64 = (blkPl_425).base + 28#64 := by dsimp only [fin3PlacedFakeB]; bv_lin
@[simp, arm64_norm] theorem fin3PlacedFakeB_off_76 [LibsignalPlacement] :
    fin3PlacedFakeB + 0x67aa4#64 = (blkPl_425).base + 76#64 := by dsimp only [fin3PlacedFakeB]; bv_lin
@[simp, arm64_norm] theorem fin3PlacedFakeB_off_80 [LibsignalPlacement] :
    fin3PlacedFakeB + 0x67aa8#64 = (blkPl_425).base + 80#64 := by dsimp only [fin3PlacedFakeB]; bv_lin
@[simp, arm64_norm] theorem fin3PlacedFakeB_off_84 [LibsignalPlacement] :
    fin3PlacedFakeB + 0x67aac#64 = (blkPl_425).base + 84#64 := by dsimp only [fin3PlacedFakeB]; bv_lin
@[simp, arm64_norm] theorem fin3PlacedFakeB_off_112 [LibsignalPlacement] :
    fin3PlacedFakeB + 0x67ac8#64 = (blkPl_425).base + 112#64 := by dsimp only [fin3PlacedFakeB]; bv_lin
@[simp, arm64_norm] theorem fin3PlacedFakeB_off_116 [LibsignalPlacement] :
    fin3PlacedFakeB + 0x67acc#64 = (blkPl_425).base + 116#64 := by dsimp only [fin3PlacedFakeB]; bv_lin
@[simp, arm64_norm] theorem fin3PlacedFakeB_off_128 [LibsignalPlacement] :
    fin3PlacedFakeB + 0x67ad8#64 = (blkPl_425).base + 128#64 := by dsimp only [fin3PlacedFakeB]; bv_lin
@[simp, arm64_norm] theorem fin3PlacedFakeB_off_132 [LibsignalPlacement] :
    fin3PlacedFakeB + 0x67adc#64 = (blkPl_425).base + 132#64 := by dsimp only [fin3PlacedFakeB]; bv_lin
@[simp, arm64_norm] theorem fin3PlacedFakeB_off_176 [LibsignalPlacement] :
    fin3PlacedFakeB + 0x67b08#64 = (blkPl_425).base + 176#64 := by dsimp only [fin3PlacedFakeB]; bv_lin
@[simp, arm64_norm] theorem fin3PlacedFakeB_off_180 [LibsignalPlacement] :
    fin3PlacedFakeB + 0x67b0c#64 = (blkPl_425).base + 180#64 := by dsimp only [fin3PlacedFakeB]; bv_lin
@[simp, arm64_norm] theorem fin3PlacedFakeB_off_304 [LibsignalPlacement] :
    fin3PlacedFakeB + 0x67b88#64 = (blkPl_425).base + 304#64 := by dsimp only [fin3PlacedFakeB]; bv_lin
@[simp, arm64_norm] theorem fin3PlacedFakeB_off_308 [LibsignalPlacement] :
    fin3PlacedFakeB + 0x67b8c#64 = (blkPl_425).base + 308#64 := by dsimp only [fin3PlacedFakeB]; bv_lin
@[simp, arm64_norm] theorem fin3PlacedFakeB_off_420 [LibsignalPlacement] :
    fin3PlacedFakeB + 0x67bfc#64 = (blkPl_425).base + 420#64 := by dsimp only [fin3PlacedFakeB]; bv_lin

private theorem mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

macro "solve_fin3_saved" : tactic =>
  `(tactic| (
    try rw [mem_setMem]
    simp (config := { decide := true }) only [arm64_norm]))

macro "fin3_reg" : tactic =>
  `(tactic| (
    try rw [State.readReg64_setMem]
    try rw [State.pc_setMem]
    try rw [State.sp_setMem]
    try rw [State.status_setMem]
    simp (config := { decide := true }) only [arm64_norm, *]))

macro "fin3_step" : tactic =>
  `(tactic| (
    refine RunsTo.step (inst := ?inst) ?hrun ?hfetch ?_
    case hfetch => (
      (try simp (config := { decide := true }) only [arm64_norm, *])
      first
      | (refine libsignalSessionCode_fetch_rebase_text ?_ (by decide) (by decide)
         (try simp only [arm64_norm]) <;> rfl)
      | rfl)
    case hrun => (simp only [arm64_norm, *])
    try dsimp only [execInst, execAddSubImm, execAddSubExt, execAddSubShift, execAddSubCarry, execLogicalImm,
      execLogicalShift, execMoveWide, execBitfield, execCondSelect, execCondCompare,
      execDataProc1, execDataProc2, execDataProc3, execLdr, execLdrLit, execStr, execLdp, execStp,
      evalLogical, evalBitfield, evalAddrMode, AddrMode.baseReg, checkRegSPAligned,
      checkAddrSPAligned, MemWidth.isAligned, State.spAligned, extendVal, Reg.fromZRBits,
      Reg.fromSPBits]
    try simp (config := { decide := true }) only [arm64_norm, *]
    try arm64_discharge_perms_internal))

/-! ## 1. Generalized Multi-Block `HmacStN` and `hmacWith_pfx_short` -/

/-- The last message block of the inner hash after `nBlocks` 64-byte blocks (including the 64-byte
key block) and a tail `tail` of `< 56` bytes:
`tail ‖ 0x80 ‖ 0… ‖ BE64(8·(64·nBlocks + |tail|))`, 64 bytes. -/
def innerLastBlockN (nBlocks : ℕ) (tail : List (BitVec 8)) : List (BitVec 8) :=
  tail ++ [0x80] ++ List.replicate (55 - tail.length) 0 ++
    toBEBytes 8 (BitVec.ofNat 64 (8 * (64 * nBlocks + tail.length)))

theorem innerLastBlockN_one (msg : List (BitVec 8)) :
    innerLastBlockN 1 msg = innerLastBlock msg := by
  simp [innerLastBlockN, innerLastBlock]

theorem innerLastBlockN_length {nBlocks : ℕ} {tail : List (BitVec 8)} (hlt : tail.length < 56) :
    (innerLastBlockN nBlocks tail).length = 64 := by
  unfold innerLastBlockN
  simp [toBEBytes]
  omega

/-- Generalized `Hmac<Sha256>` (0x90 bytes) at `a`: MAC state of `key` after absorbing `pfx`
(a multiple of 64 bytes, already compressed into `a + 0x40`) and buffering `tail` (`|tail| < 64`). -/
def HmacStN (m : Memory) (a : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) : Prop :=
  pfx.length % 64 = 0 ∧
  tail.length < 64 ∧
  m.readBytes a tail.length = tail ∧
  m.read8 (a + 0x3f#64) = BitVec.ofNat 8 tail.length ∧
  m.readBytes (a + 0x40#64) 32 = shaStateBytes ((chunks64 pfx).foldl F (hmacInnerInit F key)) ∧
  m.read64 (a + 0x60#64) = BitVec.ofNat 64 (1 + pfx.length / 64) ∧
  m.readBytes (a + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key) ∧
  m.read64 (a + 0x88#64) = 1#64

theorem HmacStN.of_hmacSt {m : Memory} {a : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {key msg : List (BitVec 8)} (h : HmacSt m a F key msg) :
    HmacStN m a F key [] msg := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hchunks : chunks64 ([] : List (BitVec 8)) = [] := rfl
  refine ⟨by decide, h1, h2, h3, ?_, h5, h6, h7⟩
  simpa [hchunks] using h4

theorem HmacStN.to_hmacSt {m : Memory} {a : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {key msg : List (BitVec 8)} (h : HmacStN m a F key [] msg) :
    HmacSt m a F key msg := by
  rcases h with ⟨_, h1, h2, h3, h4, h5, h6, h7⟩
  have hchunks : chunks64 ([] : List (BitVec 8)) = [] := rfl
  refine ⟨h1, h2, h3, ?_, h5, h6, h7⟩
  simpa [hchunks] using h4

theorem HmacStN.of_agreesOutside {m₁ m₂ : Memory} {hm : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key pfx tail : List (BitVec 8)}
    {base : BitVec 64} {len : ℕ}
    (hst : HmacStN m₁ hm F key pfx tail)
    (hag : AgreesOutside m₁ m₂ base len)
    (hd : DisjointRegions base len hm 0x90) :
    HmacStN m₂ hm F key pfx tail := by
  rcases hst with ⟨hmod, hlen, hmsg, hpos, hin, hibl, hout, hobl⟩
  refine ⟨hmod, hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hm0 : tail.length = 0
    · simp [hm0] at hmsg ⊢; exact hmsg
    · have hd' : DisjointRegions base len hm tail.length :=
        hd.sub_right hm ⟨by omega, by simp; omega⟩
      exact (hag.readBytes_eq hd' (by omega)).trans hmsg
  · have hout8 : OutsideRegion base len (hm + 0x3f#64) := by
      rcases hd with ⟨hd1, hd2⟩
      unfold OutsideRegion; bv_omega
    exact (hag.1 _ hout8).trans hpos
  · have hd' : DisjointRegions base len (hm + 0x40#64) 32 :=
      hd.sub_right (hm + 0x40#64) ⟨by decide, by bv_omega⟩
    exact (hag.readBytes_eq hd' (by decide)).trans hin
  · have hd' : DisjointRegions base len (hm + 0x60#64) 8 :=
      hd.sub_right (hm + 0x60#64) ⟨by decide, by bv_omega⟩
    exact (hag.read64_eq hd').trans hibl
  · have hd' : DisjointRegions base len (hm + 0x68#64) 32 :=
      hd.sub_right (hm + 0x68#64) ⟨by decide, by bv_omega⟩
    exact (hag.readBytes_eq hd' (by decide)).trans hout
  · have hd' : DisjointRegions base len (hm + 0x88#64) 8 :=
      hd.sub_right (hm + 0x88#64) ⟨by decide, by bv_omega⟩
    exact (hag.read64_eq hd').trans hobl

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

theorem bit_len_innerN_eq {b n : ℕ} (hn : n < 56) :
    (BitVec.ofNat 64 b <<< 9#64) ||| (BitVec.ofNat 64 n <<< 3#64) =
      BitVec.ofNat 64 (8 * (64 * b + n)) ∧
    (BitVec.ofNat 64 b <<< 9) ||| (BitVec.ofNat 64 n <<< 3) =
      BitVec.ofNat 64 (8 * (64 * b + n)) := by
  have hp : n < 64 := by omega
  have h : (BitVec.ofNat 64 b <<< 9) ||| (BitVec.ofNat 64 n <<< 3) =
      BitVec.ofNat 64 (8 * (64 * b + n)) := by
    rw [← BitVec.add_eq_or_of_and_eq_zero _ _ (bitlen_and_zero b n hp),
      BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow]
    have hdiv : 8 * (64 * b + n) = b * 512 + n * 8 := by omega
    rw [hdiv, BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_mul]
    rfl
  exact ⟨h, h⟩

/-- HMAC with a 64-byte-aligned prefix `pfx` and short tail `tail` (`|tail| < 56`). -/
theorem hmacWith_pfx_short (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8))
    (hk : key.length ≤ 64) (hpfx : pfx.length % 64 = 0) (htail : tail.length < 56) :
    hmacWith F key (pfx ++ tail) =
      digestBytes (F (hmacOuterInit F key)
        (outerBlock (digestBytes (F ((chunks64 pfx).foldl F (hmacInnerInit F key))
          (innerLastBlockN (1 + pfx.length / 64) tail))))) := by
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
  have hinner_blk_len : (innerLastBlockN nB tail).length = 64 :=
    innerLastBlockN_length htail
  have hinner_pad : sha256Pad (ipad ++ (pfx ++ tail)) =
      ipad ++ (pfx ++ innerLastBlockN nB tail) := by
    unfold sha256Pad innerLastBlockN
    have hlen : (ipad ++ (pfx ++ tail)).length = 64 * nB + tail.length := by
      simp [hipad_len, nB]; omega
    have hmod : (119 - (64 * nB + tail.length) % 64) % 64 = 55 - tail.length := by omega
    rw [hlen, hmod]
    simp only [List.append_assoc]
  have hinner : sha256With F (ipad ++ (pfx ++ tail)) =
      digestBytes (F ((chunks64 pfx).foldl F (hmacInnerInit F key))
        (innerLastBlockN nB tail)) := by
    unfold sha256With digestBytes
    rw [hinner_pad, chunks64_append_64 hipad_len, chunks64_append_mul hpfx,
      chunks64_single hinner_blk_len, List.foldl_cons, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    rfl
  rw [hinner]
  set d := digestBytes (F ((chunks64 pfx).foldl F (hmacInnerInit F key)) (innerLastBlockN nB tail))
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

/-! ## 2. `FinPre3Pfx` / `FinPre3` and Segment Proofs for `finalize_fixed [local#3]` (`0x6ce50 .. 0x6d00c`) -/

/-- Bundled preconditions of `finalize_fixed [local#3]` (`0x6ce50`) with a 64-byte-aligned prefix `pfx`
and tail `tail` (`|tail| < 56`). -/
structure FinPre3Pfx (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 : State) : Prop where
  pc_eq        : s0.pc = b + 0x67a58#64
  status       : s0.status = .Running
  key_le       : key.length ≤ 64
  tail_lt      : tail.length < 56
  hmac_st      : HmacStN s0.mem (s0.readReg64 .x1) F key pfx tail
  rw_out       : RW s0.mem (s0.readReg64 .x0) 32
  rw_hm        : RW s0.mem (s0.readReg64 .x1) 0x90
  rw_fsp       : RW s0.mem (s0.sp - 144#64) 144
  disj_out_hm  : DisjointRegions (s0.readReg64 .x0) 32 (s0.readReg64 .x1) 0x90
  disj_out_fsp : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64) 144
  disj_hm_fsp  : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64) 144
  sp_aligned   : (s0.sp &&& 0b1111#64) = 0#64

/-- Single-block (`pfx = []`) bundled preconditions of `finalize_fixed [local#3]` (`0x6ce50`). -/
structure FinPre3 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 : State) : Prop where
  pc_eq        : s0.pc = b + 0x67a58#64
  status       : s0.status = .Running
  key_le       : key.length ≤ 64
  msg_lt       : msg.length < 56
  hmac_st      : HmacSt s0.mem (s0.readReg64 .x1) F key msg
  rw_out       : RW s0.mem (s0.readReg64 .x0) 32
  rw_hm        : RW s0.mem (s0.readReg64 .x1) 0x90
  rw_fsp       : RW s0.mem (s0.sp - 144#64) 144
  disj_out_hm  : DisjointRegions (s0.readReg64 .x0) 32 (s0.readReg64 .x1) 0x90
  disj_out_fsp : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64) 144
  disj_hm_fsp  : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64) 144
  sp_aligned   : (s0.sp &&& 0b1111#64) = 0#64

theorem FinPre3.to_pfx {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {key msg : List (BitVec 8)} {s0 : State} (h : FinPre3 b F key msg s0) :
    FinPre3Pfx b F key [] msg s0 :=
  { pc_eq := h.pc_eq
    status := h.status
    key_le := h.key_le
    tail_lt := h.msg_lt
    hmac_st := HmacStN.of_hmacSt h.hmac_st
    rw_out := h.rw_out
    rw_hm := h.rw_hm
    rw_fsp := h.rw_fsp
    disj_out_hm := h.disj_out_hm
    disj_out_fsp := h.disj_out_fsp
    disj_hm_fsp := h.disj_hm_fsp
    sp_aligned := h.sp_aligned }

namespace FinalizeFixed3Proof

open FinalizeFixedProof (FinCommon FinPost)

variable {C : Crypto} {ext : String → Option (State → State)}

/-- Cut `F0p` at `b + 0x6ce6c` (7 steps after entry): prologue complete. -/
private structure StateF0p (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x67a74#64
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x0
  x1_eq   : s.readReg64 .x1 = s0.readReg64 .x1
  hmac_st : HmacStN s.mem (s0.readReg64 .x1) F key pfx tail

set_option hygiene false in
local macro "seg1a_body" : tactic => `(tactic| (
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
      (s0.sp - 144#64) 144 := by
    agrees_outside_writes
  refine
    { pc_eq := by fin3_reg
      common :=
        { status := by fin3_reg
          sp_eq := by fin3_reg
          x29_eq := by fin3_reg
          x26_eq := by fin3_reg
          x27_eq := by fin3_reg
          x28_eq := by fin3_reg
          saved := ⟨by solve_fin3_saved, by solve_fin3_saved, by solve_fin3_saved,
                    by solve_fin3_saved, by solve_fin3_saved, by solve_fin3_saved,
                    by solve_fin3_saved, by solve_fin3_saved, by solve_fin3_saved⟩
          frame := by rw [mem_setMem]; exact Frame.trans_agreesOutside (Frame.refl s0.mem _) (by simp) hag }
      x0_eq := by fin3_reg
      x1_eq := by fin3_reg
      hmac_st := by rw [mem_setMem]; exact HmacStN.of_agreesOutside hpre.hmac_st hag hpre.disj_hm_fsp.symm }))

set_option maxHeartbeats 1600000 in
private theorem seg1a_runsTo [HkdfHooks C.F ext] {b : BitVec 64} {key pfx tail : List (BitVec 8)} {s0 : State}
    (hpre : FinPre3Pfx b C.F key pfx tail s0) :
    RunsTo (tripleRatchetProgAtExt b ext) s0 (StateF0p b C.F key pfx tail s0) := by
  seg1a_body

/-- Cut `F1` at `b + 0x6ce9c` (after `memsetHook`): buffer `hm[0..64]` holds `tail ++ [0x80] ++ 0…0`. -/
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
  buf_eq  : s.mem.readBytes (s0.readReg64 .x1) 64 =
    tail ++ [0x80#8] ++ List.replicate (63 - tail.length) 0#8
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes ((chunks64 pfx).foldl F (hmacInnerInit F key))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

set_option hygiene false in
local macro "seg1b_body" memsetStep:term:max lrTerm:term:max : tactic => `(tactic| (
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
    have := hpre.tail_lt
    bv_omega
  refine $memsetStep
    hstat rfl
    ((by simp only [arm64_norm]) : _ = s0.readReg64 .x1 + BitVec.ofNat 64 tail.length + 1#64)
    (by simp (config := { decide := true }) only [arm64_norm]) htoNat_sub (rfl : _ = $lrTerm) hrw_memset ?_
  refine RunsTo.refl ?_
  have hag := agreesOutside_pad_memset s.mem (s0.readReg64 .x1) tail hpre.tail_lt
  have hd_hm64_fsp : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := by fin3_reg
      common :=
        { status := by fin3_reg
          sp_eq := by fin3_reg
          x29_eq := by fin3_reg
          x26_eq := by fin3_reg
          x27_eq := by fin3_reg
          x28_eq := by fin3_reg
          saved := FinSaved.of_agreesOutside hsaved hag hd_hm64_fsp
          frame := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag }
      x19_eq := by fin3_reg
      x20_eq := by fin3_reg
      x21_eq := by fin3_reg
      x22_eq := by fin3_reg
      x23_eq := by fin3_reg
      x24_eq := by fin3_reg
      x25_eq := by fin3_reg
      buf_eq := readBytes_64_after_pad_memset s.mem (s0.readReg64 .x1) tail hmsg_eq hpre.tail_lt
      ist_eq := (hag.readBytes_eq hd_hm64_ist (by decide)).trans hin_eq
      ost_eq := (hag.readBytes_eq hd_hm64_ost (by decide)).trans hout_eq
      obl_eq := (hag.read64_eq hd_hm64_obl).trans hobl_eq }))

set_option maxHeartbeats 1600000 in
private theorem seg1b_runsTo [HkdfHooks C.F ext] {b : BitVec 64} {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx b C.F key pfx tail s0)
    (hs : StateF0p b C.F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateF1 b C.F key pfx tail s0) := by
  seg1b_body (s2_memset_step_ext b C ext) (b + 0x67aa4#64)

/-- Cut `F2` at `b + 0x6cf00` (right before inner `bl compress256`). -/
private structure StateF2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
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
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 = innerLastBlockN (1 + pfx.length / 64) tail
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes ((chunks64 pfx).foldl F (hmacInnerInit F key))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

/-- Cut `F3` at `b + 0x6cf04` (after inner `compress256Hook`). -/
private structure StateF3 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x67b0c#64
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes (F ((chunks64 pfx).foldl F (hmacInnerInit F key))
      (innerLastBlockN (1 + pfx.length / 64) tail))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private theorem finSaved_seg2a {s0 : State} {m1 m2 m3 m4 : Memory} {hm fsp : BitVec 64}
    (hs : FinSaved s0 fsp m1) (hag1 : AgreesOutside m1 m2 fsp 64)
    (hag2 : AgreesOutside m2 m3 hm 64) (hag3 : AgreesOutside m3 m4 fsp 64)
    (hd_fsp : DisjointRegions fsp 64 (fsp + 0x40#64) 0x50)
    (hd_hm : DisjointRegions hm 64 (fsp + 0x40#64) 0x50) :
    FinSaved s0 fsp m4 :=
  FinSaved.of_agreesOutside
    (FinSaved.of_agreesOutside (FinSaved.of_agreesOutside hs hag1 hd_fsp) hag2 hd_hm) hag3 hd_fsp

set_option hygiene false in
local macro "seg2a_body" : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hult_7 := ult_7_of_lt_56 hpre.tail_lt
  obtain ⟨hbit_len1, hbit_len2⟩ := bit_len_innerN_eq (b := 1 + pfx.length / 64) hpre.tail_lt
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  iterate 6 fin3_step
  have hread32 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 32#64 (by decide) hd_hm64_fsp64
  have hread40 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 40#64 (by decide) hd_hm64_fsp64
  have hread48 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 48#64 (by decide) hd_hm64_fsp64
  iterate 7 fin3_step
  clear hread32 hread40 hread48
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3⟩ := agreesOutside_seg2a s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
    _ _ _ _ _ _ _ _ _
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
  refine
    { pc_eq := by fin3_reg
      common :=
        { status := by fin3_reg, sp_eq := by fin3_reg, x29_eq := by fin3_reg,
          x26_eq := by fin3_reg, x27_eq := by fin3_reg, x28_eq := by fin3_reg,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg2a hsaved hag1 hag2 hag3 hd_fsp64_saved hd_hm64_saved
          frame := by rw [mem_setMem]; exact frame_seg2a hframe hag1 hag2 hag3 }
      x0_eq := by fin3_reg, x1_eq := by fin3_reg, x2_eq := by fin3_reg,
      x19_eq := by fin3_reg, x20_eq := by fin3_reg, x21_eq := by fin3_reg, x22_eq := by fin3_reg
      blk_eq := by
        rw [mem_setMem]
        refine (readBytes_fsp_64_seg2 _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
        rw [toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
            toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_rev64,
            readBytes_56_eq_append_8 s.mem (s0.readReg64 .x1),
            readBytes_56_of_buf_eq s.mem (s0.readReg64 .x1) tail hbuf hpre.tail_lt]
        rfl
      ist_eq := by
        rw [mem_setMem]
        exact (hag3.readBytes_eq hd_fsp64_ist (by decide)).trans
          ((hag2.readBytes_eq hd_hm64_ist (by decide)).trans
            ((hag1.readBytes_eq hd_fsp64_ist (by decide)).trans hist))
      ost_eq := by
        rw [mem_setMem]
        exact (hag3.readBytes_eq hd_fsp64_ost (by decide)).trans
          ((hag2.readBytes_eq hd_hm64_ost (by decide)).trans
            ((hag1.readBytes_eq hd_fsp64_ost (by decide)).trans host))
      obl_eq := by
        rw [mem_setMem]
        exact (hag3.read64_eq hd_fsp64_obl).trans
          ((hag2.read64_eq hd_hm64_obl).trans
            ((hag1.read64_eq hd_fsp64_obl).trans hobl)) }))

set_option maxHeartbeats 1600000 in
private theorem seg2a_runsTo [HkdfHooks C.F ext] {b : BitVec 64} {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx b C.F key pfx tail s0)
    (hs : StateF1 b C.F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateF2 b C.F key pfx tail s0) := by
  seg2a_body

set_option hygiene false in
local macro "seg2b_body" compStep:term:max lrTerm:term:max : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hblk, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_ist : s.mem.RW (s0.readReg64 .x1 + 0x40#64) 32 := hrw_hm.sub (by bv_omega)
  fin3_step
  refine $compStep
    hstat rfl
    (by fin3_reg) (by fin3_reg) (by fin3_reg) (rfl : _ = $lrTerm)
    hist hblk (innerLastBlockN_length hpre.tail_lt) hrw_ist ?_
  refine RunsTo.refl ?_
  set blk_in := shaStateBytes (C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key))
    (innerLastBlockN (1 + pfx.length / 64) tail))
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x40#64) blk_in)
      (s0.readReg64 .x1 + 0x40#64) 32 := by
    have hlen : blk_in.length = 32 := shaStateBytes_length _
    rw [← hlen]
    exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_in
  have hd_ist_saved : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_ist_ost : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_ist_obl : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := by fin3_reg
      common :=
        { status := by fin3_reg, sp_eq := by fin3_reg, x29_eq := by fin3_reg,
          x26_eq := by fin3_reg, x27_eq := by fin3_reg, x28_eq := by fin3_reg,
          saved := FinSaved.of_agreesOutside hsaved hag_comp hd_ist_saved
          frame := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin3_reg, x20_eq := by fin3_reg, x21_eq := by fin3_reg, x22_eq := by fin3_reg
      ist_eq := by
        have hlen : blk_in.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact Bytes.readBytes_writeBytes_same s.mem _ blk_in (by rw [hlen]; decide)
      ost_eq := (hag_comp.readBytes_eq hd_ist_ost (by decide)).trans host
      obl_eq := (hag_comp.read64_eq hd_ist_obl).trans hobl }))

set_option maxHeartbeats 1600000 in
private theorem seg2b_runsTo [HkdfHooks C.F ext] {b : BitVec 64} {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx b C.F key pfx tail s0)
    (hs : StateF2 b C.F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateF3 b C.F key pfx tail s0) := by
  seg2b_body (s2_compress256_step_ext b C ext) (b + 0x67b0c#64)

/-- Cut `F3b` at `b + 0x6cf80` (right before outer `bl compress256`). -/
private structure StateF3b (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x67b88#64
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 =
    outerBlock (digestBytes (F ((chunks64 pfx).foldl F (hmacInnerInit F key))
      (innerLastBlockN (1 + pfx.length / 64) tail)))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)

/-- Cut `F4` at `b + 0x6cf84` (after outer `compress256Hook`). -/
private structure StateF4 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x67b8c#64
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 =
    shaStateBytes (F (hmacOuterInit F key)
      (outerBlock (digestBytes (F ((chunks64 pfx).foldl F (hmacInnerInit F key))
        (innerLastBlockN (1 + pfx.length / 64) tail)))))

set_option hygiene false in
local macro "seg3a_body" : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_in := C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key))
    (innerLastBlockN (1 + pfx.length / 64) tail)
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
  refine
    { pc_eq := by fin3_reg
      common :=
        { status := by fin3_reg, sp_eq := by fin3_reg, x29_eq := by fin3_reg,
          x26_eq := by fin3_reg, x27_eq := by fin3_reg, x28_eq := by fin3_reg,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg3a hsaved hag1 hag2 hag3 hag4 hd_hm64_saved hd_fsp64_saved
          frame := by rw [mem_setMem]; exact frame_seg3a hframe hag1 hag2 hag3 hag4 }
      x0_eq := by fin3_reg, x1_eq := by fin3_reg, x2_eq := by fin3_reg,
      x19_eq := by fin3_reg, x20_eq := by fin3_reg
      blk_eq := by
        rw [mem_setMem]
        refine (readBytes_fsp_64_seg3 _ _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
        rw [toLEBytes_8_rev32_append, toLEBytes_8_rev32_append,
            toLEBytes_8_rev32_append, toLEBytes_8_rev32_append]
        have htail : toLEBytes 8 0x80#64 ++ toLEBytes 8 0#64 ++ toLEBytes 8 0#64 ++
            toLEBytes 8 (rev64 768#64) =
            [0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 768#64 := by decide
        unfold outerBlock
        rw [digestBytes_eq_append h_in]
        simp only [List.append_assoc] at htail ⊢
        rw [htail]; rfl
      ost_eq := by
        rw [mem_setMem]
        exact ost_eq_seg3a host hag1 hag2 hag3 hag4 hd_hm64_ost hd_fsp64_ost }))

set_option maxHeartbeats 1600000 in
private theorem seg3a_runsTo [HkdfHooks C.F ext] {b : BitVec 64} {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx b C.F key pfx tail s0)
    (hs : StateF3 b C.F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateF3b b C.F key pfx tail s0) := by
  seg3a_body

set_option hygiene false in
local macro "seg3b_body" compStep:term:max lrTerm:term:max : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hblk, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_ost : s.mem.RW (s0.readReg64 .x1 + 0x68#64) 32 := hrw_hm.sub (by bv_omega)
  set h_in := C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key))
    (innerLastBlockN (1 + pfx.length / 64) tail)
  fin3_step
  refine $compStep
    hstat rfl
    (by fin3_reg) (by fin3_reg) (by fin3_reg) (rfl : _ = $lrTerm)
    host hblk (outerBlock_digestBytes_length h_in) hrw_ost ?_
  refine RunsTo.refl ?_
  set blk_out := shaStateBytes (C.F (hmacOuterInit C.F key) (outerBlock (digestBytes h_in)))
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x68#64) blk_out)
      (s0.readReg64 .x1 + 0x68#64) 32 := by
    have hlen : blk_out.length = 32 := shaStateBytes_length _
    rw [← hlen]
    exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_out
  have hd_ost_saved : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  refine
    { pc_eq := by fin3_reg
      common :=
        { status := by fin3_reg, sp_eq := by fin3_reg, x29_eq := by fin3_reg,
          x26_eq := by fin3_reg, x27_eq := by fin3_reg, x28_eq := by fin3_reg,
          saved := FinSaved.of_agreesOutside hsaved hag_comp hd_ost_saved
          frame := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin3_reg, x20_eq := by fin3_reg
      ost_eq := by
        have hlen : blk_out.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact Bytes.readBytes_writeBytes_same s.mem _ blk_out (by rw [hlen]; decide) }))

set_option maxHeartbeats 1600000 in
private theorem seg3b_runsTo [HkdfHooks C.F ext] {b : BitVec 64} {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx b C.F key pfx tail s0)
    (hs : StateF3b b C.F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateF4 b C.F key pfx tail s0) := by
  seg3b_body (s2_compress256_step_ext b C ext) (b + 0x67b8c#64)

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
  have hag_63 : AgreesOutside m (m.write8 (hm + 63#64) 0#8) (hm + 63#64) 1 := by
    agrees_outside_writes
  rcases hoff with rfl | rfl <;>
    rw [hag_fsp.read32_eq (hd.sub_right _ ⟨by decide, by bv_omega⟩),
        hag_63.read32_eq (by unfold DisjointRegions; bv_omega), hw]

private theorem seg4a_disj {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {key pfx tail : List (BitVec 8)} {s0 : State} (hpre : FinPre3Pfx b F key pfx tail s0) :
    DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1) 0x90 ∧
    DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64 + 0x40#64) 0x50 ∧
    DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 ∧
    DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
  ⟨hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩,
   hpre.disj_hm_fsp.sub_right _ ⟨by decide, by bv_omega⟩,
   by unfold DisjointRegions; bv_omega,
   hpre.disj_out_fsp.sub_right _ ⟨by decide, by bv_omega⟩⟩

@[local simp, local arm64_norm]
private theorem extractLsb'_0_64_zero128 : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl

@[local simp, local arm64_norm]
private theorem extractLsb'_64_64_zero128 : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl

set_option hygiene false in
local macro "seg4a_body" : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx19, hx20, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 32 := rw_of_perm_eq hframe.2 hpre.rw_out
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_out := C.F (hmacOuterInit C.F key)
    (outerBlock (digestBytes (C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key))
      (innerLastBlockN (1 + pfx.length / 64) tail))))
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
  refine
    { pc_eq := by fin3_reg
      common :=
        { status := by fin3_reg, sp_eq := by fin3_reg, x29_eq := by fin3_reg,
          x26_eq := by fin3_reg, x27_eq := by fin3_reg, x28_eq := by fin3_reg,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg4a hsaved hag1 hag2 hag3 hag4 hd_hm_saved hd_fsp64_saved hd_out_saved
          frame := by rw [mem_setMem]; exact frame_seg4a hframe hag1 hag2 hag3 hag4 }
      out_eq := by
        rw [mem_setMem]
        exact (readBytes_write32_8_digestBytes _ (s0.readReg64 .x0) h_out _ _ _ _ _ _ _ _
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)).trans
          (hmacWith_pfx_short C.F key pfx tail hpre.key_le hpre.hmac_st.1 hpre.tail_lt).symm }))

set_option maxHeartbeats 1600000 in
private theorem seg4a_runsTo [HkdfHooks C.F ext] {b : BitVec 64} {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx b C.F key pfx tail s0)
    (hs : StateF4 b C.F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateF5 b C.F key pfx tail s0) := by
  seg4a_body

set_option hygiene false in
local macro "seg4b_body" : tactic => `(tactic| (
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
private theorem seg4b_runsTo [HkdfHooks C.F ext] {b : BitVec 64} {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx b C.F key pfx tail s0)
    (hs : StateF5 b C.F key pfx tail s0 s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (FinPost C.F key (pfx ++ tail) s0) := by
  seg4b_body

/-- Full multi-block `RunsTo` contract of `finalize_fixed [local#3]` (`0x6ce50 → s0.readReg64 .lr`)
on `tripleRatchetProgAtExt b ext`. -/
theorem finalize_fixed3_pfx_runsTo_ext [HkdfHooks C.F ext] {b : BitVec 64}
    {key pfx tail : List (BitVec 8)} {s0 : State}
    (hpre : FinPre3Pfx b C.F key pfx tail s0) :
    RunsTo (tripleRatchetProgAtExt b ext) s0 (FinPost C.F key (pfx ++ tail) s0) :=
  (seg1a_runsTo hpre).trans fun _ hs1 =>
  (seg1b_runsTo hpre hs1).trans fun _ hs2 =>
  (seg2a_runsTo hpre hs2).trans fun _ hs3 =>
  (seg2b_runsTo hpre hs3).trans fun _ hs4 =>
  (seg3a_runsTo hpre hs4).trans fun _ hs5 =>
  (seg3b_runsTo hpre hs5).trans fun _ hs6 =>
  (seg4a_runsTo hpre hs6).trans fun _ hs7 =>
  seg4b_runsTo hpre hs7

/-- Single-block (`pfx = []`) `RunsTo` contract of `finalize_fixed [local#3]`
(`0x6ce50 → s0.readReg64 .lr`) on `tripleRatchetProgAtExt b ext`. -/
theorem finalize_fixed3_runsTo_ext [HkdfHooks C.F ext] {b : BitVec 64}
    {key msg : List (BitVec 8)} {s0 : State}
    (hpre : FinPre3 b C.F key msg s0) :
    RunsTo (tripleRatchetProgAtExt b ext) s0 (FinPost C.F key msg s0) :=
  @finalize_fixed3_pfx_runsTo_ext C ext _ b key [] msg s0 hpre.to_pfx

section Placed

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {H : LibsignalHooks} [HkdfPlacedHooks C.F H]

theorem s2_memset_step_425 (C : Crypto) (H : LibsignalHooks) [HkdfPlacedHooks C.F H]
    {s₀ s : State} {Q : State → Prop} {dst lr : BitVec 64} {len : ℕ}
    (hrun : s.status = .Running) (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : (s.readReg64 .x1).truncate 8 = 0#8)
    (hx2 : (s.readReg64 .x2).toNat = len) (hlr : s.readReg64 .lr = lr) (hrw : s.mem.RW dst len)
    (h : RunsToFrom ((blkPC_425).rebase (blkPl_425).base H) s₀
      ((s.setMem (s.mem.writeBytes dst (List.replicate len 0#8))).setPC lr) Q) :
    RunsToFrom ((blkPC_425).rebase (blkPl_425).base H) s₀ s Q :=
  s2_memset_step_placed C H hrun hpc hx0 hx1 hx2 hlr hrw h

theorem s2_compress256_step_425 (C : Crypto) (H : LibsignalHooks) [HkdfPlacedHooks C.F H]
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running) (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr) (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64) (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st) (hblk : s.mem.readBytes blkPtr 64 = blk)
    (hlen : blk.length = 64) (hrw : s.mem.RW stPtr 32)
    (h : RunsToFrom ((blkPC_425).rebase (blkPl_425).base H) s₀
      ((s.setMem (s.mem.writeBytes stPtr (shaStateBytes (C.F st blk)))).setPC lr) Q) :
    RunsToFrom ((blkPC_425).rebase (blkPl_425).base H) s₀ s Q :=
  s2_compress256_step_placed C H hrun hpc hx0 hx1 hx2 hlr hst hblk hlen hrw h

set_option maxHeartbeats 1600000 in
private theorem seg1a_placed_runsTo {key pfx tail : List (BitVec 8)} {s0 : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s0 (StateF0p fin3PlacedFakeB C.F key pfx tail s0) := by
  seg1a_body

set_option maxHeartbeats 1600000 in
private theorem seg1b_placed_runsTo {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF0p fin3PlacedFakeB C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF1 fin3PlacedFakeB C.F key pfx tail s0) := by
  seg1b_body (s2_memset_step_425 C H) ((blkPl_425).base + 76#64)

set_option maxHeartbeats 1600000 in
private theorem seg2a_placed_runsTo {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF1 fin3PlacedFakeB C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF2 fin3PlacedFakeB C.F key pfx tail s0) := by
  seg2a_body

set_option maxHeartbeats 1600000 in
private theorem seg2b_placed_runsTo {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF2 fin3PlacedFakeB C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF3 fin3PlacedFakeB C.F key pfx tail s0) := by
  seg2b_body (s2_compress256_step_425 C H) ((blkPl_425).base + 180#64)

set_option maxHeartbeats 1600000 in
private theorem seg3a_placed_runsTo {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF3 fin3PlacedFakeB C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF3b fin3PlacedFakeB C.F key pfx tail s0) := by
  seg3a_body

set_option maxHeartbeats 1600000 in
private theorem seg3b_placed_runsTo {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF3b fin3PlacedFakeB C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF4 fin3PlacedFakeB C.F key pfx tail s0) := by
  seg3b_body (s2_compress256_step_425 C H) ((blkPl_425).base + 308#64)

set_option maxHeartbeats 1600000 in
private theorem seg4a_placed_runsTo {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF4 fin3PlacedFakeB C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF5 fin3PlacedFakeB C.F key pfx tail s0) := by
  seg4a_body

set_option maxHeartbeats 1600000 in
private theorem seg4b_placed_runsTo {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF5 fin3PlacedFakeB C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (FinPost C.F key (pfx ++ tail) s0) := by
  seg4b_body

theorem finalize_fixed3_pfx_placed_runsTo {key pfx tail : List (BitVec 8)} {s0 : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s0 (FinPost C.F key (pfx ++ tail) s0) :=
  (seg1a_placed_runsTo hpre).trans fun _ hs1 =>
  (seg1b_placed_runsTo hpre hs1).trans fun _ hs2 =>
  (seg2a_placed_runsTo hpre hs2).trans fun _ hs3 =>
  (seg2b_placed_runsTo hpre hs3).trans fun _ hs4 =>
  (seg3a_placed_runsTo hpre hs4).trans fun _ hs5 =>
  (seg3b_placed_runsTo hpre hs5).trans fun _ hs6 =>
  (seg4a_placed_runsTo hpre hs6).trans fun _ hs7 =>
  seg4b_placed_runsTo hpre hs7

theorem finalize_fixed3_placed_runsTo {key msg : List (BitVec 8)} {s0 : State}
    (hpre : FinPre3 fin3PlacedFakeB C.F key msg s0) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s0 (FinPost C.F key msg s0) :=
  @finalize_fixed3_pfx_placed_runsTo C _ H _ key [] msg s0 hpre.to_pfx

theorem finalize_fixed3_pfx_placed_runsTo_of_other_block {callerProg : Program} {i : Nat}
    [hcaller : IsLsBlockProg callerProg i H]
    {key pfx tail : List (BitVec 8)} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0)
    (hi : i < 619 := by decide) :
    RunsTo callerProg s0 (FinPost C.F key (pfx ++ tail) s0) :=
  RunsTo.of_other_block hcl (finalize_fixed3_pfx_placed_runsTo hpre) hi (by decide) (by decide)

theorem finalize_fixed3_placed_runsTo_of_other_block {callerProg : Program} {i : Nat}
    [hcaller : IsLsBlockProg callerProg i H]
    {key msg : List (BitVec 8)} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpre : FinPre3 fin3PlacedFakeB C.F key msg s0)
    (hi : i < 619 := by decide) :
    RunsTo callerProg s0 (FinPost C.F key msg s0) :=
  RunsTo.of_other_block hcl (finalize_fixed3_placed_runsTo hpre) hi (by decide) (by decide)

end Placed

end FinalizeFixed3Proof

/-! ## 3. Separation-Logic Contract (`FinalizeFixed3OkExt`, `FinalizeFixed3PlacedOk`) -/

set_option hygiene false in
local macro "finalize_fixed3_ok_body" fakeB:term:max runsToLem:term:max : tactic => `(tactic| (
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  rw [finalizeFixedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hkey_le, hmsg_lt⟩, hsep⟩
  have hmsg_lt64 : x.msg.length < 64 := by omega
  have hb_out := IsBlock.memRegion x.out 32
  have hb_hm := isBlock_hmacCoreAt C.F x.hm x.key x.msg hmsg_lt64
  have hb_stk := IsBlock.memRegion (s0.sp - 144#64) 144
  change s0.mem ⊨
    (memRegion x.out 32 ∗ hmacCoreAt C.F x.hm x.key x.msg ∗ memRegion (s0.sp - 144#64) 144) ∗ R at hsep
  have hsep_out : s0.mem ⊨ memRegion x.out 32 ∗
      (hmacCoreAt C.F x.hm x.key x.msg ∗ (memRegion (s0.sp - 144#64) 144 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_out_stk : s0.mem ⊨ memRegion x.out 32 ∗
      (memRegion (s0.sp - 144#64) 144 ∗ (hmacCoreAt C.F x.hm x.key x.msg ∗ R)) := by ac_nf at hsep ⊢
  have hsep_hm : s0.mem ⊨ hmacCoreAt C.F x.hm x.key x.msg ∗
      (memRegion x.out 32 ∗ (memRegion (s0.sp - 144#64) 144 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 144#64) 144 ∗
      (memRegion x.out 32 ∗ (hmacCoreAt C.F x.hm x.key x.msg ∗ R)) := by ac_nf at hsep ⊢
  have hsep_hm_stk : s0.mem ⊨ hmacCoreAt C.F x.hm x.key x.msg ∗
      (memRegion (s0.sp - 144#64) 144 ∗ (memRegion x.out 32 ∗ R)) := by ac_nf at hsep ⊢
  have hhmac_st : HmacSt s0.mem x.hm C.F x.key x.msg := hb_hm.read hsep_hm
  have hrw_out : RW s0.mem x.out 32 := fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_hm : RW s0.mem x.hm 0x90 := fun a ha => hb_hm.permNoLazy_rw hsep_hm ha
  have hrw_stk : RW s0.mem (s0.sp - 144#64) 144 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hd_out_hm : DisjointRegions x.out 32 x.hm 0x90 :=
    hb_out.disjoint hb_hm (by decide) (by decide) hsep_out
  have hd_out_stk : DisjointRegions x.out 32 (s0.sp - 144#64) 144 :=
    hb_out.disjoint hb_stk (by decide) (by decide) hsep_out_stk
  have hd_hm_stk : DisjointRegions x.hm 0x90 (s0.sp - 144#64) 144 :=
    hb_hm.disjoint hb_stk (by decide) (by decide) hsep_hm_stk
  have hfin_pre : FinPre3 $fakeB C.F x.key x.msg s0 :=
    { pc_eq := by simp only [arm64_norm, hpc]
      status := hrun
      key_le := hkey_le
      msg_lt := hmsg_lt
      hmac_st := by rw [hx1]; exact hhmac_st
      rw_out := by rw [hx0]; exact hrw_out
      rw_hm := by rw [hx1]; exact hrw_hm
      rw_fsp := hrw_stk
      disj_out_hm := by rw [hx0, hx1]; exact hd_out_hm
      disj_out_fsp := by rw [hx0]; exact hd_out_stk
      disj_hm_fsp := by rw [hx1]; exact hd_hm_stk
      sp_aligned := by simpa [State.spAligned] using hsp }
  refine ($runsToLem hfin_pre).to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hout_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  rw [finalizeFixedSpec]
  dsimp only []
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  rw [hx0] at hout_sf
  rw [hx0, hx1] at hframe_sf
  have hb_out' := IsBlock.pointsToBytes_len (a := x.out) (length_hmacWith C.F x.key x.msg)
  have hb_hm' := IsBlock.memRegion x.hm 0x90
  have hpost_sep : sf.mem ⊨ (x.out ↦ₛ hmacWith C.F x.key x.msg) ∗
      (memRegion x.hm 0x90 ∗ (memRegion (s0.sp - 144#64) 144 ∗ R)) :=
    Frame.update_three_blocks hb_out hb_out' hb_hm hb_hm' hb_stk hb_stk hsep_out hframe_sf
      ⟨by rw [length_hmacWith]; decide, by rwa [length_hmacWith]⟩ trivial trivial
  change sf.mem ⊨
    ((x.out ↦ₛ hmacWith C.F x.key x.msg) ∗ memRegion x.hm 0x90 ∗ memRegion (s0.sp - 144#64) 144) ∗ R
  ac_nf at hpost_sep ⊢))

/-- `<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#3]` (`0x67974`)
meets `finalizeFixedSpec C.F` on `tripleRatchetProgAtExt b ext`. -/
def FinalizeFixed3OkExt (b : BitVec 64) (C : Crypto)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr finalizeFixed3Name)
    (finalizeFixedSpec C.F)

theorem finalize_fixed3_ok_ext (b : BitVec 64) (C : Crypto)
    (ext : String → Option (State → State)) [HkdfHooks C.F ext] :
    FinalizeFixed3OkExt b C ext := by
  unfold FinalizeFixed3OkExt
  have hfn : (tripleRatchetProgAtExt b ext).fnAddr finalizeFixed3Name = b + 0x67a58#64 := by
    unfold tripleRatchetProgAtExt finalizeFixed3Name
    rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x67a58]
  rw [hfn]
  finalize_fixed3_ok_body b (FinalizeFixed3Proof.finalize_fixed3_runsTo_ext (ext := ext))

/-- Relocatable `subroutine_ok` contract for `finalize_fixed [local#3]` (Block `425`)
on `(blkPC_425).rebase (blkPl_425).base H`. -/
def FinalizeFixed3PlacedOk [LibsignalPlacement] (C : Crypto) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_425).rebase (blkPl_425).base H) (blkPl_425).base (finalizeFixedSpec C.F)

theorem finalize_fixed3_placed_ok [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooks C.F H] :
    FinalizeFixed3PlacedOk C H := by
  unfold FinalizeFixed3PlacedOk
  finalize_fixed3_ok_body fin3PlacedFakeB (FinalizeFixed3Proof.finalize_fixed3_placed_runsTo (H := H))

theorem finalize_fixed3_placed_ok_withLsCodeLoaded [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooks C.F H] :
    subroutine_ok ((blkPC_425).rebase (blkPl_425).base H) (blkPl_425).base
      (withLsCodeLoaded lsmpl (finalizeFixedSpec C.F)) :=
  subroutine_ok_withLsCodeLoaded_of_plain (finalize_fixed3_placed_ok C H)

end CryptoVerification.SpqrV1.Kdf
