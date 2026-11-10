/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGen
public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceFirstHalf
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock -- shake: keep

/-!
# `Hmac<Sha256>::new_from_slice [local#3]`: Long-Key Prefix Segments

SHA-256 multi-block padding lemmas and symbolic execution of `new_from_slice [local#3]` on keys
with `64 < key.length < 2 ^ 63` from entry (`0x66fa0`) through tail padding (`0x6707c`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.SpqrV1.Kdf.NewFromSlice3GenProof

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.CBC CryptoGames.LibsignalSession
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet (
  zeroExtend64_truncate32_ofNat64 zeroExtend64_ofNat8 xor_63_of_lt_64
  ult_7_of_lt_56 toLEBytes_8_read64 readBytes_56_eq_append_8 readBytes_56_of_buf_eq)
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof
open ProofLib.ProgramReflection
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds
  Memory.read64_write64_base_off_disjoint
  Memory.read64_write64_base_zero_off
  Memory.read64_write64_base_off_zero

@[simp, arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [0x61ba8 → 0x61cec]

theorem nfs_ule_65_true {len : BitVec 64} (h : 64 < len.toNat) :
    BitVec.ule 0x41#64 len = true := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq]; simp; omega

/-- Single-block padded tail (`|tail| < 56`) for SHA-256 of `pfx ++ tail` (`nBlocks = |pfx| / 64`). -/
def sha256PadBlock1 (nBlocks : ℕ) (tail : List (BitVec 8)) : List (BitVec 8) :=
  tail ++ [0x80#8] ++ List.replicate (55 - tail.length) 0#8 ++
    toBEBytes 8 (BitVec.ofNat 64 (8 * (64 * nBlocks + tail.length)))

theorem sha256PadBlock1_length (nBlocks : ℕ) {tail : List (BitVec 8)} (hlt : tail.length < 56) :
    (sha256PadBlock1 nBlocks tail).length = 64 := by
  unfold sha256PadBlock1
  simp [toBEBytes]
  omega

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

/-- SHA-256 of `pfx ++ tail` when `pfx.length % 64 = 0` and `tail.length < 56` (one padding block). -/
theorem sha256With_pfx_one_block (F : ShaState → List (BitVec 8) → ShaState)
    (pfx tail : List (BitVec 8))
    (hpfx : pfx.length % 64 = 0) (htail_lt : tail.length < 56) :
    sha256With F (pfx ++ tail) =
      digestBytes
        (F ((chunks64 pfx).foldl F sha256IV) (sha256PadBlock1 (pfx.length / 64) tail)) := by
  unfold sha256With digestBytes
  set nB := pfx.length / 64
  have hblk_len : (sha256PadBlock1 nB tail).length = 64 := sha256PadBlock1_length nB htail_lt
  have hpad : sha256Pad (pfx ++ tail) = pfx ++ sha256PadBlock1 nB tail := by
    unfold sha256Pad sha256PadBlock1
    have hlen : (pfx ++ tail).length = 64 * nB + tail.length := by simp [nB]; omega
    have hmod : (119 - (64 * nB + tail.length) % 64) % 64 = 55 - tail.length := by omega
    rw [hlen, hmod]
    simp only [List.append_assoc]
    rfl
  rw [hpad, chunks64_append_mul hpfx, chunks64_single hblk_len,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- SHA-256 of `pfx ++ tail` when `pfx.length % 64 = 0` and `56 ≤ tail.length < 64` (two padding blocks). -/
theorem sha256With_pfx_two_blocks (F : ShaState → List (BitVec 8) → ShaState)
    (pfx tail : List (BitVec 8))
    (hpfx : pfx.length % 64 = 0) (htail_ge : 56 ≤ tail.length) (htail_lt : tail.length < 64) :
    sha256With F (pfx ++ tail) =
      digestBytes
        (F (F ((chunks64 pfx).foldl F sha256IV) (innerPadBlock1 tail))
          (innerPadBlock2 (pfx.length / 64) tail)) := by
  unfold sha256With digestBytes
  set nB := pfx.length / 64
  have hblk1_len : (innerPadBlock1 tail).length = 64 := innerPadBlock1_length htail_lt
  have hblk2_len : (innerPadBlock2 nB tail).length = 64 := innerPadBlock2_length nB tail
  have hpad : sha256Pad (pfx ++ tail) = pfx ++ (innerPadBlock1 tail ++ innerPadBlock2 nB tail) := by
    unfold sha256Pad innerPadBlock1 innerPadBlock2
    have hlen : (pfx ++ tail).length = 64 * nB + tail.length := by simp [nB]; omega
    have hmod : (119 - (64 * nB + tail.length) % 64) % 64 = (63 - tail.length) + 56 := by omega
    rw [hlen, hmod, List.replicate_add]
    simp only [List.append_assoc]
    rfl
  rw [hpad, chunks64_append_mul hpfx, chunks64_append_64 hblk1_len, chunks64_single hblk2_len,
    List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil]

/-- Multi-block `compress256` step on `P b F alloc` (`b + 0x48018#64`). -/
theorem sess_compress256_multi_step {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ s : State} {P_post : State → Prop}
    {m₀ : Memory} {stPtr blkPtr lr : BitVec 64} {nBlocks : ℕ} {st st' : ShaState}
    {blocks : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = b + bv% (ls_off% "sha2::sha256::compress256"))
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : (s.readReg64 .x2).toNat = nBlocks)
    (hlr : s.readReg64 .lr = lr)
    (hmem : s.mem = m₀)
    (hst : m₀.readBytes stPtr 32 = shaStateBytes st)
    (hblk : m₀.readBytes blkPtr (64 * nBlocks) = blocks)
    (hst' : (chunks64 blocks).foldl F st = st')
    (hrw : m₀.RW stPtr 32)
    (h : RunsToFrom (P b F alloc) s₀
      ((s.setMem (m₀.writeBytes stPtr (shaStateBytes st'))).setPC lr) P_post) :
    RunsToFrom (P b F alloc) s₀ s P_post := by
  have hcan : s.mem.canWrite stPtr (shaStateBytes st').length = true := by
    rw [hmem, shaStateBytes_length]
    exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : (P b F alloc).externAt? s.pc = some (compress256Hook F) := by
    rw [hpc]; exact P_externAt_273212 b F alloc
  have hstate : compress256Hook F s =
      (s.setMem (m₀.writeBytes stPtr (shaStateBytes st'))).setPC lr := by
    rw [← hst', ← hmem]
    exact compress256Hook_multi_eq F hx0 hx1 hx2 hlr (hmem ▸ hst) (hmem ▸ hblk)
  have hkeep : s.mem.KeepsFrozen (compress256Hook F s).mem := by
    rw [hstate, ← hmem]; exact Memory.keepsFrozen_writeBytes (shaStateBytes st') hcan
  have hsym : (compress256Hook F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

/-- Multi-block `compress256` step on `lsProg_402 H`. -/
theorem placed_compress256_multi_step [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {s₀ s : State} {P_post : State → Prop}
    {m₀ : Memory} {stPtr blkPtr lr : BitVec 64} {nBlocks : ℕ} {st st' : ShaState}
    {blocks : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsmpl.ρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : (s.readReg64 .x2).toNat = nBlocks)
    (hlr : s.readReg64 .lr = lr)
    (hmem : s.mem = m₀)
    (hst : m₀.readBytes stPtr 32 = shaStateBytes st)
    (hblk : m₀.readBytes blkPtr (64 * nBlocks) = blocks)
    (hst' : (chunks64 blocks).foldl F st = st')
    (hrw : m₀.RW stPtr 32)
    (h : RunsToFrom (lsProg_402 H) s₀
      ((s.setMem (m₀.writeBytes stPtr (shaStateBytes st'))).setPC lr) P_post) :
    RunsToFrom (lsProg_402 H) s₀ s P_post := by
  have hcan : s.mem.canWrite stPtr (shaStateBytes st').length = true := by
    rw [hmem, shaStateBytes_length]
    exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : (lsProg_402 H).externAt? s.pc = some (compress256Hook F) := by
    rw [hpc, ls_externAt?_of_mem (prog := lsProg_402 H) (i := 402) (by decide) (by decide) (by decide), h_compress]
  have hstate : compress256Hook F s =
      (s.setMem (m₀.writeBytes stPtr (shaStateBytes st'))).setPC lr := by
    rw [← hst', ← hmem]
    exact compress256Hook_multi_eq F hx0 hx1 hx2 hlr (hmem ▸ hst) (hmem ▸ hblk)
  have hkeep : s.mem.KeepsFrozen (compress256Hook F s).mem := by
    rw [hstate, ← hmem]; exact Memory.keepsFrozen_writeBytes (shaStateBytes st') hcan
  have hsym : (compress256Hook F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

/-- Fake image base for code offsets of `new_from_slice [local#3]` (`0x61ac4`, Block `402`). -/
abbrev nfs3CodeFakeB [LibsignalPlacement] : BitVec 64 := (blkPl_402).base - 0x61ba8#64

@[simp, arm64_norm] theorem nfs3CodeFakeB_0x61ac4 [LibsignalPlacement] :
    nfs3CodeFakeB + 0x61ba8#64 = (blkPl_402).base := by unfold nfs3CodeFakeB; bv_omega
@[simp, arm64_norm] theorem nfs3CodeFakeB_0x61b0c [LibsignalPlacement] :
    nfs3CodeFakeB + 0x61bf0#64 = (blkPl_402).base + 72#64 := by unfold nfs3CodeFakeB; bv_omega
@[simp, arm64_norm] theorem nfs3CodeFakeB_0x61b38 [LibsignalPlacement] :
    nfs3CodeFakeB + 0x61c1c#64 = (blkPl_402).base + 116#64 := by unfold nfs3CodeFakeB; bv_omega
@[simp, arm64_norm] theorem nfs3CodeFakeB_0x61b3c [LibsignalPlacement] :
    nfs3CodeFakeB + 0x61c20#64 = (blkPl_402).base + 120#64 := by unfold nfs3CodeFakeB; bv_omega
@[simp, arm64_norm] theorem nfs3CodeFakeB_0x61b4c [LibsignalPlacement] :
    nfs3CodeFakeB + 0x61c30#64 = (blkPl_402).base + 136#64 := by unfold nfs3CodeFakeB; bv_omega
@[simp, arm64_norm] theorem nfs3CodeFakeB_0x61b50 [LibsignalPlacement] :
    nfs3CodeFakeB + 0x61c34#64 = (blkPl_402).base + 140#64 := by unfold nfs3CodeFakeB; bv_omega
@[simp, arm64_norm] theorem nfs3CodeFakeB_0x61b9c [LibsignalPlacement] :
    nfs3CodeFakeB + 0x61c80#64 = (blkPl_402).base + 216#64 := by unfold nfs3CodeFakeB; bv_omega
@[simp, arm64_norm] theorem nfs3CodeFakeB_0x61ba0 [LibsignalPlacement] :
    nfs3CodeFakeB + 0x61c84#64 = (blkPl_402).base + 220#64 := by unfold nfs3CodeFakeB; bv_omega
@[simp, arm64_norm] theorem nfs3CodeFakeB_0x61bc8 [LibsignalPlacement] :
    nfs3CodeFakeB + 0x61cac#64 = (blkPl_402).base + 260#64 := by unfold nfs3CodeFakeB; bv_omega
@[simp, arm64_norm] theorem nfs3CodeFakeB_0x61c04 [LibsignalPlacement] :
    nfs3CodeFakeB + 0x61ce8#64 = (blkPl_402).base + 320#64 := by unfold nfs3CodeFakeB; bv_omega
@[simp, arm64_norm] theorem nfs3CodeFakeB_0x61c08 [LibsignalPlacement] :
    nfs3CodeFakeB + 0x61cec#64 = (blkPl_402).base + 324#64 := by unfold nfs3CodeFakeB; bv_omega
@[simp, arm64_norm] theorem nfs3CodeFakeB_0x61c7c [LibsignalPlacement] :
    nfs3CodeFakeB + 0x61d60#64 = (blkPl_402).base + 440#64 := by unfold nfs3CodeFakeB; bv_omega
@[simp, arm64_norm] theorem nfs3CodeFakeB_0x61ca0 [LibsignalPlacement] :
    nfs3CodeFakeB + 0x61d84#64 = (blkPl_402).base + 476#64 := by unfold nfs3CodeFakeB; bv_omega
@[simp, arm64_norm] theorem nfs3CodeFakeB_0x61fb0 [LibsignalPlacement] :
    nfs3CodeFakeB + 0x62094#64 = (blkPl_402).base + 1260#64 := by unfold nfs3CodeFakeB; bv_omega

/-- `memset` step on `lsProg_402 H`. -/
theorem placed_memset_step [LibsignalPlacement]
    {H : LibsignalHooks} (h_memset : H lsMemsetSym = some memsetHook)
    {s₀ s : State} {P_post : State → Prop}
    {m₀ : Memory} {dst : BitVec 64} {val : BitVec 8} {len : ℕ} {lr : BitVec 64}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsmpl.ρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hmem : s.mem = m₀)
    (hrw : m₀.RW dst len)
    (h : RunsToFrom (lsProg_402 H) s₀
      ((s.setMem (m₀.writeBytes dst (List.replicate len val))).setPC lr) P_post) :
    RunsToFrom (lsProg_402 H) s₀ s P_post :=
  RunsTo.placed_memset_step h_memset hrun hpc hx0 hx1 hx2 hlr hmem hrw h

theorem write64_quad_240_iv (b : BitVec 64) (m₁ m₂ : Memory) (sp : BitVec 64)
    (hiv : m₂.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV) :
    ((((m₁.write64 (sp + 240#64) (m₂.read64 (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)))).write64
      (sp + 248#64) (m₂.read64 (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 72)))).write64
      (sp + 256#64) (m₂.read64 (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 80)))).write64
      (sp + 264#64) (m₂.read64 (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 88)))) =
    m₁.writeBytes (sp + 240#64) (shaStateBytes sha256IV) := by
  have hd1 : sp + 248#64 = (sp + 240#64) + 8#64 := by bv_omega
  have hd2 : sp + 256#64 = (sp + 240#64) + 16#64 := by bv_omega
  have hd3 : sp + 264#64 = (sp + 240#64) + 24#64 := by bv_omega
  have hs1 : b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 72) = (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) + 8#64 := by bv_omega
  have hs2 : b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 80) = (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) + 16#64 := by bv_omega
  have hs3 : b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 88) = (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) + 24#64 := by bv_omega
  rw [hd1, hd2, hd3, hs1, hs2, hs3, write64_quad_read64_eq_writeBytes_32, hiv]

theorem write64_quad_240_iv_placed [LibsignalPlacement] (m₁ m₂ : Memory) (sp : BitVec 64)
    (hiv : m₂.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV) :
    ((((m₁.write64 (sp + 240#64) (m₂.read64 spqrSha256IVAddr)).write64
      (sp + 248#64) (m₂.read64 (spqrSha256IVAddr + 8#64))).write64
      (sp + 256#64) (m₂.read64 (spqrSha256IVAddr + 16#64))).write64
      (sp + 264#64) (m₂.read64 (spqrSha256IVAddr + 24#64))) =
    m₁.writeBytes (sp + 240#64) (shaStateBytes sha256IV) := by
  have hd1 : sp + 248#64 = (sp + 240#64) + 8#64 := by bv_omega
  have hd2 : sp + 256#64 = (sp + 240#64) + 16#64 := by bv_omega
  have hd3 : sp + 264#64 = (sp + 240#64) + 24#64 := by bv_omega
  rw [hd1, hd2, hd3, write64_quad_read64_eq_writeBytes_32, hiv]

@[scoped simp, arm64_norm]
theorem extractLsb'_read64_56 (m : Memory) (sp off : BitVec 64) :
    (m.read64 (sp + off)).extractLsb' 56 8 = m.read8 (sp + (off + 7#64)) := by
  have h := toLEBytes_8_read64_eq m (sp + off)
  rw [toLEBytes_8_eq_list, readBytes_8_eq] at h
  simp only [BitVec.add_assoc] at h
  exact (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj
    (List.cons.inj (List.cons.inj (List.cons.inj h).2).2).2).2).2).2).2).1

theorem readBytes_take_of_le (m : Memory) (a : BitVec 64) {n k : ℕ} (h : n ≤ k) :
    m.readBytes a n = (m.readBytes a k).take n := by
  have hk : k = n + (k - n) := by omega
  rw [hk, Bytes.readBytes_add, List.take_left' (Memory.readBytes_length m a n)]

/-- Memory after prologue + zeroing `[nfsSp s₀ + 112, nfsSp s₀ + 176)`. -/
def nfsZeroMem (s₀ : State) : Memory :=
  (nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)

theorem agreesOutside_nfsZeroMem (s₀ : State) :
    AgreesOutside (nfsPrologueMem s₀) (nfsZeroMem s₀) (nfsSp s₀ + 112#64) 64 := by
  simpa [nfsZeroMem] using
    ProofLib.agreesOutside_writeBytes (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (List.replicate 64 0#8)

theorem agreesOutside_trans {m₀ m₁ m₂ : Memory} {a : BitVec 64} {n : ℕ}
    (h1 : AgreesOutside m₀ m₁ a n) (h2 : AgreesOutside m₁ m₂ a n) :
    AgreesOutside m₀ m₂ a n :=
  ⟨fun x hx => (h2.1 x hx).trans (h1.1 x hx),
    h2.2.1.trans h1.2.1,
    fun x hx => (h2.2.2.1 x hx).trans (h1.2.2.1 x hx),
    fun x hlf => h2.2.2.2.1 x (h1.2.2.2.1 x hlf),
    fun x han => h2.2.2.2.2 x (h1.2.2.2.2 x han)⟩

theorem agreesOutside_sub_176_288 {m₀ m₁ m₂ : Memory} {sp off : BitVec 64} {sz : ℕ}
    (h1 : AgreesOutside m₀ m₁ (sp + 176#64) 288)
    (h2 : AgreesOutside m₁ m₂ (sp + off) sz)
    (hoff : 176 ≤ off.toNat ∧ off.toNat + sz ≤ 464) :
    AgreesOutside m₀ m₂ (sp + 176#64) 288 := by
  have hx' (x : BitVec 64) (hx : OutsideRegion (sp + 176#64) 288 x) :
      OutsideRegion (sp + off) sz x := by
    rcases hoff with ⟨_, _⟩; simp only [OutsideRegion] at hx ⊢; bv_omega
  exact ⟨fun x hx => (h2.1 x (hx' x hx)).trans (h1.1 x hx),
    h2.2.1.trans h1.2.1,
    fun x hx => (h2.2.2.1 x (hx' x hx)).trans (h1.2.2.1 x hx),
    fun x hlf => h2.2.2.2.1 x (h1.2.2.2.1 x hlf),
    fun x han => h2.2.2.2.2 x (h1.2.2.2.2 x han)⟩

/-- Common register & memory invariant across `0x66fe8 .. 0x670e4` on the `> 64` key path. -/
structure NfsGt64Common (b : BitVec 64) (s₀ s : State) : Prop where
  status : s.status = .Running
  sp_eq : s.sp = nfsSp s₀
  sp_align : (nfsSp s₀ &&& 0b1111#64) = 0#64
  x29_eq : s.readReg64 .x29 = nfsSp s₀ + 464#64
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x22_eq : s.readReg64 .x22 = b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)
  x25_eq : s.readReg64 .x25 = s₀.readReg64 .x25
  x26_eq : s.readReg64 .x26 = s₀.readReg64 .x26
  x27_eq : s.readReg64 .x27 = s₀.readReg64 .x27
  agrees_zero : AgreesOutside (nfsZeroMem s₀) s.mem (nfsSp s₀ + 176#64) 288

theorem NfsGt64Common.rw_stack {b : BitVec 64} {s₀ s : State}
    (hc : NfsGt64Common b s₀ s) (hrw : s₀.mem.RW (nfsSp s₀) 544) :
    s.mem.RW (nfsSp s₀) 544 :=
  (Frame.rw_iff (agreesOutside_toFrame hc.agrees_zero) _ _).mpr
    ((Frame.rw_iff (agreesOutside_toFrame (agreesOutside_nfsZeroMem s₀)) _ _).mpr
      ((Frame.rw_iff (agreesOutside_toFrame (agreesOutside_nfsPrologueMem s₀)) _ _).mpr hrw))

structure StateG0 (b : BitVec 64) (s₀ s : State) (b_iv : BitVec 64 := b) : Prop where
  pc_eq : s.pc = b + 0x61bf0#64
  common : NfsGt64Common b_iv s₀ s
  x1_eq : s.readReg64 .x1 = s₀.readReg64 .x1
  x2_eq : s.readReg64 .x2 = s₀.readReg64 .x2

set_option maxHeartbeats 1600000 in
theorem nfs_seg0_pro_gt64 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ : State}
    (hpc : s₀.pc = b + 0x61ba8#64)
    (hstat : s₀.status = .Running)
    (hgt : 64 < (s₀.readReg64 .x2).toNat)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    RunsTo (P b F alloc) s₀ (StateG0 b s₀) := by
  have hsp₀ : s₀.sp = nfsSp s₀ + 544#64 := nfs_sp_eq_add s₀
  have hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64 := nfs_sp_align hal
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hRW_stack : s₀.mem.RW (nfsSp s₀) 544 := hrw_stack
  have hcond : BitVec.ule 0x41#64 (s₀.readReg64 .x2) = true := nfs_ule_65_true hgt
  have hadrp1 := nfs3_adrp_x22_0x66fc8_assoc hb
  have hadrp2 := nfs3_adrp_x22_0x66fc8 hb
  iterate 15 sess_step
  refine RunsTo.refl ?_
  have hmem_eq :
      ((((((((nfsPrologueMem s₀).write64 (nfsSp s₀ + 112#64) 0#64).write64
        (nfsSp s₀ + 120#64) 0#64).write64 (nfsSp s₀ + 128#64) 0#64).write64
        (nfsSp s₀ + 136#64) 0#64).write64 (nfsSp s₀ + 144#64) 0#64).write64
        (nfsSp s₀ + 152#64) 0#64).write64 (nfsSp s₀ + 160#64) 0#64).write64
        (nfsSp s₀ + 168#64) 0#64 = nfsZeroMem s₀ :=
    write64_oct_zero_eq_writeBytes_64 (nfsPrologueMem s₀) (nfsSp s₀)
  refine
    { pc_eq := by simp only [arm64_norm]
      common :=
        { status := by simp only [arm64_norm, hstat]
          sp_eq := by simp only [arm64_norm]
          sp_align := hal_nfs
          x29_eq := by simp only [arm64_norm]
          x19_eq := by simp only [arm64_norm]
          x22_eq := by simp only [arm64_norm]
          x25_eq := by simp only [arm64_norm]
          x26_eq := by simp only [arm64_norm]
          x27_eq := by simp only [arm64_norm]
          agrees_zero := by
            dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
            dsimp only [nfsPrologueMem] at hmem_eq
            rw [hmem_eq]
            exact AgreesOutside.rfl' (nfsZeroMem s₀) (nfsSp s₀ + 176#64) 288 }
      x1_eq := by simp only [arm64_norm]
      x2_eq := by simp only [arm64_norm] }

set_option maxHeartbeats 1600000 in
theorem nfs_seg0_pro_gt64_placed [LibsignalPlacement] {H : LibsignalHooks} {s₀ : State}
    (hpc : s₀.pc = (blkPl_402).base)
    (hstat : s₀.status = .Running)
    (hgt : 64 < (s₀.readReg64 .x2).toNat)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    RunsTo (lsProg_402 H) s₀ (StateG0 nfs3CodeFakeB s₀ · nfs3PlacedFakeB) := by
  have hsp₀ : s₀.sp = nfsSp s₀ + 544#64 := nfs_sp_eq_add s₀
  have hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64 := nfs_sp_align hal
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hRW_stack : s₀.mem.RW (nfsSp s₀) 544 := hrw_stack
  have hcond : BitVec.ule 0x41#64 (s₀.readReg64 .x2) = true := nfs_ule_65_true hgt
  iterate 10 sess_step
  refine RunsTo.pairStep_402_0x28 (by simp only [arm64_norm, hpc]) (by simp only [arm64_norm, hstat]) ?_
  iterate 3 sess_step
  refine RunsTo.refl ?_
  have hmem_eq :
      ((((((((nfsPrologueMem s₀).write64 (nfsSp s₀ + 112#64) 0#64).write64
        (nfsSp s₀ + 120#64) 0#64).write64 (nfsSp s₀ + 128#64) 0#64).write64
        (nfsSp s₀ + 136#64) 0#64).write64 (nfsSp s₀ + 144#64) 0#64).write64
        (nfsSp s₀ + 152#64) 0#64).write64 (nfsSp s₀ + 160#64) 0#64).write64
        (nfsSp s₀ + 168#64) 0#64 = nfsZeroMem s₀ :=
    write64_oct_zero_eq_writeBytes_64 (nfsPrologueMem s₀) (nfsSp s₀)
  refine
    { pc_eq := by simp only [arm64_norm]
      common :=
        { status := by simp only [arm64_norm, hstat]
          sp_eq := by simp only [arm64_norm]
          sp_align := hal_nfs
          x29_eq := by simp only [arm64_norm]
          x19_eq := by simp only [arm64_norm]
          x22_eq := by simp only [arm64_norm]
          x25_eq := by simp only [arm64_norm]
          x26_eq := by simp only [arm64_norm]
          x27_eq := by simp only [arm64_norm]
          agrees_zero := by
            dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
            dsimp only [nfsPrologueMem] at hmem_eq
            rw [hmem_eq]
            exact AgreesOutside.rfl' (nfsZeroMem s₀) (nfsSp s₀ + 176#64) 288 }
      x1_eq := by simp only [arm64_norm]
      x2_eq := by simp only [arm64_norm] }

structure StateG1 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) (b_iv : BitVec 64 := b) : Prop where
  pc_eq : s.pc = b + 0x61c34#64
  common : NfsGt64Common b_iv s₀ s
  tail_bytes : s.mem.readBytes (nfsSp s₀ + 176#64) (key.length - 64 * (key.length / 64)) =
    key.drop (64 * (key.length / 64))
  pos_byte : s.mem.read8 (nfsSp s₀ + 239#64) = BitVec.ofNat 8 (key.length - 64 * (key.length / 64))
  st0_bytes : s.mem.readBytes (nfsSp s₀ + 240#64) 32 =
    shaStateBytes ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV)
  nblk_word : s.mem.read64 (nfsSp s₀ + 272#64) = BitVec.ofNat 64 (key.length / 64)

set_option hygiene false in
local macro "nfs_seg0a_gt64_body " bIv:term:max quadLem:term:max compLem:term:max mcLem:term:max : tactic => `(tactic| (
  intro key
  rcases hs with ⟨hpc, hcom, hx1, hx2⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hag_zero⟩
  have hA_pro : AgreesOutside s₀.mem (nfsPrologueMem s₀) (nfsSp s₀ + 464#64) 80 :=
    agreesOutside_nfsPrologueMem s₀
  have hA_zero : AgreesOutside (nfsPrologueMem s₀) (nfsZeroMem s₀) (nfsSp s₀ + 112#64) 64 :=
    agreesOutside_nfsZeroMem s₀
  have hRW_pro : (nfsPrologueMem s₀).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack
  have hRW_zero : (nfsZeroMem s₀).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hA_zero) _ _).mpr hRW_pro
  have hread_iv_s : s.mem.Readable ($bIv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 :=
    (Frame.readable_iff (agreesOutside_toFrame hag_zero) _ _).mpr
      ((Frame.readable_iff (agreesOutside_toFrame hA_zero) _ _).mpr
        ((Frame.readable_iff (agreesOutside_toFrame hA_pro) _ _).mpr hread_iv))
  try simp only [arm64_norm] at hread_iv_s
  have hiv_s : s.mem.readBytes ($bIv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV := by
    have hd0 : DisjointRegions (nfsSp s₀ + 176#64) 288 ($bIv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
      clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
    have hd1 : DisjointRegions (nfsSp s₀ + 112#64) 64 ($bIv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
      clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
    have hd2 : DisjointRegions (nfsSp s₀ + 464#64) 80 ($bIv + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
      clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
    rw [(agreesOutside_toFrame hag_zero).readBytes_eq (by simp only [List.mem_singleton, forall_eq]; exact hd0) (by decide),
        (agreesOutside_toFrame hA_zero).readBytes_eq (by simp only [List.mem_singleton, forall_eq]; exact hd1) (by decide),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp only [List.mem_singleton, forall_eq]; exact hd2) (by decide), hiv]
  iterate 12 sess_step
  set m_pre_c1 := ((s.mem.write8 (nfsSp s₀ + 239#64) 0#8).writeBytes
    (nfsSp s₀ + 240#64) (shaStateBytes sha256IV)).write64
    (nfsSp s₀ + 272#64) (s₀.readReg64 .x2 >>> 6)
  have hag_pre_c1 : AgreesOutside (nfsZeroMem s₀) m_pre_c1 (nfsSp s₀ + 176#64) 288 := by
    have h1 := agreesOutside_sub_176_288 hag_zero
      (AgreesOutside.write8_self s.mem (nfsSp s₀ + 239#64) 0#8) (by decide)
    have h2 : AgreesOutside (s.mem.write8 (nfsSp s₀ + 239#64) 0#8)
        ((s.mem.write8 (nfsSp s₀ + 239#64) 0#8).writeBytes (nfsSp s₀ + 240#64) (shaStateBytes sha256IV))
        (nfsSp s₀ + 240#64) 32 := by
      have hlen : (shaStateBytes sha256IV).length = 32 := shaStateBytes_length sha256IV
      rw [← hlen]; exact ProofLib.agreesOutside_writeBytes _ _ _
    have h3 := agreesOutside_sub_176_288 h1 h2 (by decide)
    exact agreesOutside_sub_176_288 h3
      (AgreesOutside.write64_self _ (nfsSp s₀ + 272#64) (s₀.readReg64 .x2 >>> 6)) (by decide)
  have hst_pre_c1 : m_pre_c1.readBytes (nfsSp s₀ + 240#64) 32 = shaStateBytes sha256IV := by
    dsimp only [m_pre_c1]
    have hd : DisjointRegions (nfsSp s₀ + 272#64) 8 (nfsSp s₀ + 240#64) 32 := by
      simp only [DisjointRegions]; bv_omega
    rw [(agreesOutside_toFrame (AgreesOutside.write64_self _ (nfsSp s₀ + 272#64) _)).readBytes_eq
      (by simp [hd]) (by decide)]
    exact Run.Layout.readBytes_writeBytes_eq _ _ _ 32 (shaStateBytes_length sha256IV) (by decide)
  have hkey_pre_c1 : m_pre_c1.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key := by
    have hd1 : DisjointRegions (nfsSp s₀ + 176#64) 288 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    have hd2 : DisjointRegions (nfsSp s₀ + 112#64) 64 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    have hd3 : DisjointRegions (nfsSp s₀ + 464#64) 80 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    rw [(agreesOutside_toFrame hag_pre_c1).readBytes_eq (by simp [hd1]) (by omega),
        (agreesOutside_toFrame hA_zero).readBytes_eq (by simp [hd2]) (by omega),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hd3]) (by omega)]
  have hkey_len : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  have hkey_gt : 64 < key.length := by omega
  have hkey_lt : key.length < 2 ^ 63 := by omega
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := ikm_split_lemmas hkey_lt
  have hpfx_pre_c1 : m_pre_c1.readBytes (s₀.readReg64 .x1) (64 * (key.length / 64)) =
      key.take (64 * (key.length / 64)) := by
    rw [readBytes_take_of_le m_pre_c1 (s₀.readReg64 .x1) (by omega : 64 * (key.length / 64) ≤ (s₀.readReg64 .x2).toNat),
        hkey_pre_c1]
  have hrw_pre_c1 : m_pre_c1.RW (nfsSp s₀ + 240#64) 32 :=
    ((Frame.rw_iff (agreesOutside_toFrame hag_pre_c1) _ _).mpr hRW_zero).sub (by bv_omega)
  refine $compLem
    (by simp only [arm64_norm, hstat]) rfl (by simp only [arm64_norm])
    (by simp only [arm64_norm, hx1])
    (by
      simp only [arm64_norm]
      have hx2_eq : s₀.readReg64 .x2 = BitVec.ofNat 64 key.length := by
        rw [hkey_len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [hx2_eq, hs1])
    (by simp only [arm64_norm]; rfl)
    (by
      rw [State.mem_setMem]
      dsimp only [m_pre_c1]
      rw [$quadLem (s.mem.write8 (nfsSp s₀ + 239#64) 0#8) s.mem (nfsSp s₀) (by simpa only [arm64_norm] using hiv_s)])
    hst_pre_c1 hpfx_pre_c1 rfl hrw_pre_c1 ?_
  set st0 := (chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV
  set m_post_c1 := m_pre_c1.writeBytes (nfsSp s₀ + 240#64) (shaStateBytes st0)
  have hag_post_c1 : AgreesOutside (nfsZeroMem s₀) m_post_c1 (nfsSp s₀ + 176#64) 288 := by
    have h2 : AgreesOutside m_pre_c1 m_post_c1 (nfsSp s₀ + 240#64) 32 := by
      have hlen : (shaStateBytes st0).length = 32 := shaStateBytes_length st0
      rw [← hlen]; exact ProofLib.agreesOutside_writeBytes _ _ _
    exact agreesOutside_sub_176_288 hag_pre_c1 h2 (by decide)
  have hRW_post_c1 : m_post_c1.RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hag_post_c1) _ _).mpr hRW_zero
  iterate 5 sess_step
  have hx2_eq : s₀.readReg64 .x2 = BitVec.ofNat 64 key.length := by
    rw [hkey_len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  set m_pre_mc := m_post_c1.write8 (nfsSp s₀ + 239#64) (BitVec.truncate 8 (s₀.readReg64 .x2 &&& 63#64))
  have hag_pre_mc : AgreesOutside (nfsZeroMem s₀) m_pre_mc (nfsSp s₀ + 176#64) 288 :=
    agreesOutside_sub_176_288 hag_post_c1
      (AgreesOutside.write8_self m_post_c1 (nfsSp s₀ + 239#64) _) (by decide)
  have hkey_pre_mc : m_pre_mc.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key := by
    have hd1 : DisjointRegions (nfsSp s₀ + 176#64) 288 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    have hd2 : DisjointRegions (nfsSp s₀ + 112#64) 64 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    have hd3 : DisjointRegions (nfsSp s₀ + 464#64) 80 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    rw [(agreesOutside_toFrame hag_pre_mc).readBytes_eq (by simp [hd1]) (by omega),
        (agreesOutside_toFrame hA_zero).readBytes_eq (by simp [hd2]) (by omega),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hd3]) (by omega)]
  have htail_pre_mc : m_pre_mc.readBytes
      (s₀.readReg64 .x1 + (s₀.readReg64 .x2 &&& 9223372036854775744#64))
      (key.length - 64 * (key.length / 64)) =
      key.drop (64 * (key.length / 64)) := by
    rw [hx2_eq, hs3]
    have hsplit : (s₀.readReg64 .x2).toNat =
        64 * (key.length / 64) + (key.length - 64 * (key.length / 64)) := by omega
    have hadd := Bytes.readBytes_add m_pre_mc (s₀.readReg64 .x1)
      (64 * (key.length / 64)) (key.length - 64 * (key.length / 64))
    rw [← hsplit, hkey_pre_mc] at hadd
    have hdrop := congrArg (List.drop (64 * (key.length / 64))) hadd.symm
    rwa [List.drop_left' (Memory.readBytes_length _ _ _)] at hdrop
  have hrw_pre_mc : m_pre_mc.RW (nfsSp s₀ + 176#64) (key.length - 64 * (key.length / 64)) :=
    ((Frame.rw_iff (agreesOutside_toFrame hag_pre_mc) _ _).mpr hRW_zero).sub (by bv_omega)
  refine $mcLem
    (by simp only [arm64_norm, hstat]) rfl (by simp only [arm64_norm])
    (by simp only [arm64_norm, hx1])
    (by simp only [arm64_norm, hx2_eq, hs4])
    (by simp only [arm64_norm]; rfl)
    (State.mem_setMem _ _) htail_pre_mc hrw_pre_mc ?_
  refine RunsTo.refl ?_
  set tail := key.drop (64 * (key.length / 64))
  have htail_len : tail.length = key.length - 64 * (key.length / 64) := by simp [tail]
  have htail_lt : tail.length < 64 := by omega
  set m_end := m_pre_mc.writeBytes (nfsSp s₀ + 176#64) tail
  have hag_mc : AgreesOutside m_pre_mc m_end (nfsSp s₀ + 176#64) tail.length :=
    ProofLib.agreesOutside_writeBytes m_pre_mc (nfsSp s₀ + 176#64) tail
  have hag_end : AgreesOutside (nfsZeroMem s₀) m_end (nfsSp s₀ + 176#64) 288 :=
    agreesOutside_sub_176_288 hag_pre_mc hag_mc (by bv_omega)
  refine
    { pc_eq := by simp only [arm64_norm]
      common :=
        { status := by simp only [arm64_norm, hstat]
          sp_eq := by simp only [arm64_norm, hsp]
          sp_align := hal_nfs
          x29_eq := by simp only [arm64_norm, hx29]
          x19_eq := by simp only [arm64_norm, hx19]
          x22_eq := by simp only [arm64_norm, hx22]
          x25_eq := by simp only [arm64_norm, hx25]
          x26_eq := by simp only [arm64_norm, hx26]
          x27_eq := by simp only [arm64_norm, hx27]
          agrees_zero := hag_end }
      tail_bytes := by
        rw [State.mem_setPC, State.mem_setMem]
        exact Run.Layout.readBytes_writeBytes_eq m_pre_mc (nfsSp s₀ + 176#64) tail
          (key.length - 64 * (key.length / 64)) htail_len (by omega)
      pos_byte := by
        have hd : DisjointRegions (nfsSp s₀ + 176#64) tail.length (nfsSp s₀ + 239#64) 1 := by
          simp only [DisjointRegions]; bv_omega
        have h1 : m_end.read8 (nfsSp s₀ + 239#64) = m_pre_mc.read8 (nfsSp s₀ + 239#64) :=
          hag_mc.1 (nfsSp s₀ + 239#64) (by simp only [OutsideRegion]; bv_omega)
        rw [State.mem_setPC, State.mem_setMem, h1]
        dsimp only [m_pre_mc]
        rw [Memory.read8_write8_same, hx2_eq, hs5]
      st0_bytes := by
        have hd1 : DisjointRegions (nfsSp s₀ + 176#64) tail.length (nfsSp s₀ + 240#64) 32 := by
          simp only [DisjointRegions]; bv_omega
        have hd2 : DisjointRegions (nfsSp s₀ + 239#64) 1 (nfsSp s₀ + 240#64) 32 := by
          simp only [DisjointRegions]; bv_omega
        rw [State.mem_setPC, State.mem_setMem,
            (agreesOutside_toFrame hag_mc).readBytes_eq (by simp [hd1]) (by decide)]
        dsimp only [m_pre_mc]
        rw [(agreesOutside_toFrame (AgreesOutside.write8_self m_post_c1 (nfsSp s₀ + 239#64) _)).readBytes_eq
              (by simp [hd2]) (by decide)]
        exact Run.Layout.readBytes_writeBytes_eq m_pre_c1 (nfsSp s₀ + 240#64) (shaStateBytes st0) 32
          (shaStateBytes_length st0) (by decide)
      nblk_word := by
        have hd1 : DisjointRegions (nfsSp s₀ + 176#64) tail.length (nfsSp s₀ + 272#64) 8 := by
          simp only [DisjointRegions]; bv_omega
        have hd2 : DisjointRegions (nfsSp s₀ + 239#64) 1 (nfsSp s₀ + 272#64) 8 := by
          simp only [DisjointRegions]; bv_omega
        have hd3 : DisjointRegions (nfsSp s₀ + 240#64) 32 (nfsSp s₀ + 272#64) 8 := by
          simp only [DisjointRegions]; bv_omega
        rw [State.mem_setPC, State.mem_setMem,
            (agreesOutside_toFrame hag_mc).read64_eq (by simp [hd1])]
        dsimp only [m_pre_mc]
        rw [(agreesOutside_toFrame (AgreesOutside.write8_self m_post_c1 (nfsSp s₀ + 239#64) _)).read64_eq
              (by simp [hd2])]
        dsimp only [m_post_c1]
        rw [(agreesOutside_toFrame (ProofLib.agreesOutside_writeBytes m_pre_c1 (nfsSp s₀ + 240#64) (shaStateBytes st0))).read64_eq
              (by simp [hd3])]
        dsimp only [m_pre_c1]
        rw [Memory.read64_write64_same, hx2_eq]
        apply BitVec.eq_of_toNat_eq
        rw [hs1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] }))

set_option maxHeartbeats 1600000 in
theorem nfs_seg0a_gt64 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ s : State}
    (hs : StateG0 b s₀ s)
    (hgt : 64 < (s₀.readReg64 .x2).toNat)
    (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32)
    (hdisj_iv_stack : DisjointRegions (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 544#64) 544)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_key_stack : DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (P b F alloc) s (StateG1 b F key s₀) := by
  nfs_seg0a_gt64_body b (write64_quad_240_iv b) sess_compress256_multi_step RunsTo.sess_memcpy_step

set_option maxHeartbeats 1600000 in
theorem nfs_seg0a_gt64_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) {s₀ s : State}
    (hs : StateG0 nfs3CodeFakeB s₀ s nfs3PlacedFakeB)
    (hgt : 64 < (s₀.readReg64 .x2).toNat)
    (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32)
    (hdisj_iv_stack : DisjointRegions (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 544#64) 544)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_key_stack : DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s (StateG1 nfs3CodeFakeB F key s₀ · nfs3PlacedFakeB) := by
  nfs_seg0a_gt64_body nfs3PlacedFakeB write64_quad_240_iv_placed (placed_compress256_multi_step h_compress) (RunsTo.placed_memcpy_step h_memcpy)

/-- Memory after copying `sp + 176..272` to `sp + 288..384` and storing `nblk` at `sp + 384`
in `0x6702c .. 0x67070`. -/
def nfsCopy288Mem (m : Memory) (sp nblk : BitVec 64) : Memory :=
  ((((((((((((m.write64 (sp + 336#64) (m.read64 (sp + 224#64))).write64
    (sp + 344#64) (m.read64 (sp + 232#64))).write64
    (sp + 352#64) (m.read64 (sp + 240#64))).write64
    (sp + 360#64) (m.read64 (sp + 248#64))).write64
    (sp + 368#64) (m.read64 (sp + 256#64))).write64
    (sp + 376#64) (m.read64 (sp + 264#64))).write64
    (sp + 384#64) nblk).write64
    (sp + 288#64) (m.read64 (sp + 176#64))).write64
    (sp + 296#64) (m.read64 (sp + 184#64))).write64
    (sp + 304#64) (m.read64 (sp + 192#64))).write64
    (sp + 312#64) (m.read64 (sp + 200#64))).write64
    (sp + 320#64) (m.read64 (sp + 208#64))).write64
    (sp + 328#64) (m.read64 (sp + 216#64))

theorem agreesOutside_nfsCopy288Mem (m : Memory) (sp nblk : BitVec 64) :
    AgreesOutside m (nfsCopy288Mem m sp nblk) (sp + 288#64) 104 := by
  unfold nfsCopy288Mem
  agrees_outside_writes

theorem nfsCopy288Mem_eq_writeBytes_48 (m : Memory) (sp nblk : BitVec 64) :
    nfsCopy288Mem m sp nblk =
      (((((((m.write64 (sp + 336#64) (m.read64 (sp + 224#64))).write64
        (sp + 344#64) (m.read64 (sp + 232#64))).write64
        (sp + 352#64) (m.read64 (sp + 240#64))).write64
        (sp + 360#64) (m.read64 (sp + 248#64))).write64
        (sp + 368#64) (m.read64 (sp + 256#64))).write64
        (sp + 376#64) (m.read64 (sp + 264#64))).write64
        (sp + 384#64) nblk).writeBytes (sp + 288#64) (m.readBytes (sp + 176#64) 48) := by
  unfold nfsCopy288Mem
  have hd1 : sp + 296#64 = (sp + 288#64) + 8#64 := by bv_omega
  have hd2 : sp + 304#64 = (sp + 288#64) + 16#64 := by bv_omega
  have hd3 : sp + 312#64 = (sp + 288#64) + 24#64 := by bv_omega
  have hs1 : sp + 184#64 = (sp + 176#64) + 8#64 := by bv_omega
  have hs2 : sp + 192#64 = (sp + 176#64) + 16#64 := by bv_omega
  have hs3 : sp + 200#64 = (sp + 176#64) + 24#64 := by bv_omega
  have hd5 : sp + 328#64 = (sp + 320#64) + 8#64 := by bv_omega
  have hs5 : sp + 216#64 = (sp + 208#64) + 8#64 := by bv_omega
  rw [hd1, hd2, hd3, hs1, hs2, hs3, write64_quad_read64_eq_writeBytes_32,
      hd5, hs5, write64_pair_read64_eq_writeBytes_16]
  have hd4 : sp + 320#64 = (sp + 288#64) + BitVec.ofNat 64 (m.readBytes (sp + 176#64) 32).length := by
    rw [Memory.readBytes_length]; bv_omega
  have hs4 : sp + 208#64 = (sp + 176#64) + 32#64 := by bv_omega
  rw [hd4, ← writeBytes_append, hs4, ← Bytes.readBytes_add m (sp + 176#64) 32 16]

theorem readBytes_352_nfsCopy288Mem (m : Memory) (sp nblk : BitVec 64) :
    (nfsCopy288Mem m sp nblk).readBytes (sp + 352#64) 32 = m.readBytes (sp + 240#64) 32 := by
  rw [nfsCopy288Mem_eq_writeBytes_48]
  set m_0 := (m.write64 (sp + 336#64) (m.read64 (sp + 224#64))).write64
    (sp + 344#64) (m.read64 (sp + 232#64))
  set m_st := (((m_0.write64 (sp + 352#64) (m.read64 (sp + 240#64))).write64
    (sp + 360#64) (m.read64 (sp + 248#64))).write64
    (sp + 368#64) (m.read64 (sp + 256#64))).write64
    (sp + 376#64) (m.read64 (sp + 264#64))
  have hag_48 : AgreesOutside (m_st.write64 (sp + 384#64) nblk)
      ((m_st.write64 (sp + 384#64) nblk).writeBytes (sp + 288#64) (m.readBytes (sp + 176#64) 48))
      (sp + 288#64) 48 := by
    have hlen : (m.readBytes (sp + 176#64) 48).length = 48 := Memory.readBytes_length _ _ _
    rw [← hlen]; exact ProofLib.agreesOutside_writeBytes _ _ _
  have hag_384 : AgreesOutside m_st (m_st.write64 (sp + 384#64) nblk) (sp + 384#64) 8 :=
    AgreesOutside.write64_self _ _ _
  have hd_48 : DisjointRegions (sp + 288#64) 48 (sp + 352#64) 32 := by
    simp only [DisjointRegions]; bv_omega
  have hd_384 : DisjointRegions (sp + 384#64) 8 (sp + 352#64) 32 := by
    simp only [DisjointRegions]; bv_omega
  rw [(agreesOutside_toFrame hag_48).readBytes_eq (by simp [hd_48]) (by decide),
      (agreesOutside_toFrame hag_384).readBytes_eq (by simp [hd_384]) (by decide)]
  dsimp only [m_st]
  have hd1 : sp + 360#64 = (sp + 352#64) + 8#64 := by bv_omega
  have hd2 : sp + 368#64 = (sp + 352#64) + 16#64 := by bv_omega
  have hd3 : sp + 376#64 = (sp + 352#64) + 24#64 := by bv_omega
  have hs1 : sp + 248#64 = (sp + 240#64) + 8#64 := by bv_omega
  have hs2 : sp + 256#64 = (sp + 240#64) + 16#64 := by bv_omega
  have hs3 : sp + 264#64 = (sp + 240#64) + 24#64 := by bv_omega
  rw [hd1, hd2, hd3, hs1, hs2, hs3, write64_quad_read64_eq_writeBytes_32]
  exact Run.Layout.readBytes_writeBytes_eq _ _ _ 32 (Memory.readBytes_length _ _ _) (by decide)

theorem readBytes_288_nfsCopy288Mem (m : Memory) (sp nblk : BitVec 64) :
    (nfsCopy288Mem m sp nblk).readBytes (sp + 288#64) 64 = m.readBytes (sp + 176#64) 64 := by
  rw [nfsCopy288Mem_eq_writeBytes_48]
  set m_0 := (m.write64 (sp + 336#64) (m.read64 (sp + 224#64))).write64
    (sp + 344#64) (m.read64 (sp + 232#64))
  set m_384 := ((((m_0.write64 (sp + 352#64) (m.read64 (sp + 240#64))).write64
    (sp + 360#64) (m.read64 (sp + 248#64))).write64
    (sp + 368#64) (m.read64 (sp + 256#64))).write64
    (sp + 376#64) (m.read64 (sp + 264#64))).write64
    (sp + 384#64) nblk
  set m_all := m_384.writeBytes (sp + 288#64) (m.readBytes (sp + 176#64) 48)
  change m_all.readBytes (sp + 288#64) (48 + 16) = _
  rw [Bytes.readBytes_add m_all (sp + 288#64) 48 16]
  have h_lo : m_all.readBytes (sp + 288#64) 48 = m.readBytes (sp + 176#64) 48 :=
    Run.Layout.readBytes_writeBytes_eq m_384 (sp + 288#64) _ 48 (Memory.readBytes_length _ _ _) (by decide)
  have hag_48 : AgreesOutside m_384 m_all (sp + 288#64) 48 := by
    have hlen : (m.readBytes (sp + 176#64) 48).length = 48 := Memory.readBytes_length _ _ _
    rw [← hlen]; exact ProofLib.agreesOutside_writeBytes _ _ _
  have hag_mid : AgreesOutside m_0 m_384 (sp + 352#64) 40 := by
    dsimp only [m_384]; agrees_outside_writes
  have h336 : sp + 288#64 + 48#64 = sp + 336#64 := by bv_omega
  have hd_48 : DisjointRegions (sp + 288#64) 48 (sp + 336#64) 16 := by
    simp only [DisjointRegions]; bv_omega
  have hd_mid : DisjointRegions (sp + 352#64) 40 (sp + 336#64) 16 := by
    simp only [DisjointRegions]; bv_omega
  have h_hi : m_all.readBytes (sp + 288#64 + 48#64) 16 = m.readBytes (sp + 224#64) 16 := by
    rw [h336,
        (agreesOutside_toFrame hag_48).readBytes_eq (by simp [hd_48]) (by decide),
        (agreesOutside_toFrame hag_mid).readBytes_eq (by simp [hd_mid]) (by decide)]
    dsimp only [m_0]
    have hd1 : sp + 344#64 = (sp + 336#64) + 8#64 := by bv_omega
    have hs1 : sp + 232#64 = (sp + 224#64) + 8#64 := by bv_omega
    rw [hd1, hs1, write64_pair_read64_eq_writeBytes_16]
    exact Run.Layout.readBytes_writeBytes_eq m (sp + 336#64) _ 16 (Memory.readBytes_length _ _ _) (by decide)
  rw [h_lo, h_hi]
  have hs224 : sp + 224#64 = (sp + 176#64) + 48#64 := by bv_omega
  rw [hs224, ← Bytes.readBytes_add m (sp + 176#64) 48 16]

structure StateG2a (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) (b_iv : BitVec 64 := b)
    (pc_target : BitVec 64 := b + bv% (ls_off% "memset")) : Prop where
  pc_eq : s.pc = pc_target
  common : NfsGt64Common b_iv s₀ s
  x0_eq : s.readReg64 .x0 =
    nfsSp s₀ + 288#64 + BitVec.ofNat 64 (key.length - 64 * (key.length / 64)) + 1#64
  x1_eq : (s.readReg64 .x1).truncate 8 = 0#8
  x2_eq : (s.readReg64 .x2).toNat = 63 - (key.length - 64 * (key.length / 64))
  lr_eq : s.readReg64 .lr = b + 0x61c84#64
  x20_eq : s.readReg64 .x20 = nfsSp s₀ + 352#64
  x21_eq : s.readReg64 .x21 = BitVec.ofNat 64 (key.length / 64)
  x23_eq : s.readReg64 .x23 = BitVec.ofNat 64 (key.length - 64 * (key.length / 64))
  x24_eq : s.readReg64 .x24 = BitVec.ofNat 64 (63 - (key.length - 64 * (key.length / 64)))
  mem_copy : ∃ m_copy : Memory,
    s.mem = m_copy.write8
      (nfsSp s₀ + 288#64 + BitVec.ofNat 64 (key.length - 64 * (key.length / 64))) 128#8 ∧
    m_copy.readBytes (nfsSp s₀ + 288#64) (key.length - 64 * (key.length / 64)) =
      key.drop (64 * (key.length / 64)) ∧
    m_copy.readBytes (nfsSp s₀ + 352#64) 32 =
      shaStateBytes ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV)

structure StateG2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) (b_iv : BitVec 64 := b) : Prop where
  pc_eq : s.pc = b + 0x61c84#64
  common : NfsGt64Common b_iv s₀ s
  x20_eq : s.readReg64 .x20 = nfsSp s₀ + 352#64
  x21_eq : s.readReg64 .x21 = BitVec.ofNat 64 (key.length / 64)
  x23_eq : s.readReg64 .x23 = BitVec.ofNat 64 (key.length - 64 * (key.length / 64))
  x24_eq : s.readReg64 .x24 = BitVec.ofNat 64 (63 - (key.length - 64 * (key.length / 64)))
  buf_eq : s.mem.readBytes (nfsSp s₀ + 288#64) 64 =
    innerPadBlock1 (key.drop (64 * (key.length / 64)))
  st0_bytes : s.mem.readBytes (nfsSp s₀ + 352#64) 32 =
    shaStateBytes ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV)

set_option hygiene false in
local macro "nfs_seg0b1_gt64_body" : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, htail_bytes, hpos_byte, hst0_bytes, hnblk_word⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hag_zero⟩
  set tail := key.drop (64 * (key.length / 64))
  have htail_len : key.length - 64 * (key.length / 64) = tail.length := by simp [tail]
  rw [htail_len] at htail_bytes hpos_byte
  clear htail_len
  have htail_lt : tail.length < 64 := by simp [tail]; omega
  have hze32 := zeroExtend64_truncate32_ofNat64 htail_lt
  have hze64 := zeroExtend64_ofNat8 htail_lt
  have hxor63 := xor_63_of_lt_64 htail_lt
  have hcw_pos1 : s.mem.canWrite (nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length) 1 = true :=
    hRW_s.canWrite_sub (by bv_omega) (by decide)
  have hcw_pos2 : s.mem.canWrite (nfsSp s₀ + (288#64 + BitVec.ofNat 64 tail.length)) 1 = true :=
    hRW_s.canWrite_sub (by bv_omega) (by decide)
  iterate 20 sess_step
  refine RunsTo.refl ?_
  have hag_copy : AgreesOutside (nfsZeroMem s₀)
      (nfsCopy288Mem s.mem (nfsSp s₀) (BitVec.ofNat 64 (key.length / 64)))
      (nfsSp s₀ + 176#64) 288 :=
    agreesOutside_sub_176_288 hag_zero
      (agreesOutside_nfsCopy288Mem s.mem (nfsSp s₀) (BitVec.ofNat 64 (key.length / 64))) (by decide)
  have hag_pre_ms : AgreesOutside (nfsZeroMem s₀)
      ((nfsCopy288Mem s.mem (nfsSp s₀) (BitVec.ofNat 64 (key.length / 64))).write8
        (nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length) 128#8)
      (nfsSp s₀ + 176#64) 288 :=
    agreesOutside_sub_176_288 hag_copy
      (by
        rw [BitVec.add_assoc]
        exact AgreesOutside.write8_self _ (nfsSp s₀ + (288#64 + BitVec.ofNat 64 tail.length)) 128#8)
      (by bv_omega)
  have htoNat_sub : (BitVec.ofNat 64 (63 - tail.length)).toNat = 63 - tail.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx0_ms : nfsSp s₀ + (288#64 + (BitVec.ofNat 64 tail.length + 1#64)) =
      nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length + 1#64 := by
    simp only [BitVec.add_assoc]
  have htail_len' : tail.length = key.length - 64 * (key.length / 64) := by simp [tail]
  refine
    { pc_eq := by simp only [arm64_norm]
      common :=
        { status := by simp only [arm64_norm, hstat]
          sp_eq := by simp only [arm64_norm, hsp]
          sp_align := hal_nfs
          x29_eq := by simp only [arm64_norm, hx29]
          x19_eq := by simp only [arm64_norm, hx19]
          x22_eq := by simp only [arm64_norm, hx22]
          x25_eq := by simp only [arm64_norm, hx25]
          x26_eq := by simp only [arm64_norm, hx26]
          x27_eq := by simp only [arm64_norm, hx27]
          agrees_zero := by
            dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
            exact hag_pre_ms }
      x0_eq := by simp only [arm64_norm, hx0_ms, htail_len']
      x1_eq := by simp only [arm64_norm]
      x2_eq := by simp only [arm64_norm]; exact htail_len' ▸ htoNat_sub
      lr_eq := by simp only [arm64_norm]
      x20_eq := by simp only [arm64_norm]
      x21_eq := by simp only [arm64_norm]
      x23_eq := by simp only [arm64_norm, htail_len']
      x24_eq := by simp only [arm64_norm, htail_len']
      mem_copy := ⟨nfsCopy288Mem s.mem (nfsSp s₀) (BitVec.ofNat 64 (key.length / 64)),
        by
          dsimp only [State.setPC, State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
          rw [← htail_len', BitVec.add_assoc]
          rfl,
        by
          rw [← htail_len',
              readBytes_take_of_le _ (nfsSp s₀ + 288#64) (by omega : tail.length ≤ 64),
              readBytes_288_nfsCopy288Mem,
              ← readBytes_take_of_le s.mem (nfsSp s₀ + 176#64) (by omega : tail.length ≤ 64),
              htail_bytes],
        by rw [readBytes_352_nfsCopy288Mem, hst0_bytes]⟩ }))

set_option maxHeartbeats 1600000 in
theorem nfs_seg0b1_gt64 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG1 b F key s₀ s)
    (hkey_gt : 64 < key.length)
    (hkey_lt : key.length < 2 ^ 63)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (P b F alloc) s (StateG2a b F key s₀) := by
  nfs_seg0b1_gt64_body

set_option maxHeartbeats 1600000 in
theorem nfs_seg0b1_gt64_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG1 nfs3CodeFakeB F key s₀ s nfs3PlacedFakeB)
    (hkey_gt : 64 < key.length)
    (hkey_lt : key.length < 2 ^ 63)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (lsProg_402 H) s (StateG2a nfs3CodeFakeB F key s₀ · nfs3PlacedFakeB (lsmpl.ρ lsMemsetSym)) := by
  nfs_seg0b1_gt64_body

set_option hygiene false in
local macro "nfs_seg0b2_gt64_body " msLem:term:max : tactic => `(tactic| (
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hlr, hx20, hx21, hx23, hx24,
    ⟨m_copy, hmem_s, htail_copy, hst0_copy⟩⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hag_zero⟩
  set tail := key.drop (64 * (key.length / 64))
  have htail_len : key.length - 64 * (key.length / 64) = tail.length := by simp [tail]
  rw [htail_len] at hx0 hx2 hx23 hx24 hmem_s htail_copy
  clear htail_len
  have htail_lt : tail.length < 64 := by simp [tail]; omega
  set m_pre_ms := m_copy.write8 (nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length) 128#8
  have hrw_pre_ms : m_pre_ms.RW
      (nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length + 1#64) (63 - tail.length) := by
    rw [← hmem_s]
    exact hRW_s.sub (by bv_omega)
  refine $msLem
    hstat hpc hx0 hx1 hx2 hlr hmem_s hrw_pre_ms ?_
  refine RunsTo.refl ?_
  set m_end := m_pre_ms.writeBytes
    (nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length + 1#64)
    (List.replicate (63 - tail.length) 0#8)
  have hag_ms : AgreesOutside m_pre_ms m_end
      (nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length + 1#64) (63 - tail.length) := by
    have hlen : (List.replicate (63 - tail.length) 0#8).length = 63 - tail.length :=
      List.length_replicate
    rw [← hlen]
    exact ProofLib.agreesOutside_writeBytes m_pre_ms
      (nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length + 1#64)
      (List.replicate (63 - tail.length) 0#8)
  have hag_end : AgreesOutside (nfsZeroMem s₀) m_end (nfsSp s₀ + 176#64) 288 := by
    have h1 : AgreesOutside (nfsZeroMem s₀) m_pre_ms (nfsSp s₀ + 176#64) 288 := hmem_s ▸ hag_zero
    have h2 : AgreesOutside m_pre_ms m_end
        (nfsSp s₀ + (288#64 + BitVec.ofNat 64 tail.length + 1#64)) (63 - tail.length) := by
      simpa only [BitVec.add_assoc] using hag_ms
    exact agreesOutside_sub_176_288 h1 h2 (by bv_omega)
  have htail_len' : tail.length = key.length - 64 * (key.length / 64) := by simp [tail]
  refine
    { pc_eq := by simp only [arm64_norm]
      common :=
        { status := by simp only [arm64_norm, hstat]
          sp_eq := by simp only [arm64_norm, hsp]
          sp_align := hal_nfs
          x29_eq := by simp only [arm64_norm, hx29]
          x19_eq := by simp only [arm64_norm, hx19]
          x22_eq := by simp only [arm64_norm, hx22]
          x25_eq := by simp only [arm64_norm, hx25]
          x26_eq := by simp only [arm64_norm, hx26]
          x27_eq := by simp only [arm64_norm, hx27]
          agrees_zero := by rw [State.mem_setPC, State.mem_setMem]; exact hag_end }
      x20_eq := by simp only [arm64_norm, hx20]
      x21_eq := by simp only [arm64_norm, hx21]
      x23_eq := by simp only [arm64_norm, hx23, htail_len']
      x24_eq := by simp only [arm64_norm, hx24, htail_len']
      buf_eq := by
        rw [State.mem_setPC, State.mem_setMem]
        rw [readBytes_64_after_pad_memset_lt64 m_copy (nfsSp s₀ + 288#64) tail htail_copy htail_lt]
        rfl
      st0_bytes := by
        have hag_pad : AgreesOutside m_copy m_end (nfsSp s₀ + 288#64) 64 :=
          agreesOutside_pad_memset_lt64 m_copy (nfsSp s₀ + 288#64) tail htail_lt
        have hd : DisjointRegions (nfsSp s₀ + 288#64) 64 (nfsSp s₀ + 352#64) 32 := by
          clear * -; simp only [DisjointRegions]; bv_omega
        rw [State.mem_setPC, State.mem_setMem,
            (agreesOutside_toFrame hag_pad).readBytes_eq (by simp [hd]) (by decide),
            hst0_copy] }))

set_option maxHeartbeats 1600000 in
theorem nfs_seg0b2_gt64 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2a b F key s₀ s)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (P b F alloc) s (StateG2 b F key s₀) := by
  nfs_seg0b2_gt64_body RunsTo.sess_memset_step

set_option maxHeartbeats 1600000 in
theorem nfs_seg0b2_gt64_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memset : H lsMemsetSym = some memsetHook)
    {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2a nfs3CodeFakeB F key s₀ s nfs3PlacedFakeB (lsmpl.ρ lsMemsetSym))
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (lsProg_402 H) s (StateG2 nfs3CodeFakeB F key s₀ · nfs3PlacedFakeB) := by
  nfs_seg0b2_gt64_body (placed_memset_step h_memset)

theorem nfs_seg0b_gt64 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG1 b F key s₀ s)
    (hkey_gt : 64 < key.length)
    (hkey_lt : key.length < 2 ^ 63)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (P b F alloc) s (StateG2 b F key s₀) :=
  (nfs_seg0b1_gt64 hs hkey_gt hkey_lt hrw_stack).trans fun _ h2a =>
    nfs_seg0b2_gt64 h2a hrw_stack

theorem nfs_seg0b_gt64_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memset : H lsMemsetSym = some memsetHook)
    {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG1 nfs3CodeFakeB F key s₀ s nfs3PlacedFakeB)
    (hkey_gt : 64 < key.length)
    (hkey_lt : key.length < 2 ^ 63)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (lsProg_402 H) s (StateG2 nfs3CodeFakeB F key s₀ · nfs3PlacedFakeB) :=
  (nfs_seg0b1_gt64_placed hs hkey_gt hkey_lt hrw_stack).trans fun _ h2a =>
    nfs_seg0b2_gt64_placed h_memset h2a hrw_stack

theorem readBytes_400_copy (m : Memory) (sp : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64) :
    ((((((((m.write64 (sp + 400#64) v0).write64 (sp + 408#64) v1).write64
      (sp + 416#64) v2).write64 (sp + 424#64) v3).write64
      (sp + 432#64) v4).write64 (sp + 440#64) v5).write64
      (sp + 448#64) v6).write64 (sp + 456#64) v7).readBytes (sp + 400#64) 64 =
      toLEBytes 8 v0 ++ toLEBytes 8 v1 ++ toLEBytes 8 v2 ++ toLEBytes 8 v3 ++
      toLEBytes 8 v4 ++ toLEBytes 8 v5 ++ toLEBytes 8 v6 ++ toLEBytes 8 v7 := by
  have h1 : sp + 408#64 = (sp + 400#64) + 8#64 := by bv_omega
  have h2 : sp + 416#64 = (sp + 400#64) + 16#64 := by bv_omega
  have h3 : sp + 424#64 = (sp + 400#64) + 24#64 := by bv_omega
  have h4 : sp + 432#64 = (sp + 400#64) + 32#64 := by bv_omega
  have h5 : sp + 440#64 = (sp + 400#64) + 40#64 := by bv_omega
  have h6 : sp + 448#64 = (sp + 400#64) + 48#64 := by bv_omega
  have h7 : sp + 456#64 = (sp + 400#64) + 56#64 := by bv_omega
  rw [h1, h2, h3, h4, h5, h6, h7]
  exact readBytes_fsp_64_copy m (sp + 400#64) v0 v1 v2 v3 v4 v5 v6 v7

theorem readBytes_400_seg2 (m : Memory) (sp : BitVec 64)
    (v0 v1 v2 v3 w56 v4 v5 v6 v7 : BitVec 64) :
    (((((((((m.write64 (sp + 400#64) v0).write64 (sp + 408#64) v1).write64
      (sp + 416#64) v2).write64 (sp + 424#64) v3).write64 (sp + 344#64) w56).write64
      (sp + 432#64) v4).write64 (sp + 440#64) v5).write64
      (sp + 448#64) v6).write64 (sp + 456#64) v7).readBytes (sp + 400#64) 64 =
      toLEBytes 8 v0 ++ toLEBytes 8 v1 ++ toLEBytes 8 v2 ++ toLEBytes 8 v3 ++
      toLEBytes 8 v4 ++ toLEBytes 8 v5 ++ toLEBytes 8 v6 ++ toLEBytes 8 v7 := by
  have hm56 : sp + 344#64 = (sp + 288#64) + 56#64 := by bv_omega
  have h1 : sp + 408#64 = (sp + 400#64) + 8#64 := by bv_omega
  have h2 : sp + 416#64 = (sp + 400#64) + 16#64 := by bv_omega
  have h3 : sp + 424#64 = (sp + 400#64) + 24#64 := by bv_omega
  have h4 : sp + 432#64 = (sp + 400#64) + 32#64 := by bv_omega
  have h5 : sp + 440#64 = (sp + 400#64) + 40#64 := by bv_omega
  have h6 : sp + 448#64 = (sp + 400#64) + 48#64 := by bv_omega
  have h7 : sp + 456#64 = (sp + 400#64) + 56#64 := by bv_omega
  rw [hm56, h1, h2, h3, h4, h5, h6, h7]
  exact CryptoVerification.LibsignalTripleRatchet.readBytes_fsp_64_seg2
    m (sp + 288#64) (sp + 400#64) v0 v1 v2 v3 w56 v4 v5 v6 v7 (by simp only [DisjointRegions]; bv_omega)

theorem toLEBytes_read64_288_56 (m : Memory) (sp : BitVec 64) :
    toLEBytes 8 (m.read64 (sp + 288#64)) ++ toLEBytes 8 (m.read64 (sp + 296#64)) ++
      toLEBytes 8 (m.read64 (sp + 304#64)) ++ toLEBytes 8 (m.read64 (sp + 312#64)) ++
      toLEBytes 8 (m.read64 (sp + 320#64)) ++ toLEBytes 8 (m.read64 (sp + 328#64)) ++
      toLEBytes 8 (m.read64 (sp + 336#64)) = m.readBytes (sp + 288#64) 56 := by
  have h1 : sp + 296#64 = (sp + 288#64) + 8#64 := by bv_omega
  have h2 : sp + 304#64 = (sp + 288#64) + 16#64 := by bv_omega
  have h3 : sp + 312#64 = (sp + 288#64) + 24#64 := by bv_omega
  have h4 : sp + 320#64 = (sp + 288#64) + 32#64 := by bv_omega
  have h5 : sp + 328#64 = (sp + 288#64) + 40#64 := by bv_omega
  have h6 : sp + 336#64 = (sp + 288#64) + 48#64 := by bv_omega
  rw [h1, h2, h3, h4, h5, h6, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
      toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
      readBytes_56_eq_append_8 m (sp + 288#64)]

theorem toLEBytes_read64_288_64 (m : Memory) (sp : BitVec 64) :
    toLEBytes 8 (m.read64 (sp + 288#64)) ++ toLEBytes 8 (m.read64 (sp + 296#64)) ++
      toLEBytes 8 (m.read64 (sp + 304#64)) ++ toLEBytes 8 (m.read64 (sp + 312#64)) ++
      toLEBytes 8 (m.read64 (sp + 320#64)) ++ toLEBytes 8 (m.read64 (sp + 328#64)) ++
      toLEBytes 8 (m.read64 (sp + 336#64)) ++ toLEBytes 8 (m.read64 (sp + 344#64)) =
      m.readBytes (sp + 288#64) 64 := by
  have h7 : sp + 344#64 = (sp + 288#64) + 56#64 := by bv_omega
  rw [toLEBytes_read64_288_56 m sp, h7, toLEBytes_8_read64, ← Bytes.readBytes_add m (sp + 288#64) 56 8]

end CryptoVerification.SpqrV1.Kdf.NewFromSlice3GenProof

