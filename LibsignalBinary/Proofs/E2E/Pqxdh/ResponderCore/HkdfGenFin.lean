/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegs
import LibsignalBinary.Specifications.LibsignalE2E.State -- shake: keep

/-!
# Generalized Multi-Block `finalize_fixed` and `PqxdhHkdfExtractOk`

Generalizes `finalize_fixed` (`0x30680`) to multi-block `HmacStGen` (`blocks.length % 64 = 0`,
`blocks.length ≤ 192`, `rem.length < 56`), lifts `Hmac<Sha256>::new_from_slice` (`0x2b3b0`) to
`tripleRatchetProgAt` under `Initiator.FrozenRo`, and proves `PqxdhHkdfExtractOk` (`0x1ad38`) for
both `salt = some` (`32`-B IKM) and `salt = none` (`ikm.length ∈ {160, 192, 224}`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000


namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib ProofLib.Variant
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)

private theorem runsTo_kit_of_trap {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {s : State} {Q : State → Prop}
    (hQ : ∀ sf, Q sf → sf.status = .Running)
    (h : RunsTo (trTrapProgAt b C abs) s Q) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s Q := by
  intro hL
  have hL' : (trTrapProgAt b C abs).CodeLoaded s.mem :=
    (trTrapProgAt_codeLoaded_iff b C ctl abs s.mem).mpr hL
  obtain ⟨sf, hs, htr, hq, _⟩ := h hL'
  have hs' : Steps (tripleRatchetProgAt b C ctl abs) s sf :=
    Steps.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) hs (OutcomeStatus.of_running (hQ sf hq))
  exact ⟨sf, hs', htr, hq, hs'.codeLoaded hL⟩

private theorem runsToE_kit_of_trap {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {s : State} {Q : State → Prop}
    (hQ : ∀ sf, Q sf → sf.status = .Running)
    (h : Extract.RunsToE (trTrapProgAt b C abs) s Q) :
    Extract.RunsToE (tripleRatchetProgAt b C ctl abs) s Q := by
  intro hL
  have hL' : (trTrapProgAt b C abs).CodeLoaded s.mem :=
    (trTrapProgAt_codeLoaded_iff b C ctl abs s.mem).mpr hL
  obtain ⟨sf, hs, htr, hq, _⟩ := h hL'
  have hs' : Steps (tripleRatchetProgAt b C ctl abs) s sf :=
    Steps.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) hs (OutcomeStatus.of_running (hQ sf hq))
  exact ⟨sf, hs', htr, hq, hs'.codeLoaded hL⟩

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes


private theorem mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

macro "solve_fin_saved" : tactic =>
  `(tactic| (
    try rw [mem_setMem]
    simp (config := { decide := true }) only [arm64_norm]))

macro "fin_reg" : tactic =>
  `(tactic| (
    try rw [State.readReg64_setMem]
    try rw [State.pc_setMem]
    try rw [State.sp_setMem]
    try rw [State.status_setMem]
    simp (config := { decide := true }) only [arm64_norm, *]))

/-! ## Multi-Block `compress256Hook` Step and `chunks64` Helpers -/

@[simp] private theorem chunks64_length (bs : List (BitVec 8)) :
    (chunks64 bs).length = bs.length / 64 := by
  simp [chunks64]

@[simp] private theorem chunks64_getElem (bs : List (BitVec 8)) (i : ℕ)
    (hi : i < (chunks64 bs).length) :
    (chunks64 bs)[i] = (bs.drop (64 * i)).take 64 := by
  simp [chunks64]

theorem chunks64_of_lt {bs : List (BitVec 8)} (h : bs.length < 64) :
    chunks64 bs = [] := by
  rw [← List.length_eq_zero_iff, chunks64_length]
  omega

theorem chunks64_append_64 {a b : List (BitVec 8)} (ha : a.length = 64) :
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

theorem chunks64_single {a : List (BitVec 8)} (ha : a.length = 64) :
    chunks64 a = [a] := by
  conv_lhs => rw [← List.append_nil a]
  rw [chunks64_append_64 ha, chunks64_of_lt (by simp)]

theorem chunks64_append_mul {a b : List (BitVec 8)} (k : ℕ) (ha : a.length = 64 * k) :
    chunks64 (a ++ b) = chunks64 a ++ chunks64 b := by
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · simp [ha]; omega
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

theorem chunks64_append {a b : List (BitVec 8)} (ha : a.length % 64 = 0) :
    chunks64 (a ++ b) = chunks64 a ++ chunks64 b :=
  chunks64_append_mul (a.length / 64) (by omega)

theorem compress256Hook_multi_eq (F : ShaState → List (BitVec 8) → ShaState) {s : State}
    {stPtr blkPtr lr : BitVec 64} {nblk : ℕ} {st : ShaState} {blocks : List (BitVec 8)}
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : (s.readReg64 .x2).toNat = nblk)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr (64 * nblk) = blocks) :
    compress256Hook F s =
      (s.setMem (s.mem.writeBytes stPtr
        (shaStateBytes ((chunks64 blocks).foldl F st)))).setPC lr := by
  dsimp only [compress256Hook, returnToLinkRegister]
  have hlr' : (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
      (shaStateBytes
        ((chunks64 (s.mem.readBytes (s.readReg64 .x1) (64 * (s.readReg64 .x2).toNat))).foldl
        F (readShaState s.mem (s.readReg64 .x0)))))).readReg64 .lr = lr := by
    simpa [arm64_norm] using hlr
  rw [hlr', hx0, hx1, hx2, hblk, readShaState_of_shaStateBytes s.mem stPtr st hst]

theorem s2_compress256_multi_step_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {nblk : ℕ} {st : ShaState} {blocks : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = b + bv% (ls_off% "sha2::sha256::compress256"))
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : (s.readReg64 .x2).toNat = nblk)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr (64 * nblk) = blocks)
    (hrw : s.mem.RW stPtr 32)
    (h : RunsToFrom (trTrapProgAt b C abs) s₀
      ((s.setMem (s.mem.writeBytes stPtr
        (shaStateBytes ((chunks64 blocks).foldl C.F st)))).setPC lr) Q) :
    RunsToFrom (trTrapProgAt b C abs) s₀ s Q := by
  have hcan :
      s.mem.canWrite stPtr (shaStateBytes ((chunks64 blocks).foldl C.F st)).length = true := by
    rw [shaStateBytes_length]
    exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : (trTrapProgAt b C abs).externAt? s.pc = some (compress256Hook C.F) := by
    rw [hpc]; exact tripleRatchetProgAt_externAt_273212_trap b C abs
  have hstate := compress256Hook_multi_eq C.F hx0 hx1 hx2 hlr hst hblk
  have hkeep : s.mem.KeepsFrozen (compress256Hook C.F s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (compress256Hook C.F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

theorem s2_compress256_multi_step (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {nblk : ℕ} {st : ShaState} {blocks : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = b + bv% (ls_off% "sha2::sha256::compress256"))
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : (s.readReg64 .x2).toNat = nblk)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr (64 * nblk) = blocks)
    (hrw : s.mem.RW stPtr 32)
    (h : RunsToFrom (tripleRatchetProgAt b C ctl abs) s₀
      ((s.setMem (s.mem.writeBytes stPtr
        (shaStateBytes ((chunks64 blocks).foldl C.F st)))).setPC lr) Q) :
    RunsToFrom (tripleRatchetProgAt b C ctl abs) s₀ s Q := by
  have hcan :
      s.mem.canWrite stPtr (shaStateBytes ((chunks64 blocks).foldl C.F st)).length = true := by
    rw [shaStateBytes_length]
    exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : (tripleRatchetProgAt b C ctl abs).externAt? s.pc = some (compress256Hook C.F) := by
    rw [hpc]; exact tripleRatchetProgAt_externAt_273212 b C ctl abs
  have hstate := compress256Hook_multi_eq C.F hx0 hx1 hx2 hlr hst hblk
  have hkeep : s.mem.KeepsFrozen (compress256Hook C.F s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (compress256Hook C.F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

/-! ## Generalized `HmacStGen` and `hmacWith_gen` -/

/-- `Hmac<Sha256>` state at `a` after absorbing `blocks` (`blocks.length % 64 = 0`) into the inner
running state and buffering `rem` (`rem.length < 64`) at `a`. -/
def HmacStGen (m : Memory) (a : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) : Prop :=
  blocks.length % 64 = 0 ∧
  blocks.length ≤ 192 ∧
  rem.length < 64 ∧
  m.readBytes a rem.length = rem ∧
  m.read8 (a + 0x3f#64) = BitVec.ofNat 8 rem.length ∧
  m.readBytes (a + 0x40#64) 32 = shaStateBytes ((chunks64 blocks).foldl F (hmacInnerInit F key)) ∧
  m.read64 (a + 0x60#64) = BitVec.ofNat 64 (1 + blocks.length / 64) ∧
  m.readBytes (a + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key) ∧
  m.read64 (a + 0x88#64) = 1#64

theorem HmacStGen.of_agreesOutside {m₁ m₂ : Memory} {hm : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key blocks rem : List (BitVec 8)}
    {base : BitVec 64} {len : ℕ}
    (hst : HmacStGen m₁ hm F key blocks rem)
    (hag : AgreesOutside m₁ m₂ base len)
    (hd : DisjointRegions base len hm 0x90) :
    HmacStGen m₂ hm F key blocks rem := by
  rcases hst with ⟨hmod, hblk_le, hlen, hmsg, hpos, hin, hibl, hout, hobl⟩
  refine ⟨hmod, hblk_le, hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hm0 : rem.length = 0
    · simp [hm0] at hmsg ⊢; exact hmsg
    · have hd' : DisjointRegions base len hm rem.length :=
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

theorem HmacStGen.of_copy_19 {m₀ m : Memory} {src dst : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key blocks rem : List (BitVec 8)}
    (hsrc : HmacStGen m₀ src F key blocks rem)
    (h0   : m.read64 dst            = m₀.read64 src)
    (h8   : m.read64 (dst + 8#64)   = m₀.read64 (src + 8#64))
    (h16  : m.read64 (dst + 16#64)  = m₀.read64 (src + 16#64))
    (h24  : m.read64 (dst + 24#64)  = m₀.read64 (src + 24#64))
    (h32  : m.read64 (dst + 32#64)  = m₀.read64 (src + 32#64))
    (h40  : m.read64 (dst + 40#64)  = m₀.read64 (src + 40#64))
    (h48  : m.read64 (dst + 48#64)  = m₀.read64 (src + 48#64))
    (h56  : m.read64 (dst + 56#64)  = m₀.read64 (src + 56#64))
    (h64  : m.read64 (dst + 64#64)  = m₀.read64 (src + 64#64))
    (h72  : m.read64 (dst + 72#64)  = m₀.read64 (src + 72#64))
    (h80  : m.read64 (dst + 80#64)  = m₀.read64 (src + 80#64))
    (h88  : m.read64 (dst + 88#64)  = m₀.read64 (src + 88#64))
    (h96  : m.read64 (dst + 96#64)  = m₀.read64 (src + 96#64))
    (h104 : m.read64 (dst + 104#64) = m₀.read64 (src + 104#64))
    (h112 : m.read64 (dst + 112#64) = m₀.read64 (src + 112#64))
    (h120 : m.read64 (dst + 120#64) = m₀.read64 (src + 120#64))
    (h128 : m.read64 (dst + 128#64) = m₀.read64 (src + 128#64))
    (h136 : m.read64 (dst + 136#64) = m₀.read64 (src + 136#64)) :
    HmacStGen m dst F key blocks rem := by
  rcases hsrc with ⟨hmod, hblk_le, hlen, hmsg, hpos, hin, hcnt1, hout, hcnt2⟩
  refine ⟨hmod, hblk_le, hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h64_eq : m.readBytes dst 64 = m₀.readBytes src 64 := by
      rw [show (64 : ℕ) = 32 + 32 from rfl,
          Bytes.readBytes_add m dst 32 32, Bytes.readBytes_add m₀ src 32 32,
          readBytes_32_eq_of_read64_eq h0 h8 h16 h24,
          readBytes_32_eq_of_read64_eq h32
            (by simpa [BitVec.add_assoc] using h40)
            (by simpa [BitVec.add_assoc] using h48)
            (by simpa [BitVec.add_assoc] using h56)]
    have hslice1 := Bytes.readBytes_slice_of_readBytes_eq m dst (m₀.readBytes src 64)
      (by rw [Memory.readBytes_length]; exact h64_eq) 0 rem.length
      (by rw [Memory.readBytes_length]; omega)
    have hslice2 := Bytes.readBytes_slice_of_readBytes_eq m₀ src (m₀.readBytes src 64)
      (by rw [Memory.readBytes_length]) 0 rem.length
      (by rw [Memory.readBytes_length]; omega)
    simpa [hmsg] using hslice1.trans hslice2.symm
  · have hd : dst + 0x3f#64 = (dst + 56#64) + 7#64 := by bv_lin
    have hs : src + 0x3f#64 = (src + 56#64) + 7#64 := by bv_lin
    rw [hd, read8_add_7_of_read64_eq h56, ← hs, hpos]
  · rw [readBytes_32_eq_of_read64_eq h64
          (by simpa [BitVec.add_assoc] using h72)
          (by simpa [BitVec.add_assoc] using h80)
          (by simpa [BitVec.add_assoc] using h88), hin]
  · rw [show (0x60#64 : BitVec 64) = 96#64 from rfl, h96, ← hcnt1]
  · rw [readBytes_32_eq_of_read64_eq h104
          (by simpa [BitVec.add_assoc] using h112)
          (by simpa [BitVec.add_assoc] using h120)
          (by simpa [BitVec.add_assoc] using h128), hout]
  · rw [show (0x88#64 : BitVec 64) = 136#64 from rfl, h136, ← hcnt2]

/-- Final padded inner SHA-256 block when `blocks` (`blocks.length % 64 = 0`) has already been
absorbed and `rem.length < 56`. -/
def innerLastBlockGen (blocks rem : List (BitVec 8)) : List (BitVec 8) :=
  rem ++ [0x80] ++ List.replicate (55 - rem.length) 0 ++
    toBEBytes 8 (BitVec.ofNat 64 (8 * (64 + blocks.length + rem.length)))

theorem innerLastBlockGen_length {blocks rem : List (BitVec 8)} (hrem : rem.length < 56) :
    (innerLastBlockGen blocks rem).length = 64 := by
  simp [innerLastBlockGen, toBEBytes]; omega

theorem bit_len_inner_gen_eq {blocksLen n : ℕ} (hmod : blocksLen % 64 = 0)
    (hblk : blocksLen ≤ 192) (hn : n < 56) :
    BitVec.ofNat 64 (1 + blocksLen / 64) <<< 9 ||| BitVec.ofNat 64 n <<< 3 =
      BitVec.ofNat 64 (8 * (64 + blocksLen + n)) := by
  have hor_fin : ∀ (q : Fin 4) (m : Fin 56),
      BitVec.ofNat 64 (1 + q.val) <<< 9 ||| BitVec.ofNat 64 m.val <<< 3 =
        BitVec.ofNat 64 (512 * (1 + q.val)) + 8#64 * BitVec.ofNat 64 m.val := by
    decide
  have h1 : BitVec.ofNat 64 (512 * (1 + blocksLen / 64)) + 8#64 * BitVec.ofNat 64 n =
      BitVec.ofNat 64 (8 * (64 + blocksLen + n)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    change (512 * (1 + blocksLen / 64) % 18446744073709551616 +
      8 * (n % 18446744073709551616) % 18446744073709551616) % 18446744073709551616 =
      (8 * (64 + blocksLen + n)) % 18446744073709551616
    omega
  exact (hor_fin ⟨blocksLen / 64, by omega⟩ ⟨n, hn⟩).trans h1

theorem hmacWith_gen (F : ShaState → List (BitVec 8) → ShaState) (key blocks rem : List (BitVec 8))
    (hk : key.length ≤ 64) (hmod : blocks.length % 64 = 0) (hm : rem.length < 56) :
    hmacWith F key (blocks ++ rem) =
      digestBytes (F (hmacOuterInit F key)
        (outerBlock (digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
          (innerLastBlockGen blocks rem))))) := by
  unfold hmacWith
  have hk_not_gt : ¬ (64 < key.length) := by omega
  simp only [hk_not_gt, ↓reduceIte]
  change sha256With F ((hmacKeyBlock key).map (· ^^^ 0x5c) ++
    sha256With F ((hmacKeyBlock key).map (· ^^^ 0x36) ++ (blocks ++ rem))) = _
  have hkb_len : (hmacKeyBlock key).length = 64 := by
    simp [hmacKeyBlock]; omega
  have hipad_len : ((hmacKeyBlock key).map (· ^^^ 0x36)).length = 64 := by
    simp [hkb_len]
  have hopad_len : ((hmacKeyBlock key).map (· ^^^ 0x5c)).length = 64 := by
    simp [hkb_len]
  have hinner_blk_len : (innerLastBlockGen blocks rem).length = 64 :=
    innerLastBlockGen_length hm
  have hinner_pad : sha256Pad ((hmacKeyBlock key).map (· ^^^ 0x36) ++ (blocks ++ rem)) =
      (hmacKeyBlock key).map (· ^^^ 0x36) ++ blocks ++ innerLastBlockGen blocks rem := by
    unfold sha256Pad innerLastBlockGen
    have hlen : ((hmacKeyBlock key).map (· ^^^ 0x36) ++ (blocks ++ rem)).length =
        64 + blocks.length + rem.length := by
      simp [hkb_len]; omega
    have hmod' : (119 - (64 + blocks.length + rem.length) % 64) % 64 = 55 - rem.length := by omega
    rw [hlen, hmod']
    simp only [List.append_assoc]
  have hinner : sha256With F ((hmacKeyBlock key).map (· ^^^ 0x36) ++ (blocks ++ rem)) =
      digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
        (innerLastBlockGen blocks rem)) := by
    unfold sha256With digestBytes
    rw [hinner_pad, List.append_assoc,
        chunks64_append (by rw [hipad_len]),
        chunks64_single hipad_len,
        chunks64_append hmod,
        chunks64_single hinner_blk_len]
    simp [hmacInnerInit]
  rw [hinner]
  set d := digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
    (innerLastBlockGen blocks rem))
  have hd_len : d.length = 32 := digestBytes_length _
  have houter_blk_len : (outerBlock d).length = 64 := by
    simp [outerBlock, hd_len]
  have houter_pad : sha256Pad ((hmacKeyBlock key).map (· ^^^ 0x5c) ++ d) =
      (hmacKeyBlock key).map (· ^^^ 0x5c) ++ outerBlock d := by
    unfold sha256Pad outerBlock
    have hlen : ((hmacKeyBlock key).map (· ^^^ 0x5c) ++ d).length = 96 := by
      simp [hkb_len, hd_len]
    rw [hlen]
    simp only [List.append_assoc]
  unfold sha256With digestBytes
  rw [houter_pad, chunks64_append (by rw [hopad_len]),
      chunks64_single hopad_len, chunks64_single houter_blk_len]
  simp [hmacOuterInit]

/-! ## Generalized `finalize_fixed` (`0x30680`) for `HmacStGen` -/

structure FinGenPre (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 : State) : Prop where
  pc_eq        : s0.pc = b + 0x30764#64
  status       : s0.status = .Running
  key_le       : key.length ≤ 64
  rem_lt       : rem.length < 56
  hmac_st      : HmacStGen s0.mem (s0.readReg64 .x1) F key blocks rem
  rw_out       : RW s0.mem (s0.readReg64 .x0) 32
  rw_hm        : RW s0.mem (s0.readReg64 .x1) 0x90
  rw_fsp       : RW s0.mem (s0.sp - 144#64) 144
  disj_out_hm  : DisjointRegions (s0.readReg64 .x0) 32 (s0.readReg64 .x1) 0x90
  disj_out_fsp : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64) 144
  disj_hm_fsp  : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64) 144
  sp_aligned   : (s0.sp &&& 0b1111#64) = 0#64

private structure StateGF0p (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x30780#64
  common  : FinalizeFixedProof.FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x0
  x1_eq   : s.readReg64 .x1 = s0.readReg64 .x1
  hmac_st : HmacStGen s.mem (s0.readReg64 .x1) F key blocks rem

private structure StateGF1 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x307b0#64
  common  : FinalizeFixedProof.FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 rem.length
  x24_eq  : s.readReg64 .x24 = BitVec.ofNat 64 (1 + blocks.length / 64)
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 (63 - rem.length)
  buf_eq  : s.mem.readBytes (s0.readReg64 .x1) 64 =
    rem ++ [0x80#8] ++ List.replicate (63 - rem.length) 0#8
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes ((chunks64 blocks).foldl F (hmacInnerInit F key))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateGF2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x30814#64
  common  : FinalizeFixedProof.FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 = innerLastBlockGen blocks rem
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes ((chunks64 blocks).foldl F (hmacInnerInit F key))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateGF3 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x30818#64
  common  : FinalizeFixedProof.FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes
      (F ((chunks64 blocks).foldl F (hmacInnerInit F key)) (innerLastBlockGen blocks rem))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateGF3b (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x30894#64
  common  : FinalizeFixedProof.FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 =
    outerBlock (digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
      (innerLastBlockGen blocks rem)))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)

private structure StateGF4 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + 0x30898#64
  common  : FinalizeFixedProof.FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 =
    shaStateBytes (F (hmacOuterInit F key)
      (outerBlock (digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
        (innerLastBlockGen blocks rem)))))

private structure StateGF5 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = b + 0x30908#64
  common : FinalizeFixedProof.FinCommon s0 s
  out_eq : s.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key (blocks ++ rem)

variable {C : Crypto} {ctl : BitVec 64}
  {abs : String → Option (State → State)}

private theorem gseg1a_runsTo_trap {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 : State}
    (hpre : FinGenPre b C.F key blocks rem s0) :
    RunsTo (trTrapProgAt b C abs) s0 (StateGF0p b C.F key blocks rem s0) := by
  have hpc := hpre.pc_eq
  have hstat := hpre.status
  have hal0 : (s0.sp &&& 15#64) = 0#64 := hpre.sp_aligned
  have hal_fsp : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hrw_fsp : s0.mem.RW (s0.sp - 144#64) 144 := hpre.rw_fsp
  iterate 7 s2_step
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
  refine
    { pc_eq := by fin_reg
      common :=
        { status := by fin_reg, sp_eq := by fin_reg, x29_eq := by fin_reg,
          x26_eq := by fin_reg, x27_eq := by fin_reg, x28_eq := by fin_reg,
          saved := ⟨by solve_fin_saved, by solve_fin_saved, by solve_fin_saved,
                    by solve_fin_saved, by solve_fin_saved, by solve_fin_saved,
                    by solve_fin_saved, by solve_fin_saved, by solve_fin_saved⟩
          frame := Frame.trans_agreesOutside (Frame.refl s0.mem _) (by simp) hag }
      x0_eq := by fin_reg, x1_eq := by fin_reg
      hmac_st := HmacStGen.of_agreesOutside hpre.hmac_st hag hpre.disj_hm_fsp.symm }

private theorem gseg1a_runsTo {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 : State}
    (hpre : FinGenPre b C.F key blocks rem s0) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s0 (StateGF0p b C.F key blocks rem s0) := runsTo_kit_of_trap (fun _ h => h.common.status) (gseg1a_runsTo_trap hpre)

private theorem gseg1b_runsTo_trap {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre b C.F key blocks rem s0)
    (hs : StateGF0p b C.F key blocks rem s0 s) :
    RunsTo (trTrapProgAt b C abs) s (StateGF1 b C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hhmac⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  rcases hhmac with ⟨hmod, hblk_le, hmsg_lt64, hmsg_eq, hpos_eq, hin_eq, hibl_eq, hout_eq, hobl_eq⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hcw_pos : s.mem.canWrite (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 1 = true :=
    hrw_hm.canWrite_sub (by bv_omega) (by decide)
  have hze32 := zeroExtend64_truncate32_ofNat64 hmsg_lt64
  have hze64 := zeroExtend64_ofNat8 hmsg_lt64
  have hxor63 := xor_63_of_lt_64 hmsg_lt64
  iterate 12 s2_step
  have htoNat_sub : (BitVec.ofNat 64 (63 - rem.length)).toNat = 63 - rem.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrw_memset :
      (s.mem.write8 (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 128#8).RW
        (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length + 1#64) (63 - rem.length) := by
    refine Memory.RW.of_perm_eq (by simp) (fun _ => Memory.isLazyFree_write8_of_false _ _) (hrw_hm.sub ?_)
    have := hpre.rem_lt
    bv_omega
  refine s2_memset_step_trap b C abs
    (dst := s0.readReg64 .x1 + BitVec.ofNat 64 rem.length + 1#64)
    (lr := b + 0x307b0#64) (len := 63 - rem.length)
    hstat rfl
    (by simp only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm]) htoNat_sub rfl hrw_memset ?_
  refine RunsTo.refl ?_
  have hag := agreesOutside_pad_memset s.mem (s0.readReg64 .x1) rem hpre.rem_lt
  have hd_hm64_fsp : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := rfl
      common :=
        { status := by fin_reg, sp_eq := by fin_reg, x29_eq := by fin_reg,
          x26_eq := by fin_reg, x27_eq := by fin_reg, x28_eq := by fin_reg,
          saved := FinSaved.of_agreesOutside hsaved hag hd_hm64_fsp
          frame := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag }
      x19_eq := by fin_reg, x20_eq := by fin_reg, x21_eq := by fin_reg,
      x22_eq := by fin_reg, x23_eq := by fin_reg, x24_eq := by fin_reg, x25_eq := by fin_reg,
      buf_eq := readBytes_64_after_pad_memset s.mem (s0.readReg64 .x1) rem hmsg_eq hpre.rem_lt
      ist_eq := (hag.readBytes_eq hd_hm64_ist (by decide)).trans hin_eq
      ost_eq := (hag.readBytes_eq hd_hm64_ost (by decide)).trans hout_eq
      obl_eq := (hag.read64_eq hd_hm64_obl).trans hobl_eq }

private theorem gseg1b_runsTo {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre b C.F key blocks rem s0)
    (hs : StateGF0p b C.F key blocks rem s0 s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s (StateGF1 b C.F key blocks rem s0) := runsTo_kit_of_trap (fun _ h => h.common.status) (gseg1b_runsTo_trap hpre hs)

private theorem gseg2a_runsTo_trap {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre b C.F key blocks rem s0)
    (hs : StateGF1 b C.F key blocks rem s0 s) :
    RunsTo (trTrapProgAt b C abs) s (StateGF2 b C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hult_7 := ult_7_of_lt_56 hpre.rem_lt
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  iterate 6 s2_step
  have hread32 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 32#64 (by decide) hd_hm64_fsp64
  have hread40 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 40#64 (by decide) hd_hm64_fsp64
  have hread48 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 48#64 (by decide) hd_hm64_fsp64
  iterate 7 s2_step
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
    { pc_eq := by fin_reg
      common :=
        { status := by fin_reg, sp_eq := by fin_reg, x29_eq := by fin_reg,
          x26_eq := by fin_reg, x27_eq := by fin_reg, x28_eq := by fin_reg,
          saved := by
            rw [mem_setMem]
            exact FinSaved.of_agreesOutside
              (FinSaved.of_agreesOutside (FinSaved.of_agreesOutside hsaved hag1 hd_fsp64_saved)
                hag2 hd_hm64_saved) hag3 hd_fsp64_saved
          frame := by rw [mem_setMem]; exact frame_seg2a hframe hag1 hag2 hag3 }
      x0_eq := by fin_reg, x1_eq := by fin_reg, x2_eq := by fin_reg,
      x19_eq := by fin_reg, x20_eq := by fin_reg, x21_eq := by fin_reg, x22_eq := by fin_reg
      blk_eq := by
        rw [mem_setMem]
        refine (readBytes_fsp_64_seg2 _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
        rw [toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
            toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_rev64,
            readBytes_56_eq_append_8 s.mem (s0.readReg64 .x1),
            readBytes_56_of_buf_eq s.mem (s0.readReg64 .x1) rem hbuf hpre.rem_lt,
            bit_len_inner_gen_eq hpre.hmac_st.1 hpre.hmac_st.2.1 hpre.rem_lt]
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
            ((hag1.read64_eq hd_fsp64_obl).trans hobl)) }

private theorem gseg2a_runsTo {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre b C.F key blocks rem s0)
    (hs : StateGF1 b C.F key blocks rem s0 s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s (StateGF2 b C.F key blocks rem s0) := runsTo_kit_of_trap (fun _ h => h.common.status) (gseg2a_runsTo_trap hpre hs)

private theorem gseg2b_runsTo_trap {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre b C.F key blocks rem s0)
    (hs : StateGF2 b C.F key blocks rem s0 s) :
    RunsTo (trTrapProgAt b C abs) s (StateGF3 b C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hblk, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_ist : s.mem.RW (s0.readReg64 .x1 + 0x40#64) 32 := hrw_hm.sub (by bv_omega)
  s2_step
  refine s2_compress256_step_trap b C abs
    (stPtr := s0.readReg64 .x1 + 0x40#64) (blkPtr := s0.sp - 144#64)
    (lr := b + 0x30818#64) (st := (chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
    (blk := innerLastBlockGen blocks rem)
    hstat rfl
    (by fin_reg) (by fin_reg) (by fin_reg) rfl
    hist hblk (innerLastBlockGen_length hpre.rem_lt) hrw_ist ?_
  refine RunsTo.refl ?_
  set blk_in := shaStateBytes (C.F ((chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
    (innerLastBlockGen blocks rem))
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x40#64) blk_in)
      (s0.readReg64 .x1 + 0x40#64) 32 := by
    have hlen : blk_in.length = 32 := shaStateBytes_length _
    rw [← hlen]
    exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_in
  have hd_ist_saved :
      DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_ist_ost :
      DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_ist_obl :
      DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := rfl
      common :=
        { status := by fin_reg, sp_eq := by fin_reg, x29_eq := by fin_reg,
          x26_eq := by fin_reg, x27_eq := by fin_reg, x28_eq := by fin_reg,
          saved := FinSaved.of_agreesOutside hsaved hag_comp hd_ist_saved
          frame := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin_reg, x20_eq := by fin_reg, x21_eq := by fin_reg, x22_eq := by fin_reg
      ist_eq := by
        have hlen : blk_in.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact Bytes.readBytes_writeBytes_same s.mem _ blk_in (by rw [hlen]; decide)
      ost_eq := (hag_comp.readBytes_eq hd_ist_ost (by decide)).trans host
      obl_eq := (hag_comp.read64_eq hd_ist_obl).trans hobl }

private theorem gseg2b_runsTo {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre b C.F key blocks rem s0)
    (hs : StateGF2 b C.F key blocks rem s0 s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s (StateGF3 b C.F key blocks rem s0) := runsTo_kit_of_trap (fun _ h => h.common.status) (gseg2b_runsTo_trap hpre hs)

private theorem gseg3a_runsTo_trap {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre b C.F key blocks rem s0)
    (hs : StateGF3 b C.F key blocks rem s0 s) :
    RunsTo (trTrapProgAt b C abs) s (StateGF3b b C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_in := C.F ((chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
    (innerLastBlockGen blocks rem)
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_64_of_shaStateBytes s.mem (s0.readReg64 .x1) h_in hist
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hrev768 : rev64 (256#64 ||| 512#64) = 0x0003000000000000#64 := by decide
  have hread32 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
    read64_seg3a_pad_32 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
  have hread40 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
    read64_seg3a_pad_40 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
  iterate 31 s2_step
  clear hread32 hread40 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hist
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg3a s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
    _ _ _ _ _ _ _ _ _ _ _ _ 0#64 0x0003000000000000#64 0x80#64 0#64 0#64 0x0003000000000000#64
  have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  refine
    { pc_eq := by fin_reg
      common :=
        { status := by fin_reg, sp_eq := by fin_reg, x29_eq := by fin_reg,
          x26_eq := by fin_reg, x27_eq := by fin_reg, x28_eq := by fin_reg,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg3a hsaved hag1 hag2 hag3 hag4 hd_hm64_saved hd_fsp64_saved
          frame := by rw [mem_setMem]; exact frame_seg3a hframe hag1 hag2 hag3 hag4 }
      x0_eq := by fin_reg, x1_eq := by fin_reg, x2_eq := by fin_reg,
      x19_eq := by fin_reg, x20_eq := by fin_reg
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
        exact ost_eq_seg3a host hag1 hag2 hag3 hag4 hd_hm64_ost hd_fsp64_ost }

private theorem gseg3a_runsTo {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre b C.F key blocks rem s0)
    (hs : StateGF3 b C.F key blocks rem s0 s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s (StateGF3b b C.F key blocks rem s0) := runsTo_kit_of_trap (fun _ h => h.common.status) (gseg3a_runsTo_trap hpre hs)

private theorem gseg3b_runsTo_trap {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre b C.F key blocks rem s0)
    (hs : StateGF3b b C.F key blocks rem s0 s) :
    RunsTo (trTrapProgAt b C abs) s (StateGF4 b C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hblk, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_ost : s.mem.RW (s0.readReg64 .x1 + 0x68#64) 32 := hrw_hm.sub (by bv_omega)
  set h_in := C.F ((chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
    (innerLastBlockGen blocks rem)
  s2_step
  refine s2_compress256_step_trap b C abs
    (stPtr := s0.readReg64 .x1 + 0x68#64) (blkPtr := s0.sp - 144#64)
    (lr := b + 0x30898#64) (st := hmacOuterInit C.F key) (blk := outerBlock (digestBytes h_in))
    hstat rfl
    (by fin_reg) (by fin_reg) (by fin_reg) rfl
    host hblk (outerBlock_digestBytes_length h_in) hrw_ost ?_
  refine RunsTo.refl ?_
  set blk_out := shaStateBytes (C.F (hmacOuterInit C.F key) (outerBlock (digestBytes h_in)))
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x68#64) blk_out)
      (s0.readReg64 .x1 + 0x68#64) 32 := by
    have hlen : blk_out.length = 32 := shaStateBytes_length _
    rw [← hlen]
    exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_out
  have hd_ost_saved :
      DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  refine
    { pc_eq := rfl
      common :=
        { status := by fin_reg, sp_eq := by fin_reg, x29_eq := by fin_reg,
          x26_eq := by fin_reg, x27_eq := by fin_reg, x28_eq := by fin_reg,
          saved := FinSaved.of_agreesOutside hsaved hag_comp hd_ost_saved
          frame := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin_reg, x20_eq := by fin_reg
      ost_eq := by
        have hlen : blk_out.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact Bytes.readBytes_writeBytes_same s.mem _ blk_out (by rw [hlen]; decide) }

private theorem gseg3b_runsTo {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre b C.F key blocks rem s0)
    (hs : StateGF3b b C.F key blocks rem s0 s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s (StateGF4 b C.F key blocks rem s0) := runsTo_kit_of_trap (fun _ h => h.common.status) (gseg3b_runsTo_trap hpre hs)

private theorem read32_gseg4a_mid (m : Memory) (hm fsp off : BitVec 64) (w : BitVec 32)
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

private theorem gseg4a_disj {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {key blocks rem : List (BitVec 8)} {s0 : State} (hpre : FinGenPre b F key blocks rem s0) :
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

private theorem gseg4a_runsTo_trap {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre b C.F key blocks rem s0)
    (hs : StateGF4 b C.F key blocks rem s0 s) :
    RunsTo (trTrapProgAt b C abs) s (StateGF5 b C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 32 := rw_of_perm_eq hframe.2 hpre.rw_out
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_out := C.F (hmacOuterInit C.F key)
    (outerBlock (digestBytes (C.F ((chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
      (innerLastBlockGen blocks rem))))
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_104_of_shaStateBytes s.mem (s0.readReg64 .x1) h_out host
  have hzero64 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
  iterate 11 s2_step
  have hd_fsp64_hm := (gseg4a_disj hpre).1
  have hread128 := read32_gseg4a_mid s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 128#64 (h_out.get 6)
    (Or.inl rfl) hd_fsp64_hm hw6
  have hread132 := read32_gseg4a_mid s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 132#64 (h_out.get 7)
    (Or.inr rfl) hd_fsp64_hm hw7
  iterate 2 s2_step
  clear hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hread128 hread132 hd_fsp64_hm host
  iterate 15 s2_step
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg4a s.mem
    (s0.readReg64 .x0) (s0.readReg64 .x1) (s0.sp - 144#64) _ _ _ _ _ _ _ _
  obtain ⟨_, hd_hm_saved, hd_fsp64_saved, hd_out_saved⟩ := gseg4a_disj hpre
  refine
    { pc_eq := by fin_reg
      common :=
        { status := by fin_reg, sp_eq := by fin_reg, x29_eq := by fin_reg,
          x26_eq := by fin_reg, x27_eq := by fin_reg, x28_eq := by fin_reg,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg4a hsaved hag1 hag2 hag3 hag4 hd_hm_saved hd_fsp64_saved hd_out_saved
          frame := by rw [mem_setMem]; exact frame_seg4a hframe hag1 hag2 hag3 hag4 }
      out_eq := by
        rw [mem_setMem]
        exact (readBytes_write32_8_digestBytes _ (s0.readReg64 .x0) h_out _ _ _ _ _ _ _ _
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
          (toLEBytes_4_rev32 _)).trans
          (hmacWith_gen C.F key blocks rem hpre.key_le hpre.hmac_st.1 hpre.rem_lt).symm }

private theorem gseg4a_runsTo {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre b C.F key blocks rem s0)
    (hs : StateGF4 b C.F key blocks rem s0 s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s (StateGF5 b C.F key blocks rem s0) := runsTo_kit_of_trap (fun _ h => h.common.status) (gseg4a_runsTo_trap hpre hs)

private theorem gseg4b_runsTo_trap {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre b C.F key blocks rem s0)
    (hs : StateGF5 b C.F key blocks rem s0 s) :
    RunsTo (trTrapProgAt b C abs) s
      (FinalizeFixedProof.FinPost C.F key (blocks ++ rem) s0) := by
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
  iterate 7 s2_step
  refine RunsTo.refl ⟨by simp (config := { decide := true }) only [arm64_norm], hstat,
    ⟨by simp (config := { decide := true }) only [arm64_norm], fun r hr => ?_⟩, hout, hframe⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [arm64_norm, hx26, hx27, hx28]

private theorem gseg4b_runsTo {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre b C.F key blocks rem s0)
    (hs : StateGF5 b C.F key blocks rem s0 s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s
      (FinalizeFixedProof.FinPost C.F key (blocks ++ rem) s0) := runsTo_kit_of_trap (fun _ h => h.2.1) (gseg4b_runsTo_trap hpre hs)

theorem finalize_fixed_gen_runsTo_trap {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 : State}
    (hpre : FinGenPre b C.F key blocks rem s0) :
    RunsTo (trTrapProgAt b C abs) s0
      (FinalizeFixedProof.FinPost C.F key (blocks ++ rem) s0) :=
  (gseg1a_runsTo_trap hpre).trans fun _ hs1 =>
  (gseg1b_runsTo_trap hpre hs1).trans fun _ hs2 =>
  (gseg2a_runsTo_trap hpre hs2).trans fun _ hs3 =>
  (gseg2b_runsTo_trap hpre hs3).trans fun _ hs4 =>
  (gseg3a_runsTo_trap hpre hs4).trans fun _ hs5 =>
  (gseg3b_runsTo_trap hpre hs5).trans fun _ hs6 =>
  (gseg4a_runsTo_trap hpre hs6).trans fun _ hs7 =>
  gseg4b_runsTo_trap hpre hs7

/-- Generalized `RunsTo` contract of `finalize_fixed` (`0x30680 → s0.readReg64 .lr`) for
multi-block `HmacStGen`. -/
theorem finalize_fixed_gen_runsTo {b : BitVec 64} {key blocks rem : List (BitVec 8)} {s0 : State}
    (hpre : FinGenPre b C.F key blocks rem s0) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s0
      (FinalizeFixedProof.FinPost C.F key (blocks ++ rem) s0) := runsTo_kit_of_trap (fun _ h => h.2.1) (finalize_fixed_gen_runsTo_trap hpre)

theorem roDataLoaded_of_keepsFrozen {img : Obj.Image} {m m' : Memory}
    (hro : img.RoDataLoaded m) (hk : m.KeepsFrozen m') : img.RoDataLoaded m' := by
  intro i hi
  change img.isRoData (img.dataAddr + BitVec.ofNat 64 i) = true →
    m'.read8 (img.dataAddr + BitVec.ofNat 64 i) = img.data[i] ∧
    m'.perm (img.dataAddr + BitVec.ofNat 64 i) = some Perm.ro ∧
    m'.isLazyFree (img.dataAddr + BitVec.ofNat 64 i) = false
  intro hro_i
  obtain ⟨hb, hp, hlf⟩ := hro i hi hro_i
  have hf : m.Frozen (img.dataAddr + BitVec.ofNat 64 i) := by
    unfold Memory.Frozen; rw [hp]; rfl
  obtain ⟨hb', hp', hlf', _⟩ := hk _ hf
  exact ⟨hb'.trans hb, hp'.trans hp, hlf'.trans hlf⟩

theorem nfs32_ro_runsTo_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {ret keyA : BitVec 64} {key : List (BitVec 8)}
    (hro : img.RoDataLoaded s.mem)
    (hpc : s.pc = img.base + 0x2b494#64)
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ret)
    (hx1 : s.readReg64 .x1 = keyA)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hkey_mem : s.mem.readBytes keyA 32 = key)
    (hrw_ret : RW s.mem ret 0x98)
    (hrw_stk : RW s.mem (s.sp - 544#64) 544)
    (hd_ret_stk : DisjointRegions ret 0x98 (s.sp - 544#64) 544)
    (hd_key_stk : DisjointRegions keyA 32 (s.sp - 544#64) 544)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    Extract.RunsToE (trTrapProgAt img.base C abs) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.read64 ret = 0#64 ∧
      HmacSt s'.mem (ret + 8#64) C.F key [] ∧
      Extract.S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 544#64, 544)]) := by
  intro hL2
  have hL1 : (LibsignalSession.CryptoHmacSha256.P img.base C.F abs).CodeLoaded s.mem := by
    rw [Program.codeLoaded_iff] at hL2 ⊢
    dsimp only [LibsignalSession.CryptoHmacSha256.P, tripleRatchetProgAt, Program.rebase] at hL2 ⊢
    exact hL2
  obtain ⟨hro_iv, hiv_eq⟩ := LibsignalSession.CryptoHmacSha256.rodata_sha256IV himg hro
  have hread_iv : s.mem.Readable (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 := by
    intro a ha; exact ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hx2_nat : (s.readReg64 .x2).toNat = 32 := by rw [hx2]; rfl
  have hrun := LibsignalSession.CryptoHmacSha256.new_from_slice_run
    (b := img.base) (F := C.F) (alloc := abs)
    hpc hstat (by rw [hx2_nat]; decide) hiv_eq (ProofLib.base_aligned_of_loads himg)
    hread_iv
    (LibsignalSession.CryptoHmacSha256.disjointRegions_of_ro_rw
      (by decide) (by decide) hro_iv hrw_stk)
    (by rw [hx0]; exact hrw_ret) hrw_stk
    (by rw [hx0]; exact hd_ret_stk)
    (by rw [hx1, hx2_nat]; exact Or.inr hd_key_stk)
    hsp_al
  obtain ⟨s', hsteps1, htr, hvregs, ⟨hpc', hstat', hcs, hret', hhm', hfr'⟩, _⟩ := hrun hL1
  have htr_eq : TraceEq s s' := ⟨htr, hvregs⟩
  rw [hx0] at hret' hhm' hfr'
  rw [hx1, hx2_nat, hkey_mem] at hhm'
  have hnh : s'.status ≠ .Halted := by rw [hstat']; intro h; injection h
  have hsteps2 : Steps (trTrapProgAt img.base C abs) s s' :=
    ConsumeMessageKeyTransfer.steps_mono libsignalSessionCode_stubs_offsets_fresh
      ConsumeMessageKeyTransfer.libsignalSessionCode_stubsDead
      (ConsumeMessageKeyTransfer.sessionExterns_le_trap C abs)
      hsteps1 hL1 hnh
  exact ⟨s', hsteps2, htr_eq,
    ⟨hpc', hstat', CallingConventionPreserved_of_calleeSaved hcs htr_eq,
      hret', hhm', Extract.S2Frame.of_frame hfr'⟩,
    hsteps2.codeLoaded hL2⟩

theorem nfs32_ro_runsTo {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {ret keyA : BitVec 64} {key : List (BitVec 8)}
    (hro : img.RoDataLoaded s.mem)
    (hpc : s.pc = img.base + 0x2b494#64)
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ret)
    (hx1 : s.readReg64 .x1 = keyA)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hkey_mem : s.mem.readBytes keyA 32 = key)
    (hrw_ret : RW s.mem ret 0x98)
    (hrw_stk : RW s.mem (s.sp - 544#64) 544)
    (hd_ret_stk : DisjointRegions ret 0x98 (s.sp - 544#64) 544)
    (hd_key_stk : DisjointRegions keyA 32 (s.sp - 544#64) 544)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    Extract.RunsToE (tripleRatchetProgAt img.base C ctl abs) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.read64 ret = 0#64 ∧
      HmacSt s'.mem (ret + 8#64) C.F key [] ∧
      Extract.S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 544#64, 544)]) := runsToE_kit_of_trap (fun _ h => h.2.1) (nfs32_ro_runsTo_trap himg hro hpc hstat hx0 hx1 hx2 hkey_mem hrw_ret hrw_stk hd_ret_stk hd_key_stk hsp_al)

theorem nfs1_ro_runsTo_trap {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hro0 : img.RoDataLoaded s0.mem)
    (hkf : s0.mem.KeepsFrozen s.mem)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hd_salt_544 : DisjointRegions (Extract.saltPtrOf sp0 x) 32 (sp0 - 544#64) 544)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hsalt_none : x.salt = none → x.saltA = 0#64)
    (hs : Extract.ENfs1 img.base x s0 sp0 s) :
    Extract.RunsToE (trTrapProgAt img.base C abs) s
      (Extract.ERet1 img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx20, hx21, hsalt_some_ne, hsalt_mem⟩
  have hreg_eq : Extract.saltRegOf sp0 x = Extract.saltPtrOf sp0 x := by
    cases hsalt : x.salt with
    | none => simp [Extract.saltRegOf, Extract.saltPtrOf, hsalt, hsalt_none hsalt]
    | some sv => simp [Extract.saltRegOf, Extract.saltPtrOf, hsalt, hsalt_some_ne sv hsalt]
  have hslice_eq : Extract.saltSliceOf x = effectiveSalt x.salt := by
    cases hsalt : x.salt with
    | none => simp [Extract.saltSliceOf, effectiveSalt, hsalt, hsalt_none hsalt]
    | some sv => simp [Extract.saltSliceOf, effectiveSalt, hsalt]
  have hslice_len : (Extract.saltSliceOf x).length = 32 := by
    rw [hslice_eq, Extract.effectiveSalt_length]
  rw [hreg_eq] at hx1
  rw [hslice_len] at hx2 hsalt_mem
  rw [hslice_eq] at hsalt_mem
  have hsub_x0 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x98 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_544 : 0 < 544 ∧ ((sp0 - 544#64) - (sp0 - 544#64)).toNat + 544 ≤ 976 := by
    have heq : (sp0 - 544#64) - (sp0 - 544#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 544#64)).toNat + 96 ≤ 976 := by
    have heq : (sp0 + 336#64) - (sp0 - 544#64) = 880#64 := by bv_lin
    rw [heq]; decide
  have hrun := nfs32_ro_runsTo_trap (C := C) (abs := abs) himg
    (roDataLoaded_of_keepsFrozen hro0 hkf)
    hpc hstat hx0 hx1 hx2 hsalt_mem
    (hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_x0.2))
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_544.2))
    (by rw [hsp]; exact (Extract.disj_sp0_sub_off sp0 544#64 544 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact hd_salt_544)
    (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8] at hhm
  have hsaved' : Extract.ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Extract.disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact Extract.disj_sp0_sub_off sp0 544#64 544 336#64 96 (by decide)
  have hframe' : Extract.ExtFrame s0 sp0 s'.mem :=
    hframe.trans_pair hfr' hsub_x0.2 hsub_544.2
  exact ⟨⟨hstat', (Extract.CallingConventionPreserved.sp_eq hcs).trans hsp,
    (Extract.CallingConventionPreserved.x19 hcs).trans hx19,
    (Extract.CallingConventionPreserved.x27 hcs).trans hx27,
    (Extract.CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr, (Extract.CallingConventionPreserved.x20 hcs).trans hx20,
    (Extract.CallingConventionPreserved.x21 hcs).trans hx21, hok, hhm⟩

theorem nfs1_ro_runsTo {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hro0 : img.RoDataLoaded s0.mem)
    (hkf : s0.mem.KeepsFrozen s.mem)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hd_salt_544 : DisjointRegions (Extract.saltPtrOf sp0 x) 32 (sp0 - 544#64) 544)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hsalt_none : x.salt = none → x.saltA = 0#64)
    (hs : Extract.ENfs1 img.base x s0 sp0 s) :
    Extract.RunsToE (tripleRatchetProgAt img.base C ctl abs) s
      (Extract.ERet1 img.base C.F x s0 sp0) := runsToE_kit_of_trap (fun _ h => h.1.1) (nfs1_ro_runsTo_trap himg hro0 hkf hRW_stk hd_salt_544 hsp_al hsalt_none hs)

theorem nfs2_ro_runsTo_trap {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hro0 : img.RoDataLoaded s0.mem)
    (hkf : s0.mem.KeepsFrozen s.mem)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : Extract.ENfs2 img.base C.F x s0 sp0 s) :
    Extract.RunsToE (trTrapProgAt img.base C abs) s
      (Extract.ERet2 img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx22, hprk⟩
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hsub_x0 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x98 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_544 : 0 < 544 ∧ ((sp0 - 544#64) - (sp0 - 544#64)).toNat + 544 ≤ 976 := by
    have heq : (sp0 - 544#64) - (sp0 - 544#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 544#64)).toNat + 96 ≤ 976 := by
    have heq : (sp0 + 336#64) - (sp0 - 544#64) = 880#64 := by bv_lin
    rw [heq]; decide
  have hrw_144_s : s.mem.RW (sp0 + 144#64) 32 :=
    hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_144.2)
  have hrun := nfs32_ro_runsTo_trap (C := C) (abs := abs) himg
    (roDataLoaded_of_keepsFrozen hro0 hkf)
    hpc hstat hx0 hx1 hx2 hprk
    (hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_x0.2))
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_544.2))
    (by rw [hsp]; exact (Extract.disj_sp0_sub_off sp0 544#64 544 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact (Extract.disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)).symm)
    (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8] at hhm
  have hprk' : s'.mem.readBytes (sp0 + 144#64) 32 = x.prk C.F := by
    rw [hfr'.readBytes_eq hrw_144_s ?_ (by decide)]
    · exact hprk
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (Extract.disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)).symm
      · exact Extract.disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)
  have hsaved' : Extract.ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Extract.disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact Extract.disj_sp0_sub_off sp0 544#64 544 336#64 96 (by decide)
  have hframe' : Extract.ExtFrame s0 sp0 s'.mem :=
    hframe.trans_pair hfr' hsub_x0.2 hsub_544.2
  exact ⟨⟨hstat', (Extract.CallingConventionPreserved.sp_eq hcs).trans hsp,
    (Extract.CallingConventionPreserved.x19 hcs).trans hx19,
    (Extract.CallingConventionPreserved.x27 hcs).trans hx27,
    (Extract.CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr, (Extract.CallingConventionPreserved.x22 hcs).trans hx22, hok, hprk', hhm⟩

theorem nfs2_ro_runsTo {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hro0 : img.RoDataLoaded s0.mem)
    (hkf : s0.mem.KeepsFrozen s.mem)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : Extract.ENfs2 img.base C.F x s0 sp0 s) :
    Extract.RunsToE (tripleRatchetProgAt img.base C ctl abs) s
      (Extract.ERet2 img.base C.F x s0 sp0) := runsToE_kit_of_trap (fun _ h => h.1.1) (nfs2_ro_runsTo_trap himg hro0 hkf hRW_stk hsp_al hs)

theorem extract_32_ro_runsToE_trap {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hpc : s0.pc = img.base + 0x1ad38#64)
    (hrun : s0.status = .Running)
    (hro0 : img.RoDataLoaded s0.mem)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx2 : x.salt.isSome → s0.readReg64 .x2 = 32#64)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = 32#64)
    (hikm_len : x.ikm.length = 32)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA 32)
    (hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976)
    (hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm)
    (hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0)
    (hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 544#64) 976)
    (hsalt_none : x.salt = none → x.saltA = 0#64)
    (hsalt_some : ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      DisjointRegions x.saltA 32 (sp0 - 544#64) 976) :
    Extract.RunsToE (trTrapProgAt img.base C abs) s0 (Extract.EPost C.F x s0 sp0) := by
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s0.mem.RW sp0 432 := Extract.rw_stk_sub hRW_stk sp0 432 hsub_432
  have hsub_544 : 0 < 544 ∧ ((sp0 - 544#64) - (sp0 - 544#64)).toNat + 544 ≤ 976 := by
    have heq : (sp0 - 544#64) - (sp0 - 544#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hd_salt_544 : DisjointRegions (Extract.saltPtrOf sp0 x) 32 (sp0 - 544#64) 544 := by
    cases hsalt : x.salt with
    | none =>
      rw [Extract.saltPtrOf, hsalt]
      exact (Extract.disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)).symm
    | some sv =>
      rw [Extract.saltPtrOf, hsalt]
      exact Extract.disj_stk_sub_right (hsalt_some sv hsalt).2.2 (sp0 - 544#64) 544 hsub_544
  have h0 := Extract.RunsTo.toE
    (Extract.seg0_runsTo (img := img) (ext := trTrapExterns C abs)
      hpc hrun hsp0 hx1 hx2 hx3 hx4 hsp_al hrw_sp0 (fun h => Or.inl (hsalt_none h)) hsalt_some)
  have h1 := Extract.RunsToE.trans_full h0 fun s hs hkf _ =>
    nfs1_ro_runsTo_trap himg hro0 hkf hRW_stk hd_salt_544 hsp_al hsalt_none hs
  have h2 := h1.trans fun s hs =>
    Extract.RunsTo.toE (Extract.seg1a_runsTo hRW_stk hsp_al hs)
  have h3 := h2.trans fun s hs =>
    Extract.RunsTo.toE
      (Extract.seg1b_runsTo hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs)
  have h4 := h3.trans fun s hs =>
    Extract.RunsTo.toE (Extract.seg1c_runsTo hRW_stk hsp_al hs)
  have h5 := h4.trans fun s hs =>
    Extract.RunsTo.toE
      (Extract.fin_runsTo (fun hpre => FinalizeFixedProof.finalize_fixed_runsTo_ext hpre)
        hRW_stk hikm_len hsp_al hs)
  have h6 := h5.trans fun s hs =>
    Extract.RunsTo.toE (Extract.seg2_runsTo hsp_al hs)
  have h7 := Extract.RunsToE.trans_full h6 fun s hs hkf _ =>
    nfs2_ro_runsTo_trap himg hro0 hkf hRW_stk hsp_al hs
  exact h7.trans fun s hs =>
    Extract.RunsTo.toE (Extract.seg3_runsTo hsp0 hRW_out hRW_stk hd_out_stk hsp_al hs)

/-- Pure `RunsToE` contract for `extract` (`0x1ad38`) when `x.ikm.length = 32`, requiring only
`img.RoDataLoaded s0.mem`. -/
theorem extract_32_ro_runsToE {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hpc : s0.pc = img.base + 0x1ad38#64)
    (hrun : s0.status = .Running)
    (hro0 : img.RoDataLoaded s0.mem)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx2 : x.salt.isSome → s0.readReg64 .x2 = 32#64)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = 32#64)
    (hikm_len : x.ikm.length = 32)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA 32)
    (hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976)
    (hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm)
    (hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0)
    (hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 544#64) 976)
    (hsalt_none : x.salt = none → x.saltA = 0#64)
    (hsalt_some : ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      DisjointRegions x.saltA 32 (sp0 - 544#64) 976) :
    Extract.RunsToE (tripleRatchetProgAt img.base C ctl abs) s0 (Extract.EPost C.F x s0 sp0) := runsToE_kit_of_trap (fun _ h => h.2.1) (extract_32_ro_runsToE_trap himg hpc hrun hro0 hsp0 hx1 hx2 hx3 hx4 hikm_len hsp_al hRW_out hRW_stk hRW_ikm hd_out_stk hikm_mem0 hd_ikm_out hd_ikm_stk hsalt_none hsalt_some)

def ENfs1Long (b : BitVec 64) (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) :
    Prop :=
  Extract.ExtCommon s0 sp0 s ∧
  s.pc = b + 0x2b494#64 ∧
  s.readReg64 .lr = b + 0x1ad88#64 ∧
  s.readReg64 .x0 = sp0 + 176#64 ∧
  s.readReg64 .x1 = Extract.saltPtrOf sp0 x ∧
  s.readReg64 .x2 = 32#64 ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = BitVec.ofNat 64 x.ikm.length ∧
  s.mem.readBytes (Extract.saltPtrOf sp0 x) 32 = effectiveSalt x.salt

def ERet1Long (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  Extract.ExtCommon s0 sp0 s ∧
  s.pc = b + 0x1ad88#64 ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = BitVec.ofNat 64 x.ikm.length ∧
  s.mem.read64 (sp0 + 176#64) = 0#64 ∧
  HmacSt s.mem (sp0 + 184#64) F (effectiveSalt x.salt) []

def ECompLong (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  Extract.ExtCommon s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "sha2::sha256::compress256") ∧
  s.readReg64 .lr = b + 0x1ae6c#64 ∧
  s.readReg64 .x0 = sp0 + 0x40#64 ∧
  s.readReg64 .x1 = x.ikmA ∧
  s.readReg64 .x2 = BitVec.ofNat 64 (x.ikm.length / 64) ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = BitVec.ofNat 64 (x.ikm.length % 64) ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.readReg64 .x24 = BitVec.ofNat 64 (64 * (x.ikm.length / 64)) ∧
  s.mem.readBytes (sp0 + 0x40#64) 32 = shaStateBytes (hmacInnerInit F (effectiveSalt x.salt)) ∧
  s.mem.read64 (sp0 + 0x60#64) = BitVec.ofNat 64 (1 + x.ikm.length / 64) ∧
  s.mem.readBytes (sp0 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F (effectiveSalt x.salt)) ∧
  s.mem.read64 (sp0 + 0x88#64) = 1#64

def EMemcpyLong (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  Extract.ExtCommon s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "memcpy") ∧
  s.readReg64 .lr = b + 0x1ae80#64 ∧
  s.readReg64 .x0 = sp0 ∧
  s.readReg64 .x1 = x.ikmA + BitVec.ofNat 64 (64 * (x.ikm.length / 64)) ∧
  s.readReg64 .x2 = BitVec.ofNat 64 (x.ikm.length % 64) ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.mem.read8 (sp0 + 0x3f#64) = BitVec.ofNat 8 (x.ikm.length % 64) ∧
  s.mem.readBytes (sp0 + 0x40#64) 32 =
    shaStateBytes ((chunks64 (x.ikm.take (64 * (x.ikm.length / 64)))).foldl F
      (hmacInnerInit F (effectiveSalt x.salt))) ∧
  s.mem.read64 (sp0 + 0x60#64) = BitVec.ofNat 64 (1 + x.ikm.length / 64) ∧
  s.mem.readBytes (sp0 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F (effectiveSalt x.salt)) ∧
  s.mem.read64 (sp0 + 0x88#64) = 1#64

def EC88Long (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  Extract.ExtCommon s0 sp0 s ∧
  s.pc = b + 0x1ae80#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  HmacStGen s.mem sp0 F (effectiveSalt x.salt)
    (x.ikm.take (64 * (x.ikm.length / 64))) (x.ikm.drop (64 * (x.ikm.length / 64)))

def EFinLong (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  Extract.ExtCommon s0 sp0 s ∧
  s.pc = b + 0x30764#64 ∧
  s.readReg64 .lr = b + 0x1aeb4#64 ∧
  s.readReg64 .x0 = sp0 + 144#64 ∧
  s.readReg64 .x1 = sp0 + 176#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  HmacStGen s.mem (sp0 + 176#64) F (effectiveSalt x.salt)
    (x.ikm.take (64 * (x.ikm.length / 64))) (x.ikm.drop (64 * (x.ikm.length / 64)))

set_option maxHeartbeats 3200000 in
theorem seg0_long_runsTo_trap {img : Obj.Image} {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hpc : s0.pc = img.base + 0x1ad38#64)
    (hstat : s0.status = .Running)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 x.ikm.length)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hrw_sp0 : s0.mem.RW sp0 432)
    (hsalt : x.salt = none)
    (hsaltA : x.saltA = 0#64) :
    RunsTo (trTrapProgAt img.base C abs) s0 (ENfs1Long img.base x s0 sp0) := by
  iterate 20 s2_step
  refine RunsTo.refl ?_
  have hsaved : Extract.ExtSaved s0 sp0
      (((((((((((((((s0.mem.write64 (sp0 + 336#64) (s0.readReg64 .x29)).write64
        (sp0 + 344#64) (s0.readReg64 .lr)).write64
        (sp0 + 352#64) (s0.readReg64 .x28)).write64
        (sp0 + 368#64) (s0.readReg64 .x26)).write64
        (sp0 + 376#64) (s0.readReg64 .x25)).write64
        (sp0 + 384#64) (s0.readReg64 .x24)).write64
        (sp0 + 392#64) (s0.readReg64 .x23)).write64
        (sp0 + 400#64) (s0.readReg64 .x22)).write64
        (sp0 + 408#64) (s0.readReg64 .x21)).write64
        (sp0 + 416#64) (s0.readReg64 .x20)).write64
        (sp0 + 424#64) (s0.readReg64 .x19)).write64
        (sp0 + 144#64) 0#64).write64
        (sp0 + 152#64) 0#64).write64
        (sp0 + 160#64) 0#64).write64
        (sp0 + 168#64) 0#64) :=
    { h29 := by simp (config := { decide := true }) only [arm64_norm]
      hlr := by simp (config := { decide := true }) only [arm64_norm]
      h28 := by simp (config := { decide := true }) only [arm64_norm]
      h26 := by simp (config := { decide := true }) only [arm64_norm]
      h25 := by simp (config := { decide := true }) only [arm64_norm]
      h24 := by simp (config := { decide := true }) only [arm64_norm]
      h23 := by simp (config := { decide := true }) only [arm64_norm]
      h22 := by simp (config := { decide := true }) only [arm64_norm]
      h21 := by simp (config := { decide := true }) only [arm64_norm]
      h20 := by simp (config := { decide := true }) only [arm64_norm]
      h19 := by simp (config := { decide := true }) only [arm64_norm] }
  have hag : AgreesOutside s0.mem
      (((((((((((((((s0.mem.write64 (sp0 + 336#64) (s0.readReg64 .x29)).write64
        (sp0 + 344#64) (s0.readReg64 .lr)).write64
        (sp0 + 352#64) (s0.readReg64 .x28)).write64
        (sp0 + 368#64) (s0.readReg64 .x26)).write64
        (sp0 + 376#64) (s0.readReg64 .x25)).write64
        (sp0 + 384#64) (s0.readReg64 .x24)).write64
        (sp0 + 392#64) (s0.readReg64 .x23)).write64
        (sp0 + 400#64) (s0.readReg64 .x22)).write64
        (sp0 + 408#64) (s0.readReg64 .x21)).write64
        (sp0 + 416#64) (s0.readReg64 .x20)).write64
        (sp0 + 424#64) (s0.readReg64 .x19)).write64
        (sp0 + 144#64) 0#64).write64
        (sp0 + 152#64) 0#64).write64
        (sp0 + 160#64) 0#64).write64
        (sp0 + 168#64) 0#64) sp0 432 := by
    repeat' (first
      | with_reducible exact AgreesOutside.rfl' _ _ _
      | with_reducible refine Extract.agreesOutside_sp0_write64 ?_ (by decide))
  have hframe : Extract.ExtFrame s0 sp0 _ :=
    Extract.ExtFrame.of_agreesOutside_sp0 (n := 432) (Extract.S2Frame.refl _ _) (by decide) hag
  unfold ENfs1Long
  refine ⟨⟨hstat, rfl, rfl, rfl, rfl, hsaved, hframe⟩,
    rfl, rfl, rfl, ?_, ?_, rfl, rfl, ?_⟩
  · simp [Extract.saltPtrOf, hsalt, hx1, hsaltA]
  · simp [hx1, hsaltA]
  · rw [Extract.saltPtrOf, effectiveSalt, hsalt]
    dsimp only [Option.map, Option.getD, State.setMem]
    refine Extract.readBytes_32_zero_of_read64_zero ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, arm64_norm]

theorem seg0_long_runsTo {img : Obj.Image} {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hpc : s0.pc = img.base + 0x1ad38#64)
    (hstat : s0.status = .Running)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 x.ikm.length)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hrw_sp0 : s0.mem.RW sp0 432)
    (hsalt : x.salt = none)
    (hsaltA : x.saltA = 0#64) :
    RunsTo (tripleRatchetProgAt img.base C ctl abs) s0 (ENfs1Long img.base x s0 sp0) := runsTo_kit_of_trap (fun _ h => h.1.1) (seg0_long_runsTo_trap hpc hstat hsp0 hx1 hx3 hx4 hsp_al hrw_sp0 hsalt hsaltA)

theorem nfs1_long_ro_runsTo_trap {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hro0 : img.RoDataLoaded s0.mem)
    (hkf : s0.mem.KeepsFrozen s.mem)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hd_salt_544 : DisjointRegions (Extract.saltPtrOf sp0 x) 32 (sp0 - 544#64) 544)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ENfs1Long img.base x s0 sp0 s) :
    Extract.RunsToE (trTrapProgAt img.base C abs) s
      (ERet1Long img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx20, hx21, hsalt_mem⟩
  have hsub_x0 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x98 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_544 : 0 < 544 ∧ ((sp0 - 544#64) - (sp0 - 544#64)).toNat + 544 ≤ 976 := by
    have heq : (sp0 - 544#64) - (sp0 - 544#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 544#64)).toNat + 96 ≤ 976 := by
    have heq : (sp0 + 336#64) - (sp0 - 544#64) = 880#64 := by bv_lin
    rw [heq]; decide
  have hrun := nfs32_ro_runsTo_trap (C := C) (abs := abs) himg
    (roDataLoaded_of_keepsFrozen hro0 hkf)
    hpc hstat hx0 hx1 hx2 hsalt_mem
    (hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_x0.2))
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_544.2))
    (by rw [hsp]; exact (Extract.disj_sp0_sub_off sp0 544#64 544 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact hd_salt_544)
    (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8] at hhm
  have hsaved' : Extract.ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Extract.disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact Extract.disj_sp0_sub_off sp0 544#64 544 336#64 96 (by decide)
  have hframe' : Extract.ExtFrame s0 sp0 s'.mem :=
    hframe.trans_pair hfr' hsub_x0.2 hsub_544.2
  exact ⟨⟨hstat', (Extract.CallingConventionPreserved.sp_eq hcs).trans hsp,
    (Extract.CallingConventionPreserved.x19 hcs).trans hx19,
    (Extract.CallingConventionPreserved.x27 hcs).trans hx27,
    (Extract.CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr, (Extract.CallingConventionPreserved.x20 hcs).trans hx20,
    (Extract.CallingConventionPreserved.x21 hcs).trans hx21, hok, hhm⟩

theorem nfs1_long_ro_runsTo {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hro0 : img.RoDataLoaded s0.mem)
    (hkf : s0.mem.KeepsFrozen s.mem)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hd_salt_544 : DisjointRegions (Extract.saltPtrOf sp0 x) 32 (sp0 - 544#64) 544)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ENfs1Long img.base x s0 sp0 s) :
    Extract.RunsToE (tripleRatchetProgAt img.base C ctl abs) s
      (ERet1Long img.base C.F x s0 sp0) := runsToE_kit_of_trap (fun _ h => h.1.1) (nfs1_long_ro_runsTo_trap himg hro0 hkf hRW_stk hd_salt_544 hsp_al hs)

theorem seg1a_long_runsTo_trap {img : Obj.Image} {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERet1Long img.base C.F x s0 sp0 s) :
    RunsTo (trTrapProgAt img.base C abs) s (ECompLong img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx20, hx21, hok, hhm⟩
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (Extract.rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hpos : s.mem.read8 (sp0 + 247#64) = 0#8 := by
    have heq : sp0 + 247#64 = (sp0 + 184#64) + 0x3f#64 := by bv_lin
    rw [heq]
    exact hhm.2.2.1
  have hcnt1 : s.mem.read64 (sp0 + 280#64) = 1#64 := by
    have heq : sp0 + 280#64 = (sp0 + 184#64) + 0x60#64 := by bv_lin
    rw [heq]
    exact hhm.2.2.2.2.1
  have hcnt2 : s.mem.read64 (sp0 + 320#64) = 1#64 := by
    have heq : sp0 + 320#64 = (sp0 + 184#64) + 0x88#64 := by bv_lin
    rw [heq]
    exact hhm.2.2.2.2.2.2
  rcases hikm_len with hlen | hlen | hlen <;> {
    rw [hlen] at hx21
    iterate 35 s2_step
    refine RunsTo.refl ?_
    unfold ECompLong
    rw [hlen]
    refine ⟨⟨hstat, hsp, hx19, hx27, hx29, ?_⟩,
      by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
      by fin_reg, by fin_reg, by fin_reg, by fin_reg, ?_, ?_, ?_, ?_⟩
    · dsimp only [State.setMem]
      refine Extract.ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe ?_
      repeat' (first
        | with_reducible exact AgreesOutside.rfl' _ _ _
        | with_reducible refine Extract.agreesOutside_sp0_write64 ?_ (by decide)
        | with_reducible refine Extract.agreesOutside_sp0_write64_zero ?_ (by decide))
    · dsimp only [State.setMem]
      rw [← hhm.2.2.2.1]
      refine readBytes_32_eq_of_read64_eq ?_ ?_ ?_ ?_ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, arm64_norm]
    · dsimp only [State.setMem]
      simp (config := { decide := true }) only [arm64_norm, hcnt1]
    · dsimp only [State.setMem]
      rw [← hhm.2.2.2.2.2.1]
      refine readBytes_32_eq_of_read64_eq ?_ ?_ ?_ ?_ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, arm64_norm]
    · dsimp only [State.setMem]
      simp (config := { decide := true }) only [arm64_norm, hcnt2]
  }

theorem seg1a_long_runsTo {img : Obj.Image} {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERet1Long img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAt img.base C ctl abs) s (ECompLong img.base C.F x s0 sp0) := runsTo_kit_of_trap (fun _ h => h.1.1) (seg1a_long_runsTo_trap hRW_stk hikm_len hsp_al hs)

theorem agreesOutside_writeBytes_sub_sp0 {m : Memory} {sp0 a : BitVec 64} {bs : List (BitVec 8)}
    (ha : (a - sp0).toNat + bs.length ≤ 328) :
    AgreesOutside m (m.writeBytes a bs) sp0 328 := by
  have h := ProofLib.AgreesOutside.writeBytes_self m a bs
  have hout : ∀ x, OutsideRegion sp0 328 x → OutsideRegion a bs.length x := by
    intro x hx; simp only [OutsideRegion] at hx ⊢; bv_omega
  exact ⟨fun x hx => h.1 x (hout x hx), h.2.1, fun x hx => h.2.2.1 x (hout x hx), h.2.2.2⟩

theorem HmacStGen.of_comp_write8 {m : Memory} {sp0 : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key blocks : List (BitVec 8)} {nrem : ℕ}
    (hcnt1 : m.read64 (sp0 + 0x60#64) = BitVec.ofNat 64 (1 + blocks.length / 64))
    (hout : m.readBytes (sp0 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key))
    (hcnt2 : m.read64 (sp0 + 0x88#64) = 1#64) :
    let ist' := shaStateBytes ((chunks64 blocks).foldl F (hmacInnerInit F key))
    let m₁ := m.writeBytes (sp0 + 0x40#64) ist'
    let m₂ := m₁.write8 (sp0 + 63#64) (BitVec.ofNat 8 nrem)
    m₂.read8 (sp0 + 0x3f#64) = BitVec.ofNat 8 nrem ∧
    m₂.readBytes (sp0 + 0x40#64) 32 = ist' ∧
    m₂.read64 (sp0 + 0x60#64) = BitVec.ofNat 64 (1 + blocks.length / 64) ∧
    m₂.readBytes (sp0 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key) ∧
    m₂.read64 (sp0 + 0x88#64) = 1#64 := by
  intro ist' m₁ m₂
  have hist_len : ist'.length = 32 := shaStateBytes_length _
  have hag1 : AgreesOutside m m₁ (sp0 + 0x40#64) 32 := by
    have h := ProofLib.AgreesOutside.writeBytes_self m (sp0 + 0x40#64) ist'
    rwa [hist_len] at h
  have hag2 : AgreesOutside m₁ m₂ (sp0 + 63#64) 1 :=
    (AgreesOutside.rfl' m₁ (sp0 + 63#64) 1).write8 (by simp only [InRegion]; bv_omega)
  have hf64_12 : Frame m₁ m₂ [(sp0, 64)] :=
    (Frame.refl m₁ [(sp0, 64)]).trans_agreesOutside_sub (rbase := sp0) (rlen := 64)
      (by simp) (by bv_omega) hag2
  have hf96_02 : Frame m m₂ [(sp0, 96)] :=
    ((Frame.refl m [(sp0, 96)]).trans_agreesOutside_sub (rbase := sp0) (rlen := 96)
      (by simp) (by bv_omega) hag1).trans
      (hf64_12.mono fun a ha r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := ha (sp0, 96) (by simp)
        unfold OutsideRegion at this ⊢; bv_omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Memory.read8_write8_same m₁ (sp0 + 63#64) (BitVec.ofNat 8 nrem)
  · rw [hf64_12.readBytes_eq ?_ (by decide)]
    · have h := Bytes.readBytes_writeBytes_same m (sp0 + 0x40#64) ist' (by rw [hist_len]; decide)
      rwa [hist_len] at h
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Extract.disj_sp0_zero_off sp0 64 0x40#64 32 (by decide)
  · rw [hf96_02.read64_eq ?_, hcnt1]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Extract.disj_sp0_zero_off sp0 96 0x60#64 8 (by decide)
  · rw [hf96_02.readBytes_eq ?_ (by decide), hout]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Extract.disj_sp0_zero_off sp0 96 0x68#64 32 (by decide)
  · rw [hf96_02.read64_eq ?_, hcnt2]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Extract.disj_sp0_zero_off sp0 96 0x88#64 8 (by decide)

theorem HmacStGen.of_memcpy_rem {m : Memory} {sp0 : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key blocks rem : List (BitVec 8)}
    (hmod : blocks.length % 64 = 0)
    (hblk_le : blocks.length ≤ 192)
    (hrem_lt : rem.length < 56)
    (hpos : m.read8 (sp0 + 0x3f#64) = BitVec.ofNat 8 rem.length)
    (hist : m.readBytes (sp0 + 0x40#64) 32 =
      shaStateBytes ((chunks64 blocks).foldl F (hmacInnerInit F key)))
    (hcnt1 : m.read64 (sp0 + 0x60#64) = BitVec.ofNat 64 (1 + blocks.length / 64))
    (hout : m.readBytes (sp0 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key))
    (hcnt2 : m.read64 (sp0 + 0x88#64) = 1#64) :
    HmacStGen (m.writeBytes sp0 rem) sp0 F key blocks rem := by
  let m' := m.writeBytes sp0 rem
  have hag : AgreesOutside m m' sp0 rem.length :=
    ProofLib.AgreesOutside.writeBytes_self m sp0 rem
  have hf63 : Frame m m' [(sp0, 63)] :=
    (Frame.refl m [(sp0, 63)]).trans_agreesOutside_sub (rbase := sp0) (rlen := 63)
      (by simp) (by bv_omega) hag
  refine ⟨hmod, hblk_le, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Bytes.readBytes_writeBytes_same m sp0 rem (by omega)
  · have hout_rem : OutsideRegion sp0 rem.length (sp0 + 0x3f#64) := by
      simp only [OutsideRegion]; bv_omega
    rw [hag.1 (sp0 + 0x3f#64) hout_rem, hpos]
  · rw [hf63.readBytes_eq ?_ (by decide), hist]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Extract.disj_sp0_zero_off sp0 63 0x40#64 32 (by decide)
  · rw [hf63.read64_eq ?_, hcnt1]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Extract.disj_sp0_zero_off sp0 63 0x60#64 8 (by decide)
  · rw [hf63.readBytes_eq ?_ (by decide), hout]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Extract.disj_sp0_zero_off sp0 63 0x68#64 32 (by decide)
  · rw [hf63.read64_eq ?_, hcnt2]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Extract.disj_sp0_zero_off sp0 63 0x88#64 8 (by decide)

theorem seg1b1_long_runsTo_trap {img : Obj.Image} {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ECompLong img.base C.F x s0 sp0 s) :
    RunsTo (trTrapProgAt img.base C abs) s (EMemcpyLong img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx20, hx21, hx22, hx24, hist, hcnt1, hout, hcnt2⟩
  have hikm_le : x.ikm.length ≤ 2 ^ 64 := by
    rcases hikm_len with h | h | h <;> (rw [h]; decide)
  have hikm_s : s.mem.readBytes x.ikmA x.ikm.length = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ hikm_le]
    · exact hikm_mem0
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hd_ikm_out.symm
      · exact hd_ikm_stk.symm
  have hblk_len : (x.ikm.take (64 * (x.ikm.length / 64))).length = 64 * (x.ikm.length / 64) := by
    simp; omega
  have hblk_s : s.mem.readBytes x.ikmA (64 * (x.ikm.length / 64)) =
      x.ikm.take (64 * (x.ikm.length / 64)) := by
    have h := Bytes.readBytes_slice_of_readBytes_eq s.mem x.ikmA x.ikm hikm_s 0
      (64 * (x.ikm.length / 64)) (by omega)
    simpa using h
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (Extract.rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_40 : s.mem.RW (sp0 + 0x40#64) 32 :=
    hrw_sp0_s.sub (by bv_omega)
  have hx2_nat : (s.readReg64 .x2).toNat = x.ikm.length / 64 := by
    rcases hikm_len with h | h | h <;> (rw [hx2, h]; rfl)
  refine s2_compress256_multi_step_trap img.base C abs
    hstat hpc hx0 hx1 hx2_nat hlr hist hblk_s hrw_sp0_40 ?_
  generalize hist_def : shaStateBytes
    ((chunks64 (x.ikm.take (64 * (x.ikm.length / 64)))).foldl C.F
      (hmacInnerInit C.F (effectiveSalt x.salt))) = ist'
  have hist'_len : ist'.length = 32 := by rw [← hist_def]; exact shaStateBytes_length _
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (sp0 + 0x40#64) ist') sp0 328 :=
    agreesOutside_writeBytes_sub_sp0 (by rw [hist'_len]; bv_omega)
  have hrw_sp0_1 : (s.mem.writeBytes (sp0 + 0x40#64) ist').RW sp0 432 :=
    rw_of_perm_eq hag_comp.2 hrw_sp0_s
  iterate 5 s2_step
  refine RunsTo.refl ?_
  have hnrem_8 : BitVec.truncate 8 (BitVec.ofNat 64 (x.ikm.length % 64)) =
      BitVec.ofNat 8 (x.ikm.length % 64) := by
    rcases hikm_len with hlen | hlen | hlen <;> (rw [hlen]; rfl)
  have hag_w8 : AgreesOutside s.mem
      ((s.mem.writeBytes (sp0 + 0x40#64) ist').write8 (sp0 + 63#64)
        (BitVec.ofNat 8 (x.ikm.length % 64))) sp0 328 :=
    Extract.agreesOutside_sp0_write8 hag_comp (by decide)
  have hcnt1' : s.mem.read64 (sp0 + 0x60#64) =
      BitVec.ofNat 64 (1 + (x.ikm.take (64 * (x.ikm.length / 64))).length / 64) := by
    rw [hblk_len, Nat.mul_div_cancel_left _ (by decide)]
    exact hcnt1
  have hm := HmacStGen.of_comp_write8 (nrem := x.ikm.length % 64) hcnt1' hout hcnt2
  rw [hblk_len, Nat.mul_div_cancel_left _ (by decide), hist_def] at hm
  unfold EMemcpyLong Extract.ExtCommon
  simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
    State.readReg64_advancePC, State.readReg64_writeReg64,
    Reg.lr, Reg.x0, Reg.x1, Reg.x2, Reg.x19, Reg.x27, Reg.x29, Reg.x22, ite_true, ite_false]
  dsimp only [State.setMem, State.setPC, State.advancePC, State.writeReg64]
  rw [hnrem_8]
  exact ⟨⟨hstat, hsp, hx19, hx27, hx29,
    Extract.ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe hag_w8⟩,
    rfl, trivial, trivial, trivial, trivial, hx22, hm.1, hm.2.1.trans hist_def.symm,
    hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2⟩

theorem seg1b1_long_runsTo {img : Obj.Image} {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ECompLong img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAt img.base C ctl abs) s (EMemcpyLong img.base C.F x s0 sp0) := runsTo_kit_of_trap (fun _ h => h.1.1) (seg1b1_long_runsTo_trap hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs)

theorem seg1b2_long_runsTo_trap {img : Obj.Image} {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hs : EMemcpyLong img.base C.F x s0 sp0 s) :
    RunsTo (trTrapProgAt img.base C abs) s (EC88Long img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx22, hpos, hist, hcnt1, hout, hcnt2⟩
  have hikm_le : x.ikm.length ≤ 2 ^ 64 := by
    rcases hikm_len with h | h | h <;> (rw [h]; decide)
  have hikm_s : s.mem.readBytes x.ikmA x.ikm.length = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ hikm_le]
    · exact hikm_mem0
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hd_ikm_out.symm
      · exact hd_ikm_stk.symm
  have hblk_len : (x.ikm.take (64 * (x.ikm.length / 64))).length = 64 * (x.ikm.length / 64) := by
    simp; omega
  have hrem_len : (x.ikm.drop (64 * (x.ikm.length / 64))).length = x.ikm.length % 64 := by
    simp; omega
  have hrem_s : s.mem.readBytes
      (x.ikmA + BitVec.ofNat 64 (64 * (x.ikm.length / 64))) (x.ikm.length % 64) =
      x.ikm.drop (64 * (x.ikm.length / 64)) := by
    have h := Bytes.readBytes_slice_of_readBytes_eq s.mem x.ikmA x.ikm hikm_s
      (64 * (x.ikm.length / 64)) (x.ikm.length % 64) (by omega)
    have htake : (x.ikm.drop (64 * (x.ikm.length / 64))).take (x.ikm.length % 64) =
        x.ikm.drop (64 * (x.ikm.length / 64)) :=
      List.take_of_length_le (by simp; omega)
    exact h.trans htake
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (Extract.rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_nrem : s.mem.RW sp0 (x.ikm.length % 64) :=
    hrw_sp0_s.sub (by bv_omega)
  have hx2_nat : (s.readReg64 .x2).toNat = x.ikm.length % 64 := by
    rcases hikm_len with h | h | h <;> (rw [hx2, h]; rfl)
  refine s2_memcpy_step_trap img.base C abs
    hstat hpc hx0 hx1 hx2_nat hlr hrem_s hrw_sp0_nrem ?_
  refine RunsTo.refl ?_
  have hag_mc : AgreesOutside s.mem
      (s.mem.writeBytes sp0 (x.ikm.drop (64 * (x.ikm.length / 64)))) sp0 328 :=
    agreesOutside_writeBytes_sub_sp0 (by rw [BitVec.sub_self, hrem_len]; bv_omega)
  unfold EC88Long Extract.ExtCommon
  simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
    Reg.x19, Reg.x27, Reg.x29, Reg.x22, ite_false]
  dsimp only [State.setMem, State.setPC]
  refine ⟨⟨hstat, hsp, hx19, hx27, hx29,
    Extract.ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe hag_mc⟩,
    rfl, hx22, ?_⟩
  have hcnt1' : s.mem.read64 (sp0 + 0x60#64) =
      BitVec.ofNat 64 (1 + (x.ikm.take (64 * (x.ikm.length / 64))).length / 64) := by
    rw [hblk_len, Nat.mul_div_cancel_left _ (by decide)]
    exact hcnt1
  have hpos' : s.mem.read8 (sp0 + 0x3f#64) =
      BitVec.ofNat 8 (x.ikm.drop (64 * (x.ikm.length / 64))).length := by
    rw [hrem_len]; exact hpos
  exact HmacStGen.of_memcpy_rem (by rw [hblk_len]; omega) (by rw [hblk_len]; omega)
    (by rw [hrem_len]; omega) hpos' hist hcnt1' hout hcnt2

theorem seg1b2_long_runsTo {img : Obj.Image} {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hs : EMemcpyLong img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAt img.base C ctl abs) s (EC88Long img.base C.F x s0 sp0) := runsTo_kit_of_trap (fun _ h => h.1.1) (seg1b2_long_runsTo_trap hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hs)

theorem seg1c_long_runsTo_trap {img : Obj.Image} {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EC88Long img.base C.F x s0 sp0 s) :
    RunsTo (trTrapProgAt img.base C abs) s (EFinLong img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx22, hhm⟩
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (Extract.rw_stk_sub hRW_stk sp0 432 hsub_432)
  iterate 13 s2_step
  refine RunsTo.refl ?_
  unfold EFinLong
  refine ⟨⟨hstat, hsp, hx19, hx27, hx29, ?_⟩,
    rfl, rfl, rfl, rfl, hx22, ?_⟩
  · dsimp only [State.setMem]
    refine Extract.ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe ?_
    repeat' (first
      | with_reducible exact AgreesOutside.rfl' _ _ _
      | with_reducible refine Extract.agreesOutside_sp0_write64 ?_ (by decide))
  · refine HmacStGen.of_copy_19 hhm
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm]

theorem seg1c_long_runsTo {img : Obj.Image} {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EC88Long img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAt img.base C ctl abs) s (EFinLong img.base C.F x s0 sp0) := runsTo_kit_of_trap (fun _ h => h.1.1) (seg1c_long_runsTo_trap hRW_stk hsp_al hs)

theorem fin_long_runsTo_trap {img : Obj.Image} {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EFinLong img.base C.F x s0 sp0 s) :
    RunsTo (trTrapProgAt img.base C abs) s (Extract.ERetFin img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx22, hhm⟩
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hsub_176 : 0 < 0x90 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x90 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_m144 : 0 < 144 ∧ ((sp0 - 144#64) - (sp0 - 544#64)).toNat + 144 ≤ 976 := by
    have heq : (sp0 - 144#64) - (sp0 - 544#64) = 400#64 := by bv_lin
    rw [heq]; decide
  have hpre : FinGenPre img.base C.F (effectiveSalt x.salt)
      (x.ikm.take (64 * (x.ikm.length / 64))) (x.ikm.drop (64 * (x.ikm.length / 64))) s :=
    { pc_eq := hpc
      status := hstat
      key_le := by rw [Extract.effectiveSalt_length]; decide
      rem_lt := by simp; omega
      hmac_st := by rw [hx1]; exact hhm
      rw_out := by rw [hx0]; exact hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_144.2)
      rw_hm := by rw [hx1]; exact hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_176.2)
      rw_fsp := by rw [hsp]; exact hframe.rw_of_rw _ _ (Extract.rw_stk_sub hRW_stk _ _ hsub_m144.2)
      disj_out_hm := by
        rw [hx0, hx1]; exact Extract.disj_sp0_off sp0 144#64 32 176#64 0x90 (by decide)
      disj_out_fsp := by
        rw [hx0, hsp]; exact (Extract.disj_sp0_sub_off sp0 144#64 144 144#64 32 (by decide)).symm
      disj_hm_fsp := by
        rw [hx1, hsp]; exact (Extract.disj_sp0_sub_off sp0 144#64 144 176#64 0x90 (by decide)).symm
      sp_aligned := by rw [hsp]; exact Extract.sp0_aligned_0b1111 hsp_al }
  refine (finalize_fixed_gen_runsTo_trap hpre).mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hout, hfr'⟩
  rw [hx0, hx1, hsp] at hfr'
  rw [hx0, List.take_append_drop] at hout
  have hsaved' : Extract.ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_frame hfr' ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Extract.disj_sp0_off sp0 144#64 32 336#64 96 (by decide)
    · exact Extract.disj_sp0_off sp0 176#64 0x90 336#64 96 (by decide)
    · exact Extract.disj_sp0_sub_off sp0 144#64 144 336#64 96 (by decide)
  have hframe' : Extract.ExtFrame s0 sp0 s'.mem :=
    hframe.trans_triple hfr' hsub_144.2 hsub_176.2 hsub_m144.2
  exact ⟨⟨hstat', hcs.sp_eq.trans hsp, (CalleeSaved.x19 hcs).trans hx19,
    (CalleeSaved.x27 hcs).trans hx27,
    (CalleeSaved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr, (CalleeSaved.x22 hcs).trans hx22, hout⟩

theorem fin_long_runsTo {img : Obj.Image} {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EFinLong img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAt img.base C ctl abs) s (Extract.ERetFin img.base C.F x s0 sp0) := runsTo_kit_of_trap (fun _ h => h.1.1) (fin_long_runsTo_trap hRW_stk hikm_len hsp_al hs)

theorem extract_none_long_ro_runsToE_trap {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hpc : s0.pc = img.base + 0x1ad38#64)
    (hrun : s0.status = .Running)
    (hro0 : img.RoDataLoaded s0.mem)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 x.ikm.length)
    (hsalt : x.salt = none)
    (hsaltA : x.saltA = 0#64)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976) :
    Extract.RunsToE (trTrapProgAt img.base C abs) s0 (Extract.EPost C.F x s0 sp0) := by
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s0.mem.RW sp0 432 := Extract.rw_stk_sub hRW_stk sp0 432 hsub_432
  have hd_salt_544 : DisjointRegions (Extract.saltPtrOf sp0 x) 32 (sp0 - 544#64) 544 := by
    rw [Extract.saltPtrOf, hsalt]
    exact (Extract.disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)).symm
  have h0 := Extract.RunsTo.toE (seg0_long_runsTo_trap (img := img) (C := C) (abs := abs)
    hpc hrun hsp0 hx1 hx3 hx4 hsp_al hrw_sp0 hsalt hsaltA)
  have h1 := Extract.RunsToE.trans_full h0 fun s hs hkf _ =>
    nfs1_long_ro_runsTo_trap himg hro0 hkf hRW_stk hd_salt_544 hsp_al hs
  have h2 := h1.trans fun s hs =>
    Extract.RunsTo.toE (seg1a_long_runsTo_trap hRW_stk hikm_len hsp_al hs)
  have h3a := h2.trans fun s hs =>
    Extract.RunsTo.toE
      (seg1b1_long_runsTo_trap hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs)
  have h3 := h3a.trans fun s hs =>
    Extract.RunsTo.toE
      (seg1b2_long_runsTo_trap hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hs)
  have h4 := h3.trans fun s hs =>
    Extract.RunsTo.toE (seg1c_long_runsTo_trap hRW_stk hsp_al hs)
  have h5 := h4.trans fun s hs =>
    Extract.RunsTo.toE (fin_long_runsTo_trap hRW_stk hikm_len hsp_al hs)
  have h6 := h5.trans fun s hs =>
    Extract.RunsTo.toE (Extract.seg2_runsTo hsp_al hs)
  have h7 := Extract.RunsToE.trans_full h6 fun s hs hkf _ =>
    nfs2_ro_runsTo_trap himg hro0 hkf hRW_stk hsp_al hs
  exact h7.trans fun s hs =>
    Extract.RunsTo.toE (Extract.seg3_runsTo hsp0 hRW_out hRW_stk hd_out_stk hsp_al hs)

/-- Pure `RunsToE` contract for `extract` (`0x1ad38`) when `x.salt = none` and
`x.ikm.length ∈ {160, 192, 224}`, requiring only `img.RoDataLoaded s0.mem`. -/
theorem extract_none_long_ro_runsToE {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hpc : s0.pc = img.base + 0x1ad38#64)
    (hrun : s0.status = .Running)
    (hro0 : img.RoDataLoaded s0.mem)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 x.ikm.length)
    (hsalt : x.salt = none)
    (hsaltA : x.saltA = 0#64)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976) :
    Extract.RunsToE (tripleRatchetProgAt img.base C ctl abs) s0 (Extract.EPost C.F x s0 sp0) := runsToE_kit_of_trap (fun _ h => h.2.1) (extract_none_long_ro_runsToE_trap himg hpc hrun hro0 hsp0 hx1 hx3 hx4 hsalt hsaltA hikm_len hsp_al hRW_out hRW_stk hRW_ikm hd_out_stk hikm_mem0 hd_ikm_out hd_ikm_stk)

end CryptoVerification.E2E.Pqxdh.ResponderCore
