/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixed
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.SpqrV1.Chain.Defs -- shake: keep

/-!
# Generalized SPQR KDF Contracts

Read-only / read-write byte-slice permissions (`kdfBytesAt`), RFC 2104 key normalization
(`effectiveHmacKey`), and generalized contracts for `new_from_slice [local#3]` and
`finalize_fixed [local#3]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Kdf

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.CodeLayout

/-- Read-only / read-write byte slice permission at `p`: read-only (`p ↦ᵣ bs`) when `ro = true`,
read-write (`p ↦ₛ bs`) when `ro = false`. -/
def kdfBytesAt (ro : Bool) (p : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if ro then p ↦ᵣ bs else p ↦ₛ bs

@[simp] theorem kdfBytesAt_true (p : BitVec 64) (bs : List (BitVec 8)) :
    kdfBytesAt true p bs = (p ↦ᵣ bs) := rfl

@[simp] theorem kdfBytesAt_false (p : BitVec 64) (bs : List (BitVec 8)) :
    kdfBytesAt false p bs = (p ↦ₛ bs) := rfl

/-- Effective HMAC key after RFC 2104 key normalization: `sha256With F key` (32 bytes) when
`64 < key.length`, and `key` when `key.length ≤ 64`. -/
def effectiveHmacKey (F : ShaState → List (BitVec 8) → ShaState) (key : List (BitVec 8)) :
    List (BitVec 8) :=
  if 64 < key.length then sha256With F key else key

theorem effectiveHmacKey_of_le (F : ShaState → List (BitVec 8) → ShaState)
    {key : List (BitVec 8)} (h : key.length ≤ 64) :
    effectiveHmacKey F key = key := by
  unfold effectiveHmacKey
  have hnot : ¬ (64 < key.length) := by omega
  simp [hnot]

theorem effectiveHmacKey_length_le (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) :
    (effectiveHmacKey F key).length ≤ 64 := by
  unfold effectiveHmacKey
  by_cases h : 64 < key.length
  · simp [h]
  · simp [h]; omega

theorem hmacWith_effectiveHmacKey (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) :
    hmacWith F (effectiveHmacKey F key) msg = hmacWith F key msg := by
  unfold hmacWith effectiveHmacKey
  by_cases h : 64 < key.length
  · simp [h]
  · simp [h]

/-! ## Generalized SPQR-local `new_from_slice [local#3]` (`0x66fa0`) contract -/

/-- Ghost arguments for generalized `new_from_slice [local#3]` (`0x66fa0`): supports read-only or
read-write key slice (`keyRO : Bool`) and arbitrary key length `< 2 ^ 63` (both the `≤ 64` pad-in-place
branch and the `> 64` hash-the-key branch at `0x66fc4`). -/
structure NewFromSliceGenGhost where
  outA : BitVec 64
  keyRO : Bool
  keyA : BitVec 64
  key : List (BitVec 8)

/-- Generalized SL specification of `<hmac::Hmac<sha2::Sha256> as KeyInit>::new_from_slice [local#3]`
(`0x66fa0`) for SPQR V1: allows `kdfBytesAt x.keyRO x.keyA x.key` and `x.key.length < 2 ^ 63`. -/
def newFromSliceGenSpec (F : ShaState → List (BitVec 8) → ShaState) : Spec NewFromSliceGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.keyA ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.key.length ∧
      x.key.length < 2 ^ 63⌝ ∗
      cells x.outA 19 ∗
      kdfBytesAt x.keyRO x.keyA x.key ∗
      stackAt s.sp newFromSliceStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.outA ↦₆₄ 0#64) ∗
      hmacCoreAt F (x.outA + 8#64) (effectiveHmacKey F x.key) [] ∗
      kdfBytesAt x.keyRO x.keyA x.key ∗
      stackAt s0.sp newFromSliceStack

/-- `<hmac::Hmac<sha2::Sha256> as KeyInit>::new_from_slice [local#3]` (`0x66fa0`) meets
`(newFromSliceGenSpec C.F).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
def NewFromSlice3GenOkX (img : Obj.Image) (C : Crypto)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr newFromSlice3Name)
    ((newFromSliceGenSpec C.F).inImage img)

/-- Generalized `RunsTo` contract of `new_from_slice [local#3]` (`0x66fa0`) on
`tripleRatchetProgAtExt b ext` for any key slice of length `< 2 ^ 63`. -/
def Nfs3GenRunsToExt (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (ext : String → Option (State → State)) : Prop :=
  ∀ {s₀ : State},
    s₀.pc = b + 0x61ba8#64 →
    s₀.status = .Running →
    (s₀.readReg64 .x2).toNat < 2 ^ 63 →
    s₀.mem.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = LibsignalHmac.shaStateBytes sha256IV →
    (b &&& 0xfff#64) = 0#64 →
    s₀.mem.Readable (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 →
    DisjointRegions (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 544#64) 544 →
    s₀.mem.RW (s₀.readReg64 .x0) 0x98 →
    s₀.mem.RW (s₀.sp - 544#64) 544 →
    DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544 →
    ((s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544) →
    ((s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.readReg64 .x0) 0x98) →
    (s₀.sp &&& 0b1111#64) = 0#64 →
    RunsTo (tripleRatchetProgAtExt b ext) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧
      s'.status = .Running ∧
      CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F
        (effectiveHmacKey F (s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)) [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)])

/-! ## Generalized SPQR-local `finalize_fixed [local#3]` (`0x6ce50`) contract -/

/-- Bundled entry preconditions of generalized `finalize_fixed [local#3]` (`b + 0x6ce50`) over
`HmacStN` (`pfx.length % 64 = 0`, `tail.length < 64` including both `< 56` one-block and `[56, 64)`
two-block padding paths, and arbitrary `key`). -/
structure FinPre3Gen (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s₀ : State) : Prop where
  pc_eq        : s₀.pc = b + 0x67a58#64
  status       : s₀.status = .Running
  pfx_lt       : pfx.length < 2 ^ 63
  tail_lt      : tail.length < 64
  hmac_st      : HmacStN s₀.mem (s₀.readReg64 .x1) F (effectiveHmacKey F key) pfx tail
  rw_out       : RW s₀.mem (s₀.readReg64 .x0) 32
  rw_hm        : RW s₀.mem (s₀.readReg64 .x1) 0x90
  rw_fsp       : RW s₀.mem (s₀.sp - 144#64) 144
  disj_out_hm  : DisjointRegions (s₀.readReg64 .x0) 32 (s₀.readReg64 .x1) 0x90
  disj_out_fsp : DisjointRegions (s₀.readReg64 .x0) 32 (s₀.sp - 144#64) 144
  disj_hm_fsp  : DisjointRegions (s₀.readReg64 .x1) 0x90 (s₀.sp - 144#64) 144
  sp_aligned   : (s₀.sp &&& 15#64) = 0#64

/-- Generalized `RunsTo` contract of `finalize_fixed [local#3]` (`0x6ce50`) on
`tripleRatchetProgAtExt b ext` over `HmacStN` (`tail.length < 64`, any `key`). -/
def Fin3GenRunsToExt (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (ext : String → Option (State → State)) : Prop :=
  ∀ {key pfx tail : List (BitVec 8)} {s₀ : State},
    FinPre3Gen b F key pfx tail s₀ →
    RunsTo (tripleRatchetProgAtExt b ext) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧
      s'.status = .Running ∧
      CalleeSaved s₀ s' ∧
      s'.mem.readBytes (s₀.readReg64 .x0) 32 = hmacWith F key (pfx ++ tail) ∧
      Frame s₀.mem s'.mem
        [(s₀.readReg64 .x0, 32), (s₀.readReg64 .x1, 0x90), (s₀.sp - 144#64, 144)])

/-! ## Multi-block `compress256` step and bitvector split helpers -/

theorem compress256Hook_multi_eq (F : ShaState → List (BitVec 8) → ShaState) {s : State}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {nBlocks : ℕ} {pfx : List (BitVec 8)}
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : (s.readReg64 .x2).toNat = nBlocks)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr (64 * nBlocks) = pfx) :
    compress256Hook F s =
      (s.setMem (s.mem.writeBytes stPtr (shaStateBytes ((chunks64 pfx).foldl F st)))).setPC lr := by
  dsimp only [compress256Hook, LibsignalAesCbc.returnToLinkRegister]
  have hlr' : (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
      (shaStateBytes ((chunks64 (s.mem.readBytes (s.readReg64 .x1) (64 * (s.readReg64 .x2).toNat))).foldl
        F (LibsignalHmac.readShaState s.mem (s.readReg64 .x0)))))).readReg64 .lr = lr := by
    simpa [arm64_norm] using hlr
  rw [hlr', hx0, hx1, hx2, readShaState_of_shaStateBytes s.mem stPtr st hst, hblk]

theorem s2_compress256_multi_step_ext
    (b_arg : BitVec 64) (C_arg : Crypto) (ext_arg : String → Option (State → State))
    [HkdfHooks C_arg.F ext_arg]
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st st' : ShaState} {nBlocks : ℕ} {pfx : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = b_arg + bv% (ls_off% "sha2::sha256::compress256"))
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : (s.readReg64 .x2).toNat = nBlocks)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr (64 * nBlocks) = pfx)
    (hst' : (chunks64 pfx).foldl C_arg.F st = st')
    (hrw : s.mem.RW stPtr 32)
    (h : RunsToFrom (tripleRatchetProgAtExt b_arg ext_arg) s₀
      ((s.setMem (s.mem.writeBytes stPtr (shaStateBytes st'))).setPC lr) Q) :
    RunsToFrom (tripleRatchetProgAtExt b_arg ext_arg) s₀ s Q := by
  have hcan : s.mem.canWrite stPtr (shaStateBytes st').length = true := by
    rw [shaStateBytes_length]
    exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : (tripleRatchetProgAtExt b_arg ext_arg).externAt? s.pc = some (compress256Hook C_arg.F) := by
    rw [hpc]; exact tripleRatchetProgAtExt_externAt_273212 b_arg (F := C_arg.F) ext_arg
  have hstate : compress256Hook C_arg.F s =
      (s.setMem (s.mem.writeBytes stPtr (shaStateBytes st'))).setPC lr := by
    rw [compress256Hook_multi_eq C_arg.F hx0 hx1 hx2 hlr hst hblk, hst']
  have hkeep : s.mem.KeepsFrozen (compress256Hook C_arg.F s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (compress256Hook C_arg.F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

theorem HmacSt.of_writeBytes_lt63_write8_pos {m : Memory} {a : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key msg : List (BitVec 8)}
    (hhm : HmacSt m a F key []) (hlt : msg.length < 64) :
    HmacSt ((m.writeBytes a msg).write8 (a + 63#64) (BitVec.ofNat 8 msg.length)) a F key msg := by
  let m₁ := m.writeBytes a msg
  let m₂ := m₁.write8 (a + 63#64) (BitVec.ofNat 8 msg.length)
  have hag1 : AgreesOutside m m₁ a 63 :=
    Expand.agreesOutside_writeBytes_le m a msg 63 (by omega)
  have hag2 : AgreesOutside m₁ m₂ (a + 63#64) 1 :=
    (AgreesOutside.rfl' m₁ (a + 63#64) 1).write8 (by simp only [InRegion]; bv_omega)
  have hf64 : Frame m m₂ [(a, 64)] :=
    ((Frame.refl m [(a, 64)]).trans_agreesOutside_sub (rbase := a) (rlen := 64)
      (by simp) (by bv_omega) hag1).trans_agreesOutside_sub (rbase := a) (rlen := 64)
      (by simp) (by bv_omega) hag2
  rcases hhm with ⟨_, _, _, hin, hinB, hout, houtB⟩
  change HmacSt m₂ a F key msg
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hm0 : msg.length = 0
    · have hnil : msg = [] := List.eq_nil_of_length_eq_zero hm0
      subst hnil; rfl
    · have hd : DisjointRegions (a + 63#64) 1 a msg.length := by
        unfold DisjointRegions; bv_omega
      rw [hag2.readBytes_eq hd (by omega)]
      exact Bytes.readBytes_writeBytes_same m a msg (by omega)
  · dsimp [m₂]
    exact Memory.read8_write8_same _ _ _
  · rw [hf64.readBytes_eq ?_ (by decide), hin]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    unfold DisjointRegions; bv_omega
  · rw [hf64.read64_eq ?_, hinB]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    unfold DisjointRegions; bv_omega
  · rw [hf64.readBytes_eq ?_ (by decide), hout]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    unfold DisjointRegions; bv_omega
  · rw [hf64.read64_eq ?_, houtB]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    unfold DisjointRegions; bv_omega

theorem cmp_ge64_lemmas {n : ℕ} (hge : 64 ≤ n) (hlt : n < 2 ^ 63) :
    BitVec.ule 64#64 (BitVec.ofNat 64 n) = true ∧
    BitVec.ult (BitVec.ofNat 64 n) 64#64 = false ∧
    (AddWithCarry64 (BitVec.ofNat 64 n) 18446744073709551551#64 true).2.c = true ∧
    ((BitVec.ofNat 64 n >>> 6) == 0#64) = false := by
  have hbv : 64#64 ≤ BitVec.ofNat 64 n := by
    rw [BitVec.le_def]; simp [Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]; exact hge
  revert hbv
  generalize BitVec.ofNat 64 n = x
  intro hbv
  dsimp only [AddWithCarry64]
  refine ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

theorem ikm_split_lemmas {n : ℕ} (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n >>> 6).toNat = n / 64 ∧
    1#64 + (BitVec.ofNat 64 n >>> 6) = BitVec.ofNat 64 (1 + n / 64) ∧
    BitVec.ofNat 64 n &&& 9223372036854775744#64 = BitVec.ofNat 64 (64 * (n / 64)) ∧
    (BitVec.ofNat 64 n &&& 63#64).toNat = n - 64 * (n / 64) ∧
    BitVec.truncate 8 (BitVec.ofNat 64 n &&& 63#64) = BitVec.ofNat 8 (n - 64 * (n / 64)) := by
  have hn64 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)
  have h1 : (BitVec.ofNat 64 n >>> 6).toNat = n / 64 := by
    rw [BitVec.toNat_ushiftRight, hn64, Nat.shiftRight_eq_div_pow]
  have h2 : 1#64 + (BitVec.ofNat 64 n >>> 6) = BitVec.ofNat 64 (1 + n / 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, h1, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h3 : BitVec.ofNat 64 n &&& 9223372036854775744#64 = BitVec.ofNat 64 (64 * (n / 64)) := by
    have hbv : BitVec.ofNat 64 n < 9223372036854775808#64 := by
      rw [BitVec.lt_def, hn64]; exact hlt
    have hand : BitVec.ofNat 64 n &&& 9223372036854775744#64 =
        64#64 * (BitVec.ofNat 64 n >>> 6) := by
      revert hbv; generalize BitVec.ofNat 64 n = x; intro hbv; bv_bits
    rw [hand]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, h1, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h4 : (BitVec.ofNat 64 n &&& 63#64).toNat = n - 64 * (n / 64) := by
    have hand : BitVec.ofNat 64 n &&& 63#64 = BitVec.ofNat 64 n % 64#64 := by
      generalize BitVec.ofNat 64 n = x; bv_bits
    rw [hand, BitVec.toNat_umod, hn64]
    change n % 64 = n - 64 * (n / 64)
    omega
  have h5 : BitVec.truncate 8 (BitVec.ofNat 64 n &&& 63#64) = BitVec.ofNat 8 (n - 64 * (n / 64)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, h4, BitVec.toNat_ofNat]
  exact ⟨h1, h2, h3, h4, h5⟩

theorem chunks64_single_64 {a : List (BitVec 8)} (ha : a.length = 64) :
    chunks64 a = [a] := by
  unfold chunks64
  rw [ha]
  change [(a.drop 0).take 64] = [a]
  simp [List.take_of_length_le (by omega : a.length ≤ 64)]

theorem HmacStN.mk_block64 {m : Memory} {a : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key blk tail : List (BitVec 8)}
    (hblk : blk.length = 64)
    (htail_lt : tail.length < 64)
    (htail_bytes : m.readBytes a tail.length = tail)
    (hpos : m.read8 (a + 0x3f#64) = BitVec.ofNat 8 tail.length)
    (hin : m.readBytes (a + 0x40#64) 32 = shaStateBytes (F (hmacInnerInit F key) blk))
    (hcnt1 : m.read64 (a + 0x60#64) = 2#64)
    (hout : m.readBytes (a + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key))
    (hcnt2 : m.read64 (a + 0x88#64) = 1#64) :
    HmacStN m a F key blk tail := by
  have hchunks : chunks64 blk = [blk] := chunks64_single_64 hblk
  refine ⟨by omega, htail_lt, htail_bytes, hpos, ?_, ?_, hout, hcnt2⟩
  · simpa [hchunks] using hin
  · have hdiv : 1 + blk.length / 64 = 2 := by omega
    rw [hdiv]; exact hcnt1

end CryptoVerification.SpqrV1.Kdf
