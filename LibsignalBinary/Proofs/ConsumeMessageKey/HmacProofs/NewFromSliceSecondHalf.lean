/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceFirstHalf

/-!
# Second Half and Full Contract of `<Hmac<Sha256> as KeyInit>::new_from_slice`

Executes `new_from_slice` from the first `compress256` call (`0x2b89c`) through the 64-byte opad
XOR loop, second `compress256`, and epilogue (`0x2bc20`), combining with `nfs_first_half` to prove
`new_from_slice_run` and `new_from_slice_placed_run` (Block 114).
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.LibsignalSession.CryptoHmacSha256

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.CBC
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read64_write64_base_off_disjoint
  Memory.read64_write64_base_zero_off
  Memory.read64_write64_base_off_zero
  Memory.read64_write8_base_off_disjoint
  Memory.read64_write8_base_zero_off
  Memory.read64_write8_base_off_zero
  truncate8_zeroExtend_xor_32
  truncate8_zeroExtend_xor_64

@[scoped simp, arm64_norm]
theorem zeroExtend64_truncate32_zeroExtend64_xor_const (a : BitVec 8) (c : BitVec 64) :
    (((a.zeroExtend 64 ^^^ c).truncate 32).zeroExtend 64).truncate 8 = a ^^^ c.truncate 8 := by
  ext i hi; simp [BitVec.getLsbD_xor]

@[scoped simp, arm64_norm]
theorem zeroExtend64_truncate32_zeroExtend64_byte (a : BitVec 8) :
    ((a.zeroExtend 64).truncate 32).zeroExtend 64 = a.zeroExtend 64 := by
  ext i hi; simp

/-! ## 16-Byte Opad XOR Helpers -/

/-- 16-byte in-place XOR with `0x6a#8` at `a`. -/
def xorChunk (m : Memory) (a : BitVec 64) : Memory :=
  (((((((((((((((m.write8 a (m.read8 a ^^^ 0x6a#8)).write8
    (a + 1#64) (m.read8 (a + 1#64) ^^^ 0x6a#8)).write8
    (a + 2#64) (m.read8 (a + 2#64) ^^^ 0x6a#8)).write8
    (a + 3#64) (m.read8 (a + 3#64) ^^^ 0x6a#8)).write8
    (a + 4#64) (m.read8 (a + 4#64) ^^^ 0x6a#8)).write8
    (a + 5#64) (m.read8 (a + 5#64) ^^^ 0x6a#8)).write8
    (a + 6#64) (m.read8 (a + 6#64) ^^^ 0x6a#8)).write8
    (a + 7#64) (m.read8 (a + 7#64) ^^^ 0x6a#8)).write8
    (a + 8#64) (m.read8 (a + 8#64) ^^^ 0x6a#8)).write8
    (a + 9#64) (m.read8 (a + 9#64) ^^^ 0x6a#8)).write8
    (a + 10#64) (m.read8 (a + 10#64) ^^^ 0x6a#8)).write8
    (a + 11#64) (m.read8 (a + 11#64) ^^^ 0x6a#8)).write8
    (a + 12#64) (m.read8 (a + 12#64) ^^^ 0x6a#8)).write8
    (a + 13#64) (m.read8 (a + 13#64) ^^^ 0x6a#8)).write8
    (a + 14#64) (m.read8 (a + 14#64) ^^^ 0x6a#8)).write8
    (a + 15#64) (m.read8 (a + 15#64) ^^^ 0x6a#8)

theorem xorChunk_eq_writeBytes (m : Memory) (a : BitVec 64) :
    xorChunk m a = m.writeBytes a ((m.readBytes a 16).map (· ^^^ 0x6a#8)) := by
  unfold xorChunk
  rw [readBytes_16_eq]
  dsimp only [List.map]
  rw [← write8_16_eq_writeBytes]

@[scoped simp]
theorem xorChunk_perm (m : Memory) (a : BitVec 64) : (xorChunk m a).perm = m.perm := by
  rw [xorChunk_eq_writeBytes]
  exact Memory.perm_writeBytes m a _

theorem rw_xorChunk {m : Memory} {sp : BitVec 64} {n : ℕ} (a : BitVec 64)
    (h : m.RW sp n) : (xorChunk m a).RW sp n := by
  rw [xorChunk_eq_writeBytes]
  have hag := ProofLib.agreesOutside_writeBytes m a ((m.readBytes a 16).map (· ^^^ 0x6a#8))
  exact Memory.RW.of_perm_eq hag.2.1 hag.2.2.2.1 h

theorem xorChunk4_eq_writeBytes (m : Memory) (a : BitVec 64) :
    xorChunk (xorChunk (xorChunk (xorChunk m a) (a + 16#64)) (a + 32#64)) (a + 48#64) =
      m.writeBytes a ((m.readBytes a 64).map (· ^^^ 0x6a#8)) := by
  have h64 : m.readBytes a 64 =
      m.readBytes a 16 ++ m.readBytes (a + 16#64) 16 ++
      m.readBytes (a + 32#64) 16 ++ m.readBytes (a + 48#64) 16 :=
    (LibsignalAesCbc.Run.Bytes.readBytes_add m a 48 16).trans
      (congrArg (· ++ _) ((LibsignalAesCbc.Run.Bytes.readBytes_add m a 32 16).trans
        (congrArg (· ++ _) (LibsignalAesCbc.Run.Bytes.readBytes_add m a 16 16))))
  rw [h64, List.map_append, List.map_append, List.map_append]
  rw [writeBytes_append, writeBytes_append, writeBytes_append]
  simp only [List.length_append, List.length_map, Memory.readBytes_length]
  have h1 : (xorChunk m a).readBytes (a + 16#64) 16 = m.readBytes (a + 16#64) 16 := by
    rw [xorChunk_eq_writeBytes]
    exact Layout.readBytes_writeBytes_of_disjoint m a _ (a + 16#64) 16
      (by clear * -; simp only [List.length_map, Memory.readBytes_length, DisjointRegions]; bv_omega) (by decide)
  have h2 : (xorChunk (xorChunk m a) (a + 16#64)).readBytes (a + 32#64) 16 =
      m.readBytes (a + 32#64) 16 := by
    rw [xorChunk_eq_writeBytes, Layout.readBytes_writeBytes_of_disjoint _ (a + 16#64) _ (a + 32#64) 16
      (by clear * -; simp only [List.length_map, Memory.readBytes_length, DisjointRegions]; bv_omega) (by decide)]
    rw [xorChunk_eq_writeBytes, Layout.readBytes_writeBytes_of_disjoint _ a _ (a + 32#64) 16
      (by clear * -; simp only [List.length_map, Memory.readBytes_length, DisjointRegions]; bv_omega) (by decide)]
  have h3 : (xorChunk (xorChunk (xorChunk m a) (a + 16#64)) (a + 32#64)).readBytes (a + 48#64) 16 =
      m.readBytes (a + 48#64) 16 := by
    rw [xorChunk_eq_writeBytes, Layout.readBytes_writeBytes_of_disjoint _ (a + 32#64) _ (a + 48#64) 16
      (by clear * -; simp only [List.length_map, Memory.readBytes_length, DisjointRegions]; bv_omega) (by decide)]
    rw [xorChunk_eq_writeBytes, Layout.readBytes_writeBytes_of_disjoint _ (a + 16#64) _ (a + 48#64) 16
      (by clear * -; simp only [List.length_map, Memory.readBytes_length, DisjointRegions]; bv_omega) (by decide)]
    rw [xorChunk_eq_writeBytes, Layout.readBytes_writeBytes_of_disjoint _ a _ (a + 48#64) 16
      (by clear * -; simp only [List.length_map, Memory.readBytes_length, DisjointRegions]; bv_omega) (by decide)]
  rw [xorChunk_eq_writeBytes _ (a + 48#64), h3,
    xorChunk_eq_writeBytes _ (a + 32#64), h2,
    xorChunk_eq_writeBytes _ (a + 16#64), h1,
    xorChunk_eq_writeBytes m a]

theorem map_xor_0x36_0x6a (l : List (BitVec 8)) :
    (l.map (· ^^^ 0x36#8)).map (· ^^^ 0x6a#8) = l.map (· ^^^ 0x5c#8) := by
  simp [List.map_map, Function.comp_def, xor_0x36_0x6a_byte]

theorem write128_pair_ivsw (m m_init : Memory) (sp : BitVec 64)
    (hiv : m_init.readBytes sp 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    (m.write128 (sp + 176#64) (m_init.read128 (sp + 16#64))).write128
      (sp + 192#64) (m_init.read128 sp) =
    m.writeBytes (sp + 176#64) (shaStateBytes sha256IV) := by
  rw [write128_eq_writeBytes, write128_eq_writeBytes, blockToBytes_read128, blockToBytes_read128]
  have hadd : sp + 192#64 =
      (sp + 176#64) + BitVec.ofNat 64 (m_init.readBytes (sp + 16#64) 16).length := by
    rw [Memory.readBytes_length]; clear * -; bv_omega
  rw [hadd, ← writeBytes_append]
  have h32 : m_init.readBytes sp 32 =
      m_init.readBytes sp 16 ++ m_init.readBytes (sp + 16#64) 16 :=
    LibsignalAesCbc.Run.Bytes.readBytes_add m_init sp 16 16
  have hhi : m_init.readBytes sp 16 = (shaStateBytes sha256IV).drop 16 := by
    have h := congrArg (List.take 16) (h32.symm.trans hiv)
    rwa [List.take_left' (Memory.readBytes_length m_init sp 16),
      List.take_left' (by simp [shaStateBytes_length])] at h
  have hlo : m_init.readBytes (sp + 16#64) 16 = (shaStateBytes sha256IV).take 16 := by
    have h := congrArg (List.drop 16) (h32.symm.trans hiv)
    rwa [List.drop_left' (Memory.readBytes_length m_init sp 16),
      List.drop_left' (by simp [shaStateBytes_length])] at h
  rw [hlo, hhi, List.take_append_drop]

/-! ## First `compress256` and Opad Loop (`0x2b89c → 0x2bbbc`) -/

structure NfsOpadPostHook (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (s₀ : State) (key : List (BitVec 8)) (s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1264)
  status  : s.status = .Running
  regInv  : NfsRegInv b s₀ s
  memInv  : NfsMemInv b s₀ s.mem
  ist_eq  : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes (innerState F key)
  blk_eq  : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8)
  ivsw_eq : s.mem.readBytes (nfsSp s₀) 32 =
    (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16

theorem nfs_compress1_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hpc : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1260))
    (hstat : s.status = .Running)
    (hR : NfsRegInv b s₀ s)
    (hM : NfsMemInv b s₀ s.mem)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hist : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8))
    (hivsw : s.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsTo (P b F alloc) s (NfsOpadPostHook b F s₀ key) := by
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  sess_step
  have hrw_ist : s.mem.RW (nfsSp s₀ + 400#64) 32 :=
    hM.rw_stack.sub (by clear * -; bv_omega)
  refine RunsTo.sess_compress256_step
    (hrun := hstat)
    (hpc := rfl)
    (hx0 := hx0)
    (hx1 := hx1)
    (hx2 := hx2)
    (hlr := rfl)
    (hmem := rfl)
    (hst := hist)
    (hblk := hblk)
    (hrw := hrw_ist)
    ?_
  refine RunsTo.refl ?_
  refine {
    pc_eq := rfl
    status := hstat
    regInv := ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩
    memInv := hM.writeBytes_low 400#64 _ (by simp [shaStateBytes_length])
    ist_eq := Layout.readBytes_writeBytes_eq s.mem (nfsSp s₀ + 400#64) _ 32 (shaStateBytes_length _) (by decide)
    blk_eq := (Layout.readBytes_writeBytes_of_disjoint s.mem (nfsSp s₀ + 400#64) _
      (nfsSp s₀ + 288#64) 64
      (by clear * -; simp only [shaStateBytes_length, DisjointRegions]; bv_omega) (by decide)).trans hblk
    ivsw_eq := (Layout.readBytes_writeBytes_of_disjoint s.mem (nfsSp s₀ + 400#64) _
      (nfsSp s₀) 32
      (by clear * -; simp only [shaStateBytes_length, DisjointRegions]; bv_omega) (by decide)).trans hivsw
  }

structure NfsOpadMidState (pcOff nextOff0 nextOff1 : BitVec 64)
    (b : BitVec 64) (s₀ : State) (m_init m_cur : Memory) (s : State) : Prop where
  pc_eq  : s.pc = b + pcOff
  status : s.status = .Running
  regInv : NfsRegInv b s₀ s
  x0_eq  : s.readReg64 .x0 = nfsSp s₀ + 176#64
  x1_eq  : s.readReg64 .x1 = nfsSp s₀ + 288#64
  x8_eq  : s.readReg64 .x8 = 0x6a#64
  x10_eq : s.readReg64 .x10 = (s.mem.read8 (nfsSp s₀ + nextOff0)).zeroExtend 64
  x11_eq : s.readReg64 .x11 = (s.mem.read8 (nfsSp s₀ + nextOff1)).zeroExtend 64
  q0_eq  : s.readVReg128 0#5 = m_init.read128 (nfsSp s₀)
  q1_eq  : s.readVReg128 1#5 = m_init.read128 (nfsSp s₀ + 16#64)
  mem_eq : s.mem = m_cur

theorem nfs_opad_chunk0 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hs : NfsOpadPostHook b F s₀ key s) :
    RunsTo (P b F alloc) s
      (NfsOpadMidState (bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1480)) 304#64 305#64 b s₀ s.mem (xorChunk s.mem (nfsSp s₀ + 288#64))) := by
  generalize hPost : (NfsOpadMidState _ _ _ _ _ _ _) = Post
  have hpc := hs.pc_eq
  have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hrw : s.mem.RW (nfsSp s₀) 544 := hs.memInv.rw_stack
  iterate 54 sess_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, Memory.read128, BitVec.add_assoc],
    by simp (config := { decide := true }) only [arm64_norm, Memory.read128, BitVec.add_assoc],
    by simp only [xorChunk, BitVec.add_assoc, arm64_norm]⟩

theorem nfs_opad_chunk1 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    {s₀ s : State} {m_init m_cur : Memory}
    (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : NfsOpadMidState (bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1480)) 304#64 305#64 b s₀ m_init m_cur s) :
    RunsTo (P b F alloc) s
      (NfsOpadMidState (bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1672)) 320#64 321#64 b s₀ m_init (xorChunk s.mem (nfsSp s₀ + 304#64))) := by
  generalize hPost : (NfsOpadMidState _ _ _ _ _ _ _) = Post
  have hpc := hs.pc_eq
  have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hx0 := hs.x0_eq
  have hx1 := hs.x1_eq
  have hx8 := hs.x8_eq
  have hx10 := hs.x10_eq
  have hx11 := hs.x11_eq
  have hq0 := hs.q0_eq
  have hq1 := hs.q1_eq
  have hrw : s.mem.RW (nfsSp s₀) 544 := hs.mem_eq ▸ hrw_cur
  iterate 48 sess_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    by simp only [arm64_norm, hx0], by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx8],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hq0],
    by simp (config := { decide := true }) only [arm64_norm, hq1],
    by simp only [xorChunk, BitVec.add_assoc, arm64_norm]⟩

theorem nfs_opad_chunk2 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    {s₀ s : State} {m_init m_cur : Memory}
    (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : NfsOpadMidState (bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1672)) 320#64 321#64 b s₀ m_init m_cur s) :
    RunsTo (P b F alloc) s
      (NfsOpadMidState (bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1864)) 336#64 337#64 b s₀ m_init (xorChunk s.mem (nfsSp s₀ + 320#64))) := by
  generalize hPost : (NfsOpadMidState _ _ _ _ _ _ _) = Post
  have hpc := hs.pc_eq
  have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hx0 := hs.x0_eq
  have hx1 := hs.x1_eq
  have hx8 := hs.x8_eq
  have hx10 := hs.x10_eq
  have hx11 := hs.x11_eq
  have hq0 := hs.q0_eq
  have hq1 := hs.q1_eq
  have hrw : s.mem.RW (nfsSp s₀) 544 := hs.mem_eq ▸ hrw_cur
  iterate 48 sess_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    by simp only [arm64_norm, hx0], by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx8],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hq0],
    by simp (config := { decide := true }) only [arm64_norm, hq1],
    by simp only [xorChunk, BitVec.add_assoc, arm64_norm]⟩

structure NfsOpadEndState (b : BitVec 64) (s₀ : State) (m_init m3 : Memory) (s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 2060)
  status : s.status = .Running
  regInv : NfsRegInv b s₀ s
  x0_eq  : s.readReg64 .x0 = nfsSp s₀ + 176#64
  x1_eq  : s.readReg64 .x1 = nfsSp s₀ + 288#64
  x2_eq  : s.readReg64 .x2 = 1#64
  mem_eq : s.mem = ((m3.write128 (nfsSp s₀ + 176#64) (m_init.read128 (nfsSp s₀ + 16#64))).write128
    (nfsSp s₀ + 192#64) (m_init.read128 (nfsSp s₀))).write64 (nfsSp s₀ + 208#64) 1#64

theorem nfs_opad_chunk3 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    {s₀ s : State} {m_init m_cur : Memory}
    (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : NfsOpadMidState (bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1864)) 336#64 337#64 b s₀ m_init m_cur s) :
    RunsTo (P b F alloc) s
      (NfsOpadEndState b s₀ m_init (xorChunk s.mem (nfsSp s₀ + 336#64))) := by
  generalize hPost : (NfsOpadEndState _ _ _ _) = Post
  have hpc := hs.pc_eq
  have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hx0 := hs.x0_eq
  have hx1 := hs.x1_eq
  have hx8 := hs.x8_eq
  have hx10 := hs.x10_eq
  have hx11 := hs.x11_eq
  have hq0 := hs.q0_eq
  have hq1 := hs.q1_eq
  have hrw : s.mem.RW (nfsSp s₀) 544 := hs.mem_eq ▸ hrw_cur
  iterate 49 sess_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    by simp only [arm64_norm, hx0], by simp only [arm64_norm, hx1], by simp only [arm64_norm],
    by simp only [xorChunk, Memory.write128, Memory.read128, BitVec.add_assoc, arm64_norm]⟩

structure NfsPreCompress2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (s₀ : State) (key : List (BitVec 8)) (s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 2060)
  status : s.status = .Running
  regInv : NfsRegInv b s₀ s
  memInv : NfsMemInv b s₀ s.mem
  x0_eq  : s.readReg64 .x0 = nfsSp s₀ + 176#64
  x1_eq  : s.readReg64 .x1 = nfsSp s₀ + 288#64
  x2_eq  : s.readReg64 .x2 = 1#64
  ist_eq : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes (innerState F key)
  blk_eq : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x5c#8)
  ost_eq : s.mem.readBytes (nfsSp s₀ + 176#64) 32 = shaStateBytes sha256IV
  obl_eq : s.mem.read64 (nfsSp s₀ + 208#64) = 1#64

theorem nfs_opad_loop {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hpc : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1260))
    (hstat : s.status = .Running)
    (hR : NfsRegInv b s₀ s)
    (hM : NfsMemInv b s₀ s.mem)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hist : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8))
    (hivsw : s.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsTo (P b F alloc) s (NfsPreCompress2 b F s₀ key) := by
  have hopad_len : ((keyBlock key).map (· ^^^ 0x5c#8)).length = 64 := by
    simp [keyBlock_length hlen]
  have hiv_len : (shaStateBytes sha256IV).length = 32 := shaStateBytes_length sha256IV
  refine (nfs_compress1_runsTo hpc hstat hR hM hx0 hx1 hx2 hist hblk hivsw).trans fun s1 h1 => ?_
  refine (nfs_opad_chunk0 h1).trans fun s2 h2 => ?_
  have hrw1 : (xorChunk s1.mem (nfsSp s₀ + 288#64)).RW (nfsSp s₀) 544 :=
    rw_xorChunk _ h1.memInv.rw_stack
  refine (nfs_opad_chunk1 hrw1 h2).trans fun s3 h3 => ?_
  have hrw2 : (xorChunk s2.mem (nfsSp s₀ + 304#64)).RW (nfsSp s₀) 544 :=
    rw_xorChunk _ (h2.mem_eq ▸ hrw1)
  refine (nfs_opad_chunk2 hrw2 h3).trans fun s4 h4 => ?_
  have hrw3 : (xorChunk s3.mem (nfsSp s₀ + 320#64)).RW (nfsSp s₀) 544 :=
    rw_xorChunk _ (h3.mem_eq ▸ hrw2)
  refine (nfs_opad_chunk3 hrw3 h4).mono fun s5 h5 => ?_
  have hm4 : xorChunk s4.mem (nfsSp s₀ + 336#64) =
      s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8)) := by
    rw [h4.mem_eq, h3.mem_eq, h2.mem_eq]
    have ha1 : nfsSp s₀ + 304#64 = (nfsSp s₀ + 288#64) + 16#64 := by clear * -; bv_omega
    have ha2 : nfsSp s₀ + 320#64 = (nfsSp s₀ + 288#64) + 32#64 := by clear * -; bv_omega
    have ha3 : nfsSp s₀ + 336#64 = (nfsSp s₀ + 288#64) + 48#64 := by clear * -; bv_omega
    rw [ha1, ha2, ha3, xorChunk4_eq_writeBytes, h1.blk_eq, map_xor_0x36_0x6a]
  have hmem5 : s5.mem =
      (((s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8))).writeBytes
        (nfsSp s₀ + 176#64) (shaStateBytes sha256IV)).write64 (nfsSp s₀ + 208#64) 1#64) := by
    rw [h5.mem_eq, hm4, write128_pair_ivsw _ s1.mem (nfsSp s₀) h1.ivsw_eq]
  have hM5 : NfsMemInv b s₀ s5.mem := by
    rw [hmem5]
    exact ((h1.memInv.writeBytes_low 288#64 _ (by rw [hopad_len]; decide)).writeBytes_low
      176#64 _ (by rw [hiv_len]; decide)).write64_low 208#64 1#64 (by decide)
  have hA_opad := AgreesOutside.writeBytes_self s1.mem (nfsSp s₀ + 288#64)
    ((keyBlock key).map (· ^^^ 0x5c#8))
  have hA_iv := AgreesOutside.writeBytes_self
    (s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8)))
    (nfsSp s₀ + 176#64) (shaStateBytes sha256IV)
  have hA_208 := AgreesOutside.write64_self
    ((s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8))).writeBytes
      (nfsSp s₀ + 176#64) (shaStateBytes sha256IV))
    (nfsSp s₀ + 208#64) 1#64
  refine {
    pc_eq := h5.pc_eq
    status := h5.status
    regInv := h5.regInv
    memInv := hM5
    x0_eq := h5.x0_eq
    x1_eq := h5.x1_eq
    x2_eq := h5.x2_eq
    ist_eq := by
      rw [hmem5,
          (agreesOutside_toFrame hA_208).readBytes_eq
            (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
          (agreesOutside_toFrame hA_iv).readBytes_eq
            (by rw [hiv_len]; clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
          (agreesOutside_toFrame hA_opad).readBytes_eq
            (by rw [hopad_len]; clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
          h1.ist_eq]
    blk_eq := by
      rw [hmem5,
          (agreesOutside_toFrame hA_208).readBytes_eq
            (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
          (agreesOutside_toFrame hA_iv).readBytes_eq
            (by rw [hiv_len]; clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide)]
      exact Layout.readBytes_writeBytes_eq s1.mem (nfsSp s₀ + 288#64) _ 64 hopad_len (by decide)
    ost_eq := by
      rw [hmem5,
          (agreesOutside_toFrame hA_208).readBytes_eq
            (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide)]
      exact Layout.readBytes_writeBytes_eq _ (nfsSp s₀ + 176#64) _ 32 hiv_len (by decide)
    obl_eq := by
      rw [hmem5, Memory.read64_write64_same]
  }

/-! ## Second `compress256` and Epilogue (`0x2bbbc → lr`) -/

structure NfsPostCompress2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (s₀ : State) (key : List (BitVec 8)) (s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 2064)
  status : s.status = .Running
  regInv : NfsRegInv b s₀ s
  memInv : NfsMemInv b s₀ s.mem
  ist_eq : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes (innerState F key)
  ost_eq : s.mem.readBytes (nfsSp s₀ + 176#64) 32 = shaStateBytes (outerState F key)
  obl_eq : s.mem.read64 (nfsSp s₀ + 208#64) = 1#64

theorem nfs_compress2_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hs : NfsPreCompress2 b F s₀ key s) :
    RunsTo (P b F alloc) s (NfsPostCompress2 b F s₀ key) := by
  have hpc := hs.pc_eq
  have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hM := hs.memInv
  sess_step
  have hrw_ost : s.mem.RW (nfsSp s₀ + 176#64) 32 :=
    hM.rw_stack.sub (by clear * -; bv_omega)
  refine RunsTo.sess_compress256_step
    (hrun := hstat)
    (hpc := rfl)
    (hx0 := hs.x0_eq)
    (hx1 := hs.x1_eq)
    (hx2 := hs.x2_eq)
    (hlr := rfl)
    (hmem := rfl)
    (hst := hs.ost_eq)
    (hblk := hs.blk_eq)
    (hrw := hrw_ost)
    ?_
  refine RunsTo.refl ?_
  have hA := AgreesOutside.writeBytes_self s.mem (nfsSp s₀ + 176#64)
    (shaStateBytes (F sha256IV ((keyBlock key).map (· ^^^ 0x5c#8))))
  refine {
    pc_eq := rfl
    status := hstat
    regInv := ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩
    memInv := hM.writeBytes_low 176#64 _ (by simp [shaStateBytes_length])
    ist_eq := (Layout.readBytes_writeBytes_of_disjoint s.mem (nfsSp s₀ + 176#64) _
      (nfsSp s₀ + 400#64) 32
      (by clear * -; simp only [shaStateBytes_length, DisjointRegions]; bv_omega) (by decide)).trans hs.ist_eq
    ost_eq := Layout.readBytes_writeBytes_eq s.mem (nfsSp s₀ + 176#64) _ 32 (shaStateBytes_length _) (by decide)
    obl_eq := ((agreesOutside_toFrame hA).read64_eq
      (by clear * -; simp only [shaStateBytes_length, List.mem_singleton, forall_eq, DisjointRegions]; bv_omega)).trans hs.obl_eq
  }

theorem readBytes_32_eq_of_read64_eq (m₁ m₂ : Memory) (a b : BitVec 64)
    (h0 : m₁.read64 a = m₂.read64 b)
    (h8 : m₁.read64 (a + 8#64) = m₂.read64 (b + 8#64))
    (h16 : m₁.read64 (a + 16#64) = m₂.read64 (b + 16#64))
    (h24 : m₁.read64 (a + 24#64) = m₂.read64 (b + 24#64)) :
    m₁.readBytes a 32 = m₂.readBytes b 32 := by
  have ha24 : (a + 16#64) + 8#64 = a + 24#64 := by clear * -; bv_omega
  have hb24 : (b + 16#64) + 8#64 = b + 24#64 := by clear * -; bv_omega
  rw [LibsignalAesCbc.Run.Bytes.readBytes_add m₁ a 16 16, LibsignalAesCbc.Run.Bytes.readBytes_add m₁ a 8 8, LibsignalAesCbc.Run.Bytes.readBytes_add m₁ (a + 16#64) 8 8, ha24,
      LibsignalAesCbc.Run.Bytes.readBytes_add m₂ b 16 16, LibsignalAesCbc.Run.Bytes.readBytes_add m₂ b 8 8, LibsignalAesCbc.Run.Bytes.readBytes_add m₂ (b + 16#64) 8 8, hb24,
      ← toLEBytes_8_read64_eq m₁ a, ← toLEBytes_8_read64_eq m₁ (a + 8#64),
      ← toLEBytes_8_read64_eq m₁ (a + 16#64), ← toLEBytes_8_read64_eq m₁ (a + 24#64),
      ← toLEBytes_8_read64_eq m₂ b, ← toLEBytes_8_read64_eq m₂ (b + 8#64),
      ← toLEBytes_8_read64_eq m₂ (b + 16#64), ← toLEBytes_8_read64_eq m₂ (b + 24#64),
      h0, h8, h16, h24]

theorem read64_sp_write8_out {out sp : BitVec 64}
    (hdisj : DisjointRegions out 0x98 sp 544)
    (m : Memory) (j k : BitVec 64) (v : BitVec 8)
    (hd : decide (j.toNat + 1 ≤ 152 ∧ k.toNat + 8 ≤ 544) = true) :
    (m.write8 (out + j) v).read64 (sp + k) = m.read64 (sp + k) := by
  have hd' : j.toNat + 1 ≤ 152 ∧ k.toNat + 8 ≤ 544 := of_decide_eq_true hd
  rcases hd' with ⟨h1, h2⟩
  refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write8_self m (out + j) v)) ?_
  clear * - hdisj h1 h2
  simp only [List.mem_singleton, forall_eq, DisjointRegions] at hdisj ⊢
  bv_omega

theorem read64_sp_write64_out {out sp : BitVec 64}
    (hdisj : DisjointRegions out 0x98 sp 544)
    (m : Memory) (j k v : BitVec 64)
    (hd : decide (j.toNat + 8 ≤ 152 ∧ k.toNat + 8 ≤ 544) = true) :
    (m.write64 (out + j) v).read64 (sp + k) = m.read64 (sp + k) := by
  have hd' : j.toNat + 8 ≤ 152 ∧ k.toNat + 8 ≤ 544 := of_decide_eq_true hd
  rcases hd' with ⟨h1, h2⟩
  refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write64_self m (out + j) v)) ?_
  clear * - hdisj h1 h2
  simp only [List.mem_singleton, forall_eq, DisjointRegions] at hdisj ⊢
  bv_omega

theorem read64_sp_write64_out_zero {out sp : BitVec 64}
    (hdisj : DisjointRegions out 0x98 sp 544)
    (m : Memory) (k v : BitVec 64)
    (hd : decide (k.toNat + 8 ≤ 544) = true) :
    (m.write64 out v).read64 (sp + k) = m.read64 (sp + k) := by
  have hd' : k.toNat + 8 ≤ 544 := of_decide_eq_true hd
  refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write64_self m out v)) ?_
  clear * - hdisj hd'
  simp only [List.mem_singleton, forall_eq, DisjointRegions] at hdisj ⊢
  bv_omega

theorem read64_out_write64_sp {out sp : BitVec 64}
    (hdisj : DisjointRegions out 0x98 sp 544)
    (m : Memory) (k j v : BitVec 64)
    (hd : decide (k.toNat + 8 ≤ 544 ∧ j.toNat + 8 ≤ 152) = true) :
    (m.write64 (sp + k) v).read64 (out + j) = m.read64 (out + j) := by
  have hd' : k.toNat + 8 ≤ 544 ∧ j.toNat + 8 ≤ 152 := of_decide_eq_true hd
  rcases hd' with ⟨h1, h2⟩
  refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write64_self m (sp + k) v)) ?_
  clear * - hdisj h1 h2
  simp only [List.mem_singleton, forall_eq, DisjointRegions] at hdisj ⊢
  bv_omega

theorem read64_out_zero_write64_sp {out sp : BitVec 64}
    (hdisj : DisjointRegions out 0x98 sp 544)
    (m : Memory) (k v : BitVec 64)
    (hd : decide (k.toNat + 8 ≤ 544) = true) :
    (m.write64 (sp + k) v).read64 out = m.read64 out := by
  have hd' : k.toNat + 8 ≤ 544 := of_decide_eq_true hd
  refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write64_self m (sp + k) v)) ?_
  clear * - hdisj hd'
  simp only [List.mem_singleton, forall_eq, DisjointRegions] at hdisj ⊢
  bv_omega

theorem read8_out_write64_sp {out sp : BitVec 64}
    (hdisj : DisjointRegions out 0x98 sp 544)
    (m : Memory) (k j v : BitVec 64)
    (hd : decide (k.toNat + 8 ≤ 544 ∧ j.toNat + 1 ≤ 152) = true) :
    (m.write64 (sp + k) v).read8 (out + j) = m.read8 (out + j) := by
  have hd' : k.toNat + 8 ≤ 544 ∧ j.toNat + 1 ≤ 152 := of_decide_eq_true hd
  rcases hd' with ⟨h1, h2⟩
  refine Frame.read8_eq (agreesOutside_toFrame (AgreesOutside.write64_self m (sp + k) v)) ?_
  clear * - hdisj h1 h2
  simp only [List.mem_singleton, forall_eq, DisjointRegions, OutsideRegion] at hdisj ⊢
  bv_omega

theorem Frame.write64_stack {out sp : BitVec 64} {m₀ m : Memory}
    (hf : Frame m₀ m [(out, 0x98), (sp, 544)])
    (off v : BitVec 64) (hoff : off.toNat + 8 ≤ 544 := by decide) :
    Frame m₀ (m.write64 (sp + off) v) [(out, 0x98), (sp, 544)] :=
  Frame.of_agreesOutside_stack hf (AgreesOutside.write64_self m (sp + off) v) hoff

theorem Frame.write8_out {out sp : BitVec 64} {m₀ m : Memory}
    (hf : Frame m₀ m [(out, 0x98), (sp, 544)])
    (off : BitVec 64) (v : BitVec 8) (hoff : off.toNat + 1 ≤ 0x98 := by decide) :
    Frame m₀ (m.write8 (out + off) v) [(out, 0x98), (sp, 544)] :=
  Frame.of_agreesOutside_out hf (AgreesOutside.write8_self m (out + off) v) hoff

theorem Frame.write64_out {out sp : BitVec 64} {m₀ m : Memory}
    (hf : Frame m₀ m [(out, 0x98), (sp, 544)])
    (off v : BitVec 64) (hoff : off.toNat + 8 ≤ 0x98 := by decide) :
    Frame m₀ (m.write64 (out + off) v) [(out, 0x98), (sp, 544)] :=
  Frame.of_agreesOutside_out hf (AgreesOutside.write64_self m (out + off) v) hoff

theorem Frame.write64_out_zero {out sp : BitVec 64} {m₀ m : Memory}
    (hf : Frame m₀ m [(out, 0x98), (sp, 544)]) (v : BitVec 64) :
    Frame m₀ (m.write64 out v) [(out, 0x98), (sp, 544)] := by
  have hA : AgreesOutside m (m.write64 (out + 0#64) v) (out + 0#64) 8 :=
    AgreesOutside.write64_self m (out + 0#64) v
  simpa only [BitVec.add_zero] using Frame.of_agreesOutside_out hf hA (by decide)

theorem nfs_epilogue {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hs : NfsPostCompress2 b F s₀ key s) :
    RunsTo (P b F alloc) s (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧
      s'.status = .Running ∧
      CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  generalize hPost : (fun s' : State => _) = Post
  have hpc := hs.pc_eq
  have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hM := hs.memInv
  have hm_ost := hs.ost_eq
  have hm_ist := hs.ist_eq
  have hm_208 := hs.obl_eq
  have hm_432 := hM.saved.m432
  have hm_464 := hM.saved.m464
  have hm_472 := hM.saved.m472
  have hm_480 := hM.saved.m480
  have hm_496 := hM.saved.m496
  have hm_504 := hM.saved.m504
  have hm_512 := hM.saved.m512
  have hm_520 := hM.saved.m520
  have hm_528 := hM.saved.m528
  have hm_536 := hM.saved.m536
  have hrw_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  have hrw_out : s.mem.RW (s₀.readReg64 .x0) 0x98 := hM.rw_out
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hcross1 := read64_sp_write8_out hM.disj_out_stack
  have hcross2 := read64_sp_write64_out hM.disj_out_stack
  have hcross3 := read64_sp_write64_out_zero hM.disj_out_stack
  have hcross4 := read64_out_write64_sp hM.disj_out_stack
  have hcross5 := read64_out_zero_write64_sp hM.disj_out_stack
  have hcross6 := read8_out_write64_sp hM.disj_out_stack
  iterate 25 sess_step
  subst hPost
  refine RunsTo.refl ?_
  have hsp_restore : nfsSp s₀ + 544#64 = s₀.sp := (nfs_sp_eq_add s₀).symm
  have hpos_addr : (s₀.readReg64 .x0 + 8#64) + 0x3f#64 = s₀.readReg64 .x0 + 71#64 := by clear * -; bv_omega
  have hist_addr : (s₀.readReg64 .x0 + 8#64) + 0x40#64 = s₀.readReg64 .x0 + 72#64 := by clear * -; bv_omega
  have hibl_addr : (s₀.readReg64 .x0 + 8#64) + 0x60#64 = s₀.readReg64 .x0 + 104#64 := by clear * -; bv_omega
  have host_addr : (s₀.readReg64 .x0 + 8#64) + 0x68#64 = s₀.readReg64 .x0 + 112#64 := by clear * -; bv_omega
  have hobl_addr : (s₀.readReg64 .x0 + 8#64) + 0x88#64 = s₀.readReg64 .x0 + 144#64 := by clear * -; bv_omega
  refine ⟨by simp only [arm64_norm], by simp only [arm64_norm, hstat], ?_, ?_, ?_, ?_⟩
  · refine ⟨by simp only [arm64_norm, hsp_restore], ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := { decide := true }) only [arm64_norm, hx25, hx26, hx27]
  · simp (config := { decide := true }) only [arm64_norm, *]
  · refine ⟨by decide, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpos_addr]
      simp (config := { decide := true }) only [arm64_norm, *]
    · rw [hist_addr, ← hm_ist]
      refine readBytes_32_eq_of_read64_eq _ s.mem (s₀.readReg64 .x0 + 72#64) (nfsSp s₀ + 400#64)
        ?_ ?_ ?_ ?_ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, *]
    · rw [hibl_addr]
      simp (config := { decide := true }) only [arm64_norm, *]
    · rw [host_addr, ← hm_ost]
      refine readBytes_32_eq_of_read64_eq _ s.mem (s₀.readReg64 .x0 + 112#64) (nfsSp s₀ + 176#64)
        ?_ ?_ ?_ ?_ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, *]
    · rw [hobl_addr]
      simp (config := { decide := true }) only [arm64_norm, *]
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC, State.setPC]
    refine Frame.write64_out ?_ 80#64 _
    refine Frame.write64_out ?_ 72#64 _
    refine Frame.write64_out ?_ 144#64 _
    refine Frame.write64_out ?_ 136#64 _
    refine Frame.write64_stack ?_ 56#64 _
    refine Frame.write64_stack ?_ 48#64 _
    refine Frame.write64_stack ?_ 40#64 _
    refine Frame.write64_stack ?_ 32#64 _
    refine Frame.write64_out ?_ 96#64 _
    refine Frame.write64_out ?_ 88#64 _
    refine Frame.write64_out ?_ 128#64 _
    refine Frame.write64_out ?_ 120#64 _
    refine Frame.write64_out ?_ 112#64 _
    refine Frame.write64_out ?_ 104#64 _
    refine Frame.write64_out_zero ?_ 0#64
    refine Frame.write64_stack ?_ 104#64 _
    refine Frame.write64_stack ?_ 96#64 _
    refine Frame.write64_stack ?_ 88#64 _
    refine Frame.write64_stack ?_ 80#64 _
    refine Frame.write64_stack ?_ 72#64 _
    refine Frame.write64_stack ?_ 64#64 _
    refine Frame.write8_out ?_ 71#64 _
    exact hM.frame

/-- Second half of `new_from_slice` (`0x2b89c → s₀.readReg64 .lr`). -/
theorem nfs_second_half {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hpc : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1260))
    (hstat : s.status = .Running)
    (hR : NfsRegInv b s₀ s)
    (hM : NfsMemInv b s₀ s.mem)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hist : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8))
    (hivsw : s.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsTo (P b F alloc) s (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧
      s'.status = .Running ∧
      CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  refine (nfs_opad_loop hlen hpc hstat hR hM hx0 hx1 hx2 hist hblk hivsw).trans fun s1 h1 => ?_
  refine (nfs_compress2_runsTo h1).trans fun s2 h2 => ?_
  exact nfs_epilogue hal h2

/-- Full `RunsTo` contract for `<Hmac<Sha256> as KeyInit>::new_from_slice` (`0x2b3b0`). -/
theorem new_from_slice_run {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ : State}
    (hpc : s₀.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]"))
    (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 = shaStateBytes sha256IV)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hread_iv : s₀.mem.Readable (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32)
    (hdisj_iv_stack : DisjointRegions (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (P b F alloc) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧
      s'.status = .Running ∧
      CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  have hkey_len : (s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat).length ≤ 64 := by
    rw [Memory.readBytes_length]; exact hlen
  refine (nfs_first_half hpc hstat hlen hiv hb hread_iv hdisj_iv_stack hrw_out hrw_stack
    hdisj_out_stack hdisj_key_stack hal).trans fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx0_1, hx1_1, hx2_1, hist1, hblk1, hivsw1⟩
  exact nfs_second_half hkey_len hal hpc1 hstat1 hR1 hM1 hx0_1 hx1_1 hx2_1 hist1 hblk1 hivsw1

/-! ## Relocatable `[LibsignalPlacement]` Second Half and Full Contract (Block 114) -/

structure NfsOpadPostHookPlaced [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (s₀ : State) (key : List (BitVec 8)) (s : State) : Prop where
  pc_eq   : s.pc = (blkPl_114).base + 1264#64
  status  : s.status = .Running
  regInv  : NfsRegInv nfsPlacedFakeB s₀ s
  memInv  : NfsMemInv nfsPlacedFakeB s₀ s.mem
  ist_eq  : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes (innerState F key)
  blk_eq  : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8)
  ivsw_eq : s.mem.readBytes (nfsSp s₀) 32 =
    (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16

theorem nfs_compress1_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {s₀ s : State} {key : List (BitVec 8)}
    (hpc : s.pc = (blkPl_114).base + 1260#64) (hstat : s.status = .Running)
    (hR : NfsRegInv nfsPlacedFakeB s₀ s) (hM : NfsMemInv nfsPlacedFakeB s₀ s.mem)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64) (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hist : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8))
    (hivsw : s.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsTo (lsProg_114 H) s (NfsOpadPostHookPlaced F s₀ key) := by
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  sess_step
  have hrw_ist : s.mem.RW (nfsSp s₀ + 400#64) 32 := hM.rw_stack.sub (by clear * -; bv_omega)
  refine RunsTo.placed_compress256_step h_compress
    (hrun := hstat) (hpc := rfl) (hx0 := hx0) (hx1 := hx1) (hx2 := hx2)
    (hlr := rfl) (hmem := rfl) (hst := hist) (hblk := hblk) (hrw := hrw_ist) ?_
  refine RunsTo.refl
    { pc_eq := rfl, status := hstat,
      regInv := ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩,
      memInv := hM.writeBytes_low 400#64 _ (by simp [shaStateBytes_length]),
      ist_eq := Layout.readBytes_writeBytes_eq s.mem (nfsSp s₀ + 400#64) _ 32 (shaStateBytes_length _) (by decide),
      blk_eq := (Layout.readBytes_writeBytes_of_disjoint s.mem (nfsSp s₀ + 400#64) _ (nfsSp s₀ + 288#64) 64
        (by clear * -; simp only [shaStateBytes_length, DisjointRegions]; bv_omega) (by decide)).trans hblk,
      ivsw_eq := (Layout.readBytes_writeBytes_of_disjoint s.mem (nfsSp s₀ + 400#64) _ (nfsSp s₀) 32
        (by clear * -; simp only [shaStateBytes_length, DisjointRegions]; bv_omega) (by decide)).trans hivsw }

structure NfsOpadMidStatePlaced [LibsignalPlacement] (pcOff nextOff0 nextOff1 : BitVec 64)
    (s₀ : State) (m_init m_cur : Memory) (s : State) : Prop where
  pc_eq  : s.pc = (blkPl_114).base + pcOff
  status : s.status = .Running
  regInv : NfsRegInv nfsPlacedFakeB s₀ s
  x0_eq  : s.readReg64 .x0 = nfsSp s₀ + 176#64
  x1_eq  : s.readReg64 .x1 = nfsSp s₀ + 288#64
  x8_eq  : s.readReg64 .x8 = 0x6a#64
  x10_eq : s.readReg64 .x10 = (s.mem.read8 (nfsSp s₀ + nextOff0)).zeroExtend 64
  x11_eq : s.readReg64 .x11 = (s.mem.read8 (nfsSp s₀ + nextOff1)).zeroExtend 64
  q0_eq  : s.readVReg128 0#5 = m_init.read128 (nfsSp s₀)
  q1_eq  : s.readVReg128 1#5 = m_init.read128 (nfsSp s₀ + 16#64)
  mem_eq : s.mem = m_cur

theorem nfs_opad_chunk0_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} {s₀ s : State} {key : List (BitVec 8)}
    (hs : NfsOpadPostHookPlaced F s₀ key s) :
    RunsTo (lsProg_114 H) s
      (NfsOpadMidStatePlaced 1480#64 304#64 305#64 s₀ s.mem (xorChunk s.mem (nfsSp s₀ + 288#64))) := by
  generalize hPost : (NfsOpadMidStatePlaced _ _ _ _ _ _) = Post
  have hpc := hs.pc_eq; have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hrw : s.mem.RW (nfsSp s₀) 544 := hs.memInv.rw_stack
  iterate 54 sess_step
  subst hPost; refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, Memory.read128, BitVec.add_assoc],
    by simp (config := { decide := true }) only [arm64_norm, Memory.read128, BitVec.add_assoc],
    by simp only [xorChunk, BitVec.add_assoc, arm64_norm]⟩

theorem nfs_opad_chunk1_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s₀ s : State} {m_init m_cur : Memory} (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : NfsOpadMidStatePlaced 1480#64 304#64 305#64 s₀ m_init m_cur s) :
    RunsTo (lsProg_114 H) s
      (NfsOpadMidStatePlaced 1672#64 320#64 321#64 s₀ m_init (xorChunk s.mem (nfsSp s₀ + 304#64))) := by
  generalize hPost : (NfsOpadMidStatePlaced _ _ _ _ _ _) = Post
  have hpc := hs.pc_eq; have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hx0 := hs.x0_eq; have hx1 := hs.x1_eq; have hx8 := hs.x8_eq
  have hx10 := hs.x10_eq; have hx11 := hs.x11_eq; have hq0 := hs.q0_eq; have hq1 := hs.q1_eq
  have hrw : s.mem.RW (nfsSp s₀) 544 := hs.mem_eq ▸ hrw_cur
  iterate 48 sess_step
  subst hPost; refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    by simp only [arm64_norm, hx0], by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx8],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hq0],
    by simp (config := { decide := true }) only [arm64_norm, hq1],
    by simp only [xorChunk, BitVec.add_assoc, arm64_norm]⟩

theorem nfs_opad_chunk2_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s₀ s : State} {m_init m_cur : Memory} (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : NfsOpadMidStatePlaced 1672#64 320#64 321#64 s₀ m_init m_cur s) :
    RunsTo (lsProg_114 H) s
      (NfsOpadMidStatePlaced 1864#64 336#64 337#64 s₀ m_init (xorChunk s.mem (nfsSp s₀ + 320#64))) := by
  generalize hPost : (NfsOpadMidStatePlaced _ _ _ _ _ _) = Post
  have hpc := hs.pc_eq; have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hx0 := hs.x0_eq; have hx1 := hs.x1_eq; have hx8 := hs.x8_eq
  have hx10 := hs.x10_eq; have hx11 := hs.x11_eq; have hq0 := hs.q0_eq; have hq1 := hs.q1_eq
  have hrw : s.mem.RW (nfsSp s₀) 544 := hs.mem_eq ▸ hrw_cur
  iterate 48 sess_step
  subst hPost; refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    by simp only [arm64_norm, hx0], by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx8],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hq0],
    by simp (config := { decide := true }) only [arm64_norm, hq1],
    by simp only [xorChunk, BitVec.add_assoc, arm64_norm]⟩

structure NfsOpadEndStatePlaced [LibsignalPlacement] (s₀ : State) (m_init m3 : Memory) (s : State) : Prop where
  pc_eq  : s.pc = (blkPl_114).base + 2060#64
  status : s.status = .Running
  regInv : NfsRegInv nfsPlacedFakeB s₀ s
  x0_eq  : s.readReg64 .x0 = nfsSp s₀ + 176#64
  x1_eq  : s.readReg64 .x1 = nfsSp s₀ + 288#64
  x2_eq  : s.readReg64 .x2 = 1#64
  mem_eq : s.mem = ((m3.write128 (nfsSp s₀ + 176#64) (m_init.read128 (nfsSp s₀ + 16#64))).write128
    (nfsSp s₀ + 192#64) (m_init.read128 (nfsSp s₀))).write64 (nfsSp s₀ + 208#64) 1#64

theorem nfs_opad_chunk3_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s₀ s : State} {m_init m_cur : Memory} (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : NfsOpadMidStatePlaced 1864#64 336#64 337#64 s₀ m_init m_cur s) :
    RunsTo (lsProg_114 H) s
      (NfsOpadEndStatePlaced s₀ m_init (xorChunk s.mem (nfsSp s₀ + 336#64))) := by
  generalize hPost : (NfsOpadEndStatePlaced _ _ _) = Post
  have hpc := hs.pc_eq; have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hx0 := hs.x0_eq; have hx1 := hs.x1_eq; have hx8 := hs.x8_eq
  have hx10 := hs.x10_eq; have hx11 := hs.x11_eq; have hq0 := hs.q0_eq; have hq1 := hs.q1_eq
  have hrw : s.mem.RW (nfsSp s₀) 544 := hs.mem_eq ▸ hrw_cur
  iterate 49 sess_step
  subst hPost; refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    by simp only [arm64_norm, hx0], by simp only [arm64_norm, hx1], by simp only [arm64_norm],
    by simp only [xorChunk, Memory.write128, Memory.read128, BitVec.add_assoc, arm64_norm]⟩

structure NfsPreCompress2Placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (s₀ : State) (key : List (BitVec 8)) (s : State) : Prop where
  pc_eq  : s.pc = (blkPl_114).base + 2060#64
  status : s.status = .Running
  regInv : NfsRegInv nfsPlacedFakeB s₀ s
  memInv : NfsMemInv nfsPlacedFakeB s₀ s.mem
  x0_eq  : s.readReg64 .x0 = nfsSp s₀ + 176#64
  x1_eq  : s.readReg64 .x1 = nfsSp s₀ + 288#64
  x2_eq  : s.readReg64 .x2 = 1#64
  ist_eq : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes (innerState F key)
  blk_eq : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x5c#8)
  ost_eq : s.mem.readBytes (nfsSp s₀ + 176#64) 32 = shaStateBytes sha256IV
  obl_eq : s.mem.read64 (nfsSp s₀ + 208#64) = 1#64

theorem nfs_opad_loop_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {s₀ s : State} {key : List (BitVec 8)} (hlen : key.length ≤ 64)
    (hpc : s.pc = (blkPl_114).base + 1260#64) (hstat : s.status = .Running)
    (hR : NfsRegInv nfsPlacedFakeB s₀ s) (hM : NfsMemInv nfsPlacedFakeB s₀ s.mem)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64) (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hist : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8))
    (hivsw : s.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsTo (lsProg_114 H) s (NfsPreCompress2Placed F s₀ key) := by
  have hopad_len : ((keyBlock key).map (· ^^^ 0x5c#8)).length = 64 := by simp [keyBlock_length hlen]
  have hiv_len : (shaStateBytes sha256IV).length = 32 := shaStateBytes_length sha256IV
  refine (nfs_compress1_placed_runsTo h_compress hpc hstat hR hM hx0 hx1 hx2 hist hblk hivsw).trans fun s1 h1 => ?_
  refine (nfs_opad_chunk0_placed h1).trans fun s2 h2 => ?_
  have hrw1 : (xorChunk s1.mem (nfsSp s₀ + 288#64)).RW (nfsSp s₀) 544 := rw_xorChunk _ h1.memInv.rw_stack
  refine (nfs_opad_chunk1_placed hrw1 h2).trans fun s3 h3 => ?_
  have hrw2 : (xorChunk s2.mem (nfsSp s₀ + 304#64)).RW (nfsSp s₀) 544 := rw_xorChunk _ (h2.mem_eq ▸ hrw1)
  refine (nfs_opad_chunk2_placed hrw2 h3).trans fun s4 h4 => ?_
  have hrw3 : (xorChunk s3.mem (nfsSp s₀ + 320#64)).RW (nfsSp s₀) 544 := rw_xorChunk _ (h3.mem_eq ▸ hrw2)
  refine (nfs_opad_chunk3_placed hrw3 h4).mono fun s5 h5 => ?_
  have hm4 : xorChunk s4.mem (nfsSp s₀ + 336#64) =
      s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8)) := by
    rw [h4.mem_eq, h3.mem_eq, h2.mem_eq,
      (by clear * -; bv_omega : nfsSp s₀ + 304#64 = (nfsSp s₀ + 288#64) + 16#64),
      (by clear * -; bv_omega : nfsSp s₀ + 320#64 = (nfsSp s₀ + 288#64) + 32#64),
      (by clear * -; bv_omega : nfsSp s₀ + 336#64 = (nfsSp s₀ + 288#64) + 48#64),
      xorChunk4_eq_writeBytes, h1.blk_eq, map_xor_0x36_0x6a]
  have hmem5 : s5.mem =
      (((s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8))).writeBytes
        (nfsSp s₀ + 176#64) (shaStateBytes sha256IV)).write64 (nfsSp s₀ + 208#64) 1#64) := by
    rw [h5.mem_eq, hm4, write128_pair_ivsw _ s1.mem (nfsSp s₀) h1.ivsw_eq]
  have hM5 : NfsMemInv nfsPlacedFakeB s₀ s5.mem := by
    rw [hmem5]
    exact ((h1.memInv.writeBytes_low 288#64 _ (by rw [hopad_len]; decide)).writeBytes_low
      176#64 _ (by rw [hiv_len]; decide)).write64_low 208#64 1#64 (by decide)
  have hA_opad := AgreesOutside.writeBytes_self s1.mem (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8))
  have hA_iv := AgreesOutside.writeBytes_self (s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8)))
    (nfsSp s₀ + 176#64) (shaStateBytes sha256IV)
  have hA_208 := AgreesOutside.write64_self
    ((s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8))).writeBytes
      (nfsSp s₀ + 176#64) (shaStateBytes sha256IV)) (nfsSp s₀ + 208#64) 1#64
  refine {
    pc_eq := h5.pc_eq, status := h5.status, regInv := h5.regInv, memInv := hM5,
    x0_eq := h5.x0_eq, x1_eq := h5.x1_eq, x2_eq := h5.x2_eq,
    ist_eq := by
      rw [hmem5, (agreesOutside_toFrame hA_208).readBytes_eq
            (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
          (agreesOutside_toFrame hA_iv).readBytes_eq
            (by rw [hiv_len]; clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
          (agreesOutside_toFrame hA_opad).readBytes_eq
            (by rw [hopad_len]; clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
          h1.ist_eq]
    blk_eq := by
      rw [hmem5, (agreesOutside_toFrame hA_208).readBytes_eq
            (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
          (agreesOutside_toFrame hA_iv).readBytes_eq
            (by rw [hiv_len]; clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide)]
      exact Layout.readBytes_writeBytes_eq s1.mem (nfsSp s₀ + 288#64) _ 64 hopad_len (by decide)
    ost_eq := by
      rw [hmem5, (agreesOutside_toFrame hA_208).readBytes_eq
            (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide)]
      exact Layout.readBytes_writeBytes_eq _ (nfsSp s₀ + 176#64) _ 32 hiv_len (by decide)
    obl_eq := by rw [hmem5, Memory.read64_write64_same] }

structure NfsPostCompress2Placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (s₀ : State) (key : List (BitVec 8)) (s : State) : Prop where
  pc_eq  : s.pc = (blkPl_114).base + 2064#64
  status : s.status = .Running
  regInv : NfsRegInv nfsPlacedFakeB s₀ s
  memInv : NfsMemInv nfsPlacedFakeB s₀ s.mem
  ist_eq : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes (innerState F key)
  ost_eq : s.mem.readBytes (nfsSp s₀ + 176#64) 32 = shaStateBytes (outerState F key)
  obl_eq : s.mem.read64 (nfsSp s₀ + 208#64) = 1#64

theorem nfs_compress2_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {s₀ s : State} {key : List (BitVec 8)} (hs : NfsPreCompress2Placed F s₀ key s) :
    RunsTo (lsProg_114 H) s (NfsPostCompress2Placed F s₀ key) := by
  have hpc := hs.pc_eq; have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hM := hs.memInv; sess_step
  have hrw_ost : s.mem.RW (nfsSp s₀ + 176#64) 32 := hM.rw_stack.sub (by clear * -; bv_omega)
  refine RunsTo.placed_compress256_step h_compress
    (hrun := hstat) (hpc := rfl) (hx0 := hs.x0_eq) (hx1 := hs.x1_eq) (hx2 := hs.x2_eq)
    (hlr := rfl) (hmem := rfl) (hst := hs.ost_eq) (hblk := hs.blk_eq) (hrw := hrw_ost) ?_
  have hA := AgreesOutside.writeBytes_self s.mem (nfsSp s₀ + 176#64)
    (shaStateBytes (F sha256IV ((keyBlock key).map (· ^^^ 0x5c#8))))
  refine RunsTo.refl
    { pc_eq := rfl, status := hstat,
      regInv := ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩,
      memInv := hM.writeBytes_low 176#64 _ (by simp [shaStateBytes_length]),
      ist_eq := (Layout.readBytes_writeBytes_of_disjoint s.mem (nfsSp s₀ + 176#64) _ (nfsSp s₀ + 400#64) 32
        (by clear * -; simp only [shaStateBytes_length, DisjointRegions]; bv_omega) (by decide)).trans hs.ist_eq,
      ost_eq := Layout.readBytes_writeBytes_eq s.mem (nfsSp s₀ + 176#64) _ 32 (shaStateBytes_length _) (by decide),
      obl_eq := ((agreesOutside_toFrame hA).read64_eq
        (by clear * -; simp only [shaStateBytes_length, List.mem_singleton, forall_eq, DisjointRegions]; bv_omega)).trans hs.obl_eq }

theorem nfs_epilogue_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} {s₀ s : State} {key : List (BitVec 8)}
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) (hs : NfsPostCompress2Placed F s₀ key s) :
    RunsTo (lsProg_114 H) s (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  generalize hPost : (fun s' : State => _) = Post
  have hpc := hs.pc_eq; have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hM := hs.memInv; have hm_ost := hs.ost_eq; have hm_ist := hs.ist_eq; have hm_208 := hs.obl_eq
  have hm_432 := hM.saved.m432; have hm_464 := hM.saved.m464; have hm_472 := hM.saved.m472
  have hm_480 := hM.saved.m480; have hm_496 := hM.saved.m496; have hm_504 := hM.saved.m504
  have hm_512 := hM.saved.m512; have hm_520 := hM.saved.m520; have hm_528 := hM.saved.m528
  have hm_536 := hM.saved.m536; have hrw_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  have hrw_out : s.mem.RW (s₀.readReg64 .x0) 0x98 := hM.rw_out
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hcross1 := read64_sp_write8_out hM.disj_out_stack
  have hcross2 := read64_sp_write64_out hM.disj_out_stack
  have hcross3 := read64_sp_write64_out_zero hM.disj_out_stack
  have hcross4 := read64_out_write64_sp hM.disj_out_stack
  have hcross5 := read64_out_zero_write64_sp hM.disj_out_stack
  have hcross6 := read8_out_write64_sp hM.disj_out_stack
  iterate 25 sess_step
  subst hPost; refine RunsTo.refl ?_
  have hsp_restore : nfsSp s₀ + 544#64 = s₀.sp := (nfs_sp_eq_add s₀).symm
  have hpos_addr : (s₀.readReg64 .x0 + 8#64) + 0x3f#64 = s₀.readReg64 .x0 + 71#64 := by clear * -; bv_omega
  have hist_addr : (s₀.readReg64 .x0 + 8#64) + 0x40#64 = s₀.readReg64 .x0 + 72#64 := by clear * -; bv_omega
  have hibl_addr : (s₀.readReg64 .x0 + 8#64) + 0x60#64 = s₀.readReg64 .x0 + 104#64 := by clear * -; bv_omega
  have host_addr : (s₀.readReg64 .x0 + 8#64) + 0x68#64 = s₀.readReg64 .x0 + 112#64 := by clear * -; bv_omega
  have hobl_addr : (s₀.readReg64 .x0 + 8#64) + 0x88#64 = s₀.readReg64 .x0 + 144#64 := by clear * -; bv_omega
  refine ⟨by simp only [arm64_norm], by simp only [arm64_norm, hstat], ?_, ?_, ?_, ?_⟩
  · refine ⟨by simp only [arm64_norm, hsp_restore], fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := { decide := true }) only [arm64_norm, hx25, hx26, hx27]
  · simp (config := { decide := true }) only [arm64_norm, *]
  · refine ⟨by decide, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpos_addr]; simp (config := { decide := true }) only [arm64_norm, *]
    · rw [hist_addr, ← hm_ist]
      refine readBytes_32_eq_of_read64_eq _ s.mem (s₀.readReg64 .x0 + 72#64) (nfsSp s₀ + 400#64) ?_ ?_ ?_ ?_ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, *]
    · rw [hibl_addr]; simp (config := { decide := true }) only [arm64_norm, *]
    · rw [host_addr, ← hm_ost]
      refine readBytes_32_eq_of_read64_eq _ s.mem (s₀.readReg64 .x0 + 112#64) (nfsSp s₀ + 176#64) ?_ ?_ ?_ ?_ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, *]
    · rw [hobl_addr]; simp (config := { decide := true }) only [arm64_norm, *]
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC, State.setPC]
    refine Frame.write64_out ?_ 80#64 _; refine Frame.write64_out ?_ 72#64 _
    refine Frame.write64_out ?_ 144#64 _; refine Frame.write64_out ?_ 136#64 _
    refine Frame.write64_stack ?_ 56#64 _; refine Frame.write64_stack ?_ 48#64 _
    refine Frame.write64_stack ?_ 40#64 _; refine Frame.write64_stack ?_ 32#64 _
    refine Frame.write64_out ?_ 96#64 _; refine Frame.write64_out ?_ 88#64 _
    refine Frame.write64_out ?_ 128#64 _; refine Frame.write64_out ?_ 120#64 _
    refine Frame.write64_out ?_ 112#64 _; refine Frame.write64_out ?_ 104#64 _
    refine Frame.write64_out_zero ?_ 0#64; refine Frame.write64_stack ?_ 104#64 _
    refine Frame.write64_stack ?_ 96#64 _; refine Frame.write64_stack ?_ 88#64 _
    refine Frame.write64_stack ?_ 80#64 _; refine Frame.write64_stack ?_ 72#64 _
    refine Frame.write64_stack ?_ 64#64 _; exact Frame.write8_out hM.frame 71#64 _

/-- Placed second half of `new_from_slice` (Block 114, `+1260 → s₀.readReg64 .lr`). -/
theorem nfs_second_half_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {s₀ s : State} {key : List (BitVec 8)} (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) (hpc : s.pc = (blkPl_114).base + 1260#64)
    (hstat : s.status = .Running) (hR : NfsRegInv nfsPlacedFakeB s₀ s)
    (hM : NfsMemInv nfsPlacedFakeB s₀ s.mem) (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64) (hx2 : s.readReg64 .x2 = 1#64)
    (hist : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8))
    (hivsw : s.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsTo (lsProg_114 H) s (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  refine (nfs_opad_loop_placed h_compress hlen hpc hstat hR hM hx0 hx1 hx2 hist hblk hivsw).trans fun s1 h1 => ?_
  refine (nfs_compress2_placed_runsTo h_compress h1).trans fun s2 h2 => ?_
  exact nfs_epilogue_placed hal h2

/-- Full placed `RunsTo` contract for `<Hmac<Sha256> as KeyInit>::new_from_slice` (Block 114). -/
theorem new_from_slice_placed_run [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) {s₀ : State}
    (hpc : s₀.pc = (blkPl_114).base) (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable lsSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions lsSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_114 H) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  have hkey_len : (s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat).length ≤ 64 := by
    rw [Memory.readBytes_length]; exact hlen
  refine (nfs_first_half_placed h_memcpy hpc hstat hlen hiv hread_iv hdisj_iv_stack hrw_out hrw_stack
    hdisj_out_stack hdisj_key_stack hal).trans fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx0_1, hx1_1, hx2_1, hist1, hblk1, hivsw1⟩
  exact nfs_second_half_placed h_compress hkey_len hal hpc1 hstat1 hR1 hM1 hx0_1 hx1_1 hx2_1 hist1 hblk1 hivsw1

end CryptoVerification.LibsignalSession.CryptoHmacSha256
