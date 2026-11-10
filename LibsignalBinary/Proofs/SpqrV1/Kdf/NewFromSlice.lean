/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceFirstHalf
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
public import LibsignalBinary.Proofs.SpqrV1.Kdf.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hmac.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed

/-!
# `Hmac<Sha256>::new_from_slice [local#3]`: Second Half and Short-Key Contract

Symbolic execution of the inner/outer compression and opad XOR blocks (`0x6748c → lr`) and full
`key.length ≤ 64` contracts (fixed-base and Block `402` `[LibsignalPlacement]`) for
`<Hmac<Sha256> as KeyInit>::new_from_slice [local#3]`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.CBC CryptoGames.LibsignalSession
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
open CryptoVerification.LibsignalSessionRepr
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

@[simp, arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [0x62094 → 0x62418]

set_option maxHeartbeats 1600000 in
structure Nfs3OpadPostHook (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (s₀ : State) (key : List (BitVec 8)) (s : State) : Prop where
  pc_eq   : s.pc = b + 0x62098#64
  status  : s.status = .Running
  regInv  : NfsRegInv3 b s₀ s
  memInv  : NfsMemInv3 b s₀ s.mem
  ist_eq  : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes (innerState F key)
  blk_eq  : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8)
  ivsw_eq : s.mem.readBytes (nfsSp s₀) 32 =
    (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16

theorem nfs_compress1_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hpc : s.pc = b + 0x62094#64)
    (hstat : s.status = .Running)
    (hR : NfsRegInv3 b s₀ s)
    (hM : NfsMemInv3 b s₀ s.mem)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hist : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8))
    (hivsw : s.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsTo (P b F alloc) s (Nfs3OpadPostHook b F s₀ key) := by
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

structure Nfs3OpadMidState (pcOff nextOff0 nextOff1 : BitVec 64)
    (b : BitVec 64) (s₀ : State) (m_init m_cur : Memory) (s : State) : Prop where
  pc_eq  : s.pc = b + pcOff
  status : s.status = .Running
  regInv : NfsRegInv3 b s₀ s
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
    (hs : Nfs3OpadPostHook b F s₀ key s) :
    RunsTo (P b F alloc) s
      (Nfs3OpadMidState 0x62170#64 304#64 305#64 b s₀ s.mem (xorChunk s.mem (nfsSp s₀ + 288#64))) := by
  generalize hPost : (Nfs3OpadMidState _ _ _ _ _ _ _) = Post
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

set_option maxHeartbeats 1600000 in
theorem nfs_opad_chunk1 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    {s₀ s : State} {m_init m_cur : Memory}
    (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : Nfs3OpadMidState 0x62170#64 304#64 305#64 b s₀ m_init m_cur s) :
    RunsTo (P b F alloc) s
      (Nfs3OpadMidState 0x62230#64 320#64 321#64 b s₀ m_init (xorChunk s.mem (nfsSp s₀ + 304#64))) := by
  generalize hPost : (Nfs3OpadMidState _ _ _ _ _ _ _) = Post
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

set_option maxHeartbeats 1600000 in
theorem nfs_opad_chunk2 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    {s₀ s : State} {m_init m_cur : Memory}
    (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : Nfs3OpadMidState 0x62230#64 320#64 321#64 b s₀ m_init m_cur s) :
    RunsTo (P b F alloc) s
      (Nfs3OpadMidState 0x622f0#64 336#64 337#64 b s₀ m_init (xorChunk s.mem (nfsSp s₀ + 320#64))) := by
  generalize hPost : (Nfs3OpadMidState _ _ _ _ _ _ _) = Post
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

set_option maxHeartbeats 1600000 in
/-- State at `b + 0x677ac#64` after opad chunk 3 and outer IV / block count initialization. -/
structure Nfs3OpadEndState (b : BitVec 64) (s₀ : State) (m_init m3 : Memory) (s : State) : Prop where
  pc_eq  : s.pc = b + 0x623b4#64
  status : s.status = .Running
  regInv : NfsRegInv3 b s₀ s
  x0_eq  : s.readReg64 .x0 = nfsSp s₀ + 176#64
  x1_eq  : s.readReg64 .x1 = nfsSp s₀ + 288#64
  x2_eq  : s.readReg64 .x2 = 1#64
  mem_eq : s.mem = ((m3.write128 (nfsSp s₀ + 176#64) (m_init.read128 (nfsSp s₀ + 16#64))).write128
    (nfsSp s₀ + 192#64) (m_init.read128 (nfsSp s₀))).write64 (nfsSp s₀ + 208#64) 1#64

theorem nfs_opad_chunk3 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    {s₀ s : State} {m_init m_cur : Memory}
    (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : Nfs3OpadMidState 0x622f0#64 336#64 337#64 b s₀ m_init m_cur s) :
    RunsTo (P b F alloc) s
      (Nfs3OpadEndState b s₀ m_init (xorChunk s.mem (nfsSp s₀ + 336#64))) := by
  generalize hPost : (Nfs3OpadEndState _ _ _ _) = Post
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

set_option maxHeartbeats 1600000 in
/-- Combined `compress256` #1 + opad XOR loop (`0x6748c → 0x677ac`, 201 steps). -/
structure Nfs3PreCompress2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (s₀ : State) (key : List (BitVec 8)) (s : State) : Prop where
  pc_eq  : s.pc = b + 0x623b4#64
  status : s.status = .Running
  regInv : NfsRegInv3 b s₀ s
  memInv : NfsMemInv3 b s₀ s.mem
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
    (hpc : s.pc = b + 0x62094#64)
    (hstat : s.status = .Running)
    (hR : NfsRegInv3 b s₀ s)
    (hM : NfsMemInv3 b s₀ s.mem)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hist : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8))
    (hivsw : s.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsTo (P b F alloc) s (Nfs3PreCompress2 b F s₀ key) := by
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
  have hM5 : NfsMemInv3 b s₀ s5.mem := by
    rw [hmem5]
    exact ((h1.memInv.writeBytes_low 288#64 _ (by rw [hopad_len]; decide)).writeBytes_low
      176#64 _ (by rw [hiv_len]; decide)).write64_low 208#64 1#64 (by decide)
  have hA_opad := ProofLib.agreesOutside_writeBytes s1.mem (nfsSp s₀ + 288#64)
    ((keyBlock key).map (· ^^^ 0x5c#8))
  have hA_iv := ProofLib.agreesOutside_writeBytes
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

/-! ## `compress256` #2 and Epilogue (`0x677ac → s₀.readReg64 .lr`, 27 steps) -/

structure Nfs3PostCompress2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (s₀ : State) (key : List (BitVec 8)) (s : State) : Prop where
  pc_eq  : s.pc = b + 0x623b8#64
  status : s.status = .Running
  regInv : NfsRegInv3 b s₀ s
  memInv : NfsMemInv3 b s₀ s.mem
  ist_eq : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes (innerState F key)
  ost_eq : s.mem.readBytes (nfsSp s₀ + 176#64) 32 = shaStateBytes (outerState F key)
  obl_eq : s.mem.read64 (nfsSp s₀ + 208#64) = 1#64

theorem nfs_compress2_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hs : Nfs3PreCompress2 b F s₀ key s) :
    RunsTo (P b F alloc) s (Nfs3PostCompress2 b F s₀ key) := by
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
  have hA := ProofLib.agreesOutside_writeBytes s.mem (nfsSp s₀ + 176#64)
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

set_option hygiene false in
local macro "nfs3_epilogue_body" : tactic => `(tactic| (
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
    refine Frame.write64_stack ?_ 64#64 _; exact Frame.write8_out hM.frame 71#64 _))

set_option maxHeartbeats 1600000 in
theorem nfs_epilogue {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hs : Nfs3PostCompress2 b F s₀ key s) :
    RunsTo (P b F alloc) s (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧
      s'.status = .Running ∧
      CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  nfs3_epilogue_body

/-- Full second half of `new_from_slice` (`0x6748c → s₀.readReg64 .lr`). -/
theorem nfs_second_half {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)}
    {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hpc : s.pc = b + 0x62094#64)
    (hstat : s.status = .Running)
    (hR : NfsRegInv3 b s₀ s)
    (hM : NfsMemInv3 b s₀ s.mem)
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

set_option maxHeartbeats 1600000 in
/-- Full `new_from_slice` contract (`0x66fa0 → s₀.readReg64 .lr`). -/
theorem new_from_slice3_run {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ : State}
    (hpc : s₀.pc = b + 0x61ba8#64)
    (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hread_iv : s₀.mem.Readable (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32)
    (hdisj_iv_stack : DisjointRegions (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 544#64) 544)
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

/-! ## `.rodata` SHA-256 IV at `0x837d8` and `NewFromSlice3OkExt` -/

noncomputable abbrev roSecSlice3 : List (BitVec 8) :=
  (libsignalSessionImage.data.drop (num% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964") - num% (ls_xref% 0x2440 0x2444))).take 96

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
theorem roSecSlice3_length : roSecSlice3.length = 96 := by
  rfl_kernel

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
theorem rodata_sha256IV_0x837d8_bytes :
    (roSecSlice3.drop 64).take 32 = shaStateBytes sha256IV := by
  rfl_kernel

open ProofLib.ProgramReflection in
theorem rodata_sha256IV_0x837d8 {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} (hro : img.RoDataLoaded m) :
    m.RO (img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 ∧
    m.readBytes (img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV := by
  have hdlen : num% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964") - num% (ls_xref% 0x2440 0x2444) + 96 ≤ libsignalSessionImage.data.length := by
    have hlen := roSecSlice3_length
    simp only [roSecSlice3, List.length_take, List.length_drop] at hlen
    omega
  have h := ProofLib.rodata_readBytes_disjoint himg (dataOff := num% (ls_xref% 0x2440 0x2444)) rfl
    (secOff := num% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964")) (secLen := 96) (by decide) (by decide) (by decide) hdlen (by rfl_kernel)
    m hro
  have hadd : img.base + BitVec.ofNat 64 (num% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964")) + 64#64 = img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64) := by
    clear * -; bv_omega
  have hro32 : m.RO (img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
    intro a ha
    apply h.1 a
    unfold InRegion at ha ⊢
    clear * - ha; bv_omega
  have hslice := readBytes_slice_of_readBytes_eq m (img.base + BitVec.ofNat 64 (num% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964"))) roSecSlice3
    (by rw [roSecSlice3_length]; exact h.2) 64 32 (by rw [roSecSlice3_length])
  rw [hadd, rodata_sha256IV_0x837d8_bytes] at hslice
  exact ⟨hro32, hslice⟩

open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.LibsignalTripleRatchet (newFromSliceSpec newFromSliceStack)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer

theorem new_from_slice3_ok_sessionProg (img : Obj.Image) (F : ShaCompress)
    (abs : String → Option (State → State)) (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (LibsignalSession.sessionProg img F abs) (img.base + 0x61ba8#64)
      ((newFromSliceSpec F).inImage img) := by
  rw [LibsignalSession.CryptoHmacSha256.sessionProg_eq_P himg F abs]
  refine subroutine_ok_intro fun ⟨ret, keyA, key⟩ R s0 hpc hrun hpre hsp => ?_
  rw [Spec.inImage, newFromSliceSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, _⟩, hpre⟩
  dsimp only at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_nat, hkey_len⟩, hsep⟩
  have hb_out := IsBlock.memRegion ret 0x98
  have hb_key := IsBlock.pointsToBytes (a := keyA) key
  have hb_stk := IsBlock.memRegion (s0.sp - 544#64) 544
  have hsep_out : s0.mem ⊨ memRegion ret 0x98 ∗ (memRegion (s0.sp - 544#64) 544 ∗
      ((keyA ↦ₛ key) ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep
    ac_nf at hsep ⊢
  have hsep_key : s0.mem ⊨ (keyA ↦ₛ key) ∗ (memRegion (s0.sp - 544#64) 544 ∗
      (memRegion ret 0x98 ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep
    ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 544#64) 544 ∗
      (memRegion ret 0x98 ∗ (keyA ↦ₛ key) ∗ R) := by
    simp only [newFromSliceStack, stackAt] at hsep
    ac_nf at hsep ⊢
  have hkey_eq : s0.mem.readBytes keyA key.length = key := (hb_key.read hsep_key).2
  have hrw_out : s0.mem.RW ret 0x98 := fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_stk : s0.mem.RW (s0.sp - 544#64) 544 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_sha256IV_0x837d8 himg hF.roData
  have hread_iv : s0.mem.Readable (img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hdisj_key : key.length = 0 ∨ DisjointRegions keyA key.length (s0.sp - 544#64) 544 := by
    rcases key with _ | ⟨k0, ks⟩
    · exact Or.inl rfl
    · exact Or.inr (hb_key.disjoint hb_stk (by simp) (by decide) hsep_key)
  have hx2_len : (s0.readReg64 .x2).toNat = key.length := hx2_nat
  have hrunsTo := new_from_slice3_run (F := F) (alloc := abs)
    hpc hrun (by rw [hx2_len]; exact hkey_len) hiv_eq (ProofLib.base_aligned_of_loads himg)
    hread_iv (LibsignalSession.CryptoHmacSha256.disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk)
    (by rw [hx0]; exact hrw_out) hrw_stk
    (by rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out)
    (by rw [hx1, hx2_len]; exact hdisj_key)
    (by simpa [State.spAligned] using hsp)
  rw [hx1, hx2_len, hkey_eq] at hrunsTo
  refine hrunsTo.to_reaches_pc fun sf h5 _ _ htr hvregs => ?_
  rcases h5 with ⟨hpc_sf, hstat_sf, hcallee, hret_sf, hst_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_,
    LibsignalSession.CryptoHmacSha256.CallingConventionPreserved_of_calleeSaved hcallee hvregs⟩
  rw [Spec.inImage, newFromSliceSpec]
  dsimp only []
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr, ?_⟩
  rw [hx0] at hret_sf hst_sf hframe_sf
  have hpost := LibsignalSession.CryptoHmacSha256.Frame.update_two_blocks hb_out
    (isBlock_nfsResult F ret key) hb_stk hb_stk hsep_out hframe_sf ⟨hret_sf, hst_sf⟩ trivial
  simp only [newFromSliceStack, stackAt]
  ac_nf at hpost ⊢

/-! ## Placed (`[LibsignalPlacement]`) Second Half & Full `new_from_slice [local#3]` Contract (Block `402`) -/

structure Nfs3OpadPostHookPlaced [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (s₀ : State) (key : List (BitVec 8)) (s : State) : Prop where
  pc_eq   : s.pc = (blkPl_402).base + 1264#64
  status  : s.status = .Running
  regInv  : NfsRegInv3 nfs3PlacedFakeB s₀ s
  memInv  : NfsMemInv3 nfs3PlacedFakeB s₀ s.mem
  ist_eq  : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes (innerState F key)
  blk_eq  : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8)
  ivsw_eq : s.mem.readBytes (nfsSp s₀) 32 =
    (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16

theorem nfs_compress1_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {s₀ s : State} {key : List (BitVec 8)}
    (hpc : s.pc = (blkPl_402).base + 1260#64) (hstat : s.status = .Running)
    (hR : NfsRegInv3 nfs3PlacedFakeB s₀ s) (hM : NfsMemInv3 nfs3PlacedFakeB s₀ s.mem)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64) (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hist : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8))
    (hivsw : s.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsTo (lsProg_402 H) s (Nfs3OpadPostHookPlaced F s₀ key) := by
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

structure Nfs3OpadMidStatePlaced [LibsignalPlacement] (pcOff nextOff0 nextOff1 : BitVec 64)
    (s₀ : State) (m_init m_cur : Memory) (s : State) : Prop where
  pc_eq  : s.pc = (blkPl_402).base + pcOff
  status : s.status = .Running
  regInv : NfsRegInv3 nfs3PlacedFakeB s₀ s
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
    (hs : Nfs3OpadPostHookPlaced F s₀ key s) :
    RunsTo (lsProg_402 H) s
      (Nfs3OpadMidStatePlaced 1480#64 304#64 305#64 s₀ s.mem (xorChunk s.mem (nfsSp s₀ + 288#64))) := by
  generalize hPost : (Nfs3OpadMidStatePlaced _ _ _ _ _ _) = Post
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

set_option maxHeartbeats 1600000 in
theorem nfs_opad_chunk1_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s₀ s : State} {m_init m_cur : Memory} (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : Nfs3OpadMidStatePlaced 1480#64 304#64 305#64 s₀ m_init m_cur s) :
    RunsTo (lsProg_402 H) s
      (Nfs3OpadMidStatePlaced 1672#64 320#64 321#64 s₀ m_init (xorChunk s.mem (nfsSp s₀ + 304#64))) := by
  generalize hPost : (Nfs3OpadMidStatePlaced _ _ _ _ _ _) = Post
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

set_option maxHeartbeats 1600000 in
theorem nfs_opad_chunk2_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s₀ s : State} {m_init m_cur : Memory} (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : Nfs3OpadMidStatePlaced 1672#64 320#64 321#64 s₀ m_init m_cur s) :
    RunsTo (lsProg_402 H) s
      (Nfs3OpadMidStatePlaced 1864#64 336#64 337#64 s₀ m_init (xorChunk s.mem (nfsSp s₀ + 320#64))) := by
  generalize hPost : (Nfs3OpadMidStatePlaced _ _ _ _ _ _) = Post
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

structure Nfs3OpadEndStatePlaced [LibsignalPlacement] (s₀ : State) (m_init m3 : Memory) (s : State) : Prop where
  pc_eq  : s.pc = (blkPl_402).base + 2060#64
  status : s.status = .Running
  regInv : NfsRegInv3 nfs3PlacedFakeB s₀ s
  x0_eq  : s.readReg64 .x0 = nfsSp s₀ + 176#64
  x1_eq  : s.readReg64 .x1 = nfsSp s₀ + 288#64
  x2_eq  : s.readReg64 .x2 = 1#64
  mem_eq : s.mem = ((m3.write128 (nfsSp s₀ + 176#64) (m_init.read128 (nfsSp s₀ + 16#64))).write128
    (nfsSp s₀ + 192#64) (m_init.read128 (nfsSp s₀))).write64 (nfsSp s₀ + 208#64) 1#64

set_option maxHeartbeats 1600000 in
theorem nfs_opad_chunk3_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s₀ s : State} {m_init m_cur : Memory} (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : Nfs3OpadMidStatePlaced 1864#64 336#64 337#64 s₀ m_init m_cur s) :
    RunsTo (lsProg_402 H) s
      (Nfs3OpadEndStatePlaced s₀ m_init (xorChunk s.mem (nfsSp s₀ + 336#64))) := by
  generalize hPost : (Nfs3OpadEndStatePlaced _ _ _) = Post
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

structure Nfs3PreCompress2Placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (s₀ : State) (key : List (BitVec 8)) (s : State) : Prop where
  pc_eq  : s.pc = (blkPl_402).base + 2060#64
  status : s.status = .Running
  regInv : NfsRegInv3 nfs3PlacedFakeB s₀ s
  memInv : NfsMemInv3 nfs3PlacedFakeB s₀ s.mem
  x0_eq  : s.readReg64 .x0 = nfsSp s₀ + 176#64
  x1_eq  : s.readReg64 .x1 = nfsSp s₀ + 288#64
  x2_eq  : s.readReg64 .x2 = 1#64
  ist_eq : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes (innerState F key)
  blk_eq : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x5c#8)
  ost_eq : s.mem.readBytes (nfsSp s₀ + 176#64) 32 = shaStateBytes sha256IV
  obl_eq : s.mem.read64 (nfsSp s₀ + 208#64) = 1#64

set_option maxHeartbeats 1600000 in
theorem nfs_opad_loop_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {s₀ s : State} {key : List (BitVec 8)} (hlen : key.length ≤ 64)
    (hpc : s.pc = (blkPl_402).base + 1260#64) (hstat : s.status = .Running)
    (hR : NfsRegInv3 nfs3PlacedFakeB s₀ s) (hM : NfsMemInv3 nfs3PlacedFakeB s₀ s.mem)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64) (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hist : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8))
    (hivsw : s.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsTo (lsProg_402 H) s (Nfs3PreCompress2Placed F s₀ key) := by
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
  have hM5 : NfsMemInv3 nfs3PlacedFakeB s₀ s5.mem := by
    rw [hmem5]
    exact ((h1.memInv.writeBytes_low 288#64 _ (by rw [hopad_len]; decide)).writeBytes_low
      176#64 _ (by rw [hiv_len]; decide)).write64_low 208#64 1#64 (by decide)
  have hA_opad := ProofLib.agreesOutside_writeBytes s1.mem (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8))
  have hA_iv := ProofLib.agreesOutside_writeBytes (s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8)))
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

structure Nfs3PostCompress2Placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (s₀ : State) (key : List (BitVec 8)) (s : State) : Prop where
  pc_eq  : s.pc = (blkPl_402).base + 2064#64
  status : s.status = .Running
  regInv : NfsRegInv3 nfs3PlacedFakeB s₀ s
  memInv : NfsMemInv3 nfs3PlacedFakeB s₀ s.mem
  ist_eq : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes (innerState F key)
  ost_eq : s.mem.readBytes (nfsSp s₀ + 176#64) 32 = shaStateBytes (outerState F key)
  obl_eq : s.mem.read64 (nfsSp s₀ + 208#64) = 1#64

theorem nfs_compress2_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {s₀ s : State} {key : List (BitVec 8)} (hs : Nfs3PreCompress2Placed F s₀ key s) :
    RunsTo (lsProg_402 H) s (Nfs3PostCompress2Placed F s₀ key) := by
  have hpc := hs.pc_eq; have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hM := hs.memInv; sess_step
  have hrw_ost : s.mem.RW (nfsSp s₀ + 176#64) 32 := hM.rw_stack.sub (by clear * -; bv_omega)
  refine RunsTo.placed_compress256_step h_compress
    (hrun := hstat) (hpc := rfl) (hx0 := hs.x0_eq) (hx1 := hs.x1_eq) (hx2 := hs.x2_eq)
    (hlr := rfl) (hmem := rfl) (hst := hs.ost_eq) (hblk := hs.blk_eq) (hrw := hrw_ost) ?_
  have hA := ProofLib.agreesOutside_writeBytes s.mem (nfsSp s₀ + 176#64)
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

set_option maxHeartbeats 1600000 in
theorem nfs_epilogue_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} {s₀ s : State} {key : List (BitVec 8)}
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) (hs : Nfs3PostCompress2Placed F s₀ key s) :
    RunsTo (lsProg_402 H) s (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  nfs3_epilogue_body

/-- Full second half of placed `new_from_slice [local#3]` (Block `402`, `+1260 → s₀.readReg64 .lr`). -/
theorem nfs_second_half_placed [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {s₀ s : State} {key : List (BitVec 8)} (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) (hpc : s.pc = (blkPl_402).base + 1260#64)
    (hstat : s.status = .Running) (hR : NfsRegInv3 nfs3PlacedFakeB s₀ s)
    (hM : NfsMemInv3 nfs3PlacedFakeB s₀ s.mem) (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64) (hx2 : s.readReg64 .x2 = 1#64)
    (hist : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8))
    (hivsw : s.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsTo (lsProg_402 H) s (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  refine (nfs_opad_loop_placed h_compress hlen hpc hstat hR hM hx0 hx1 hx2 hist hblk hivsw).trans fun s1 h1 => ?_
  refine (nfs_compress2_placed_runsTo h_compress h1).trans fun s2 h2 => ?_
  exact nfs_epilogue_placed hal h2

set_option maxHeartbeats 1600000 in
/-- Full placed `new_from_slice [local#3]` contract (Block `402`, `(blkPl_402).base → s₀.readReg64 .lr`). -/
theorem new_from_slice3_placed_run [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) {s₀ : State}
    (hpc : s₀.pc = (blkPl_402).base) (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  have hkey_len : (s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat).length ≤ 64 := by
    rw [Memory.readBytes_length]; exact hlen
  refine (nfs_first_half_placed h_memcpy hpc hstat hlen hiv hread_iv hdisj_iv_stack hrw_out hrw_stack
    hdisj_out_stack hdisj_key_stack hal).trans fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx0_1, hx1_1, hx2_1, hist1, hblk1, hivsw1⟩
  exact nfs_second_half_placed h_compress hkey_len hal hpc1 hstat1 hR1 hM1 hx0_1 hx1_1 hx2_1 hist1 hblk1 hivsw1

set_option maxRecDepth 2000000 in
/-- `.rodata` at `spqrSha256IVAddr` (`spqr:.rodata.cst32+0x40`) holds the 32-byte
SHA-256 IV under `LibsignalRoLoaded lsmpl m`. -/
theorem rodata_placed_spqrSha256IV [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) :
    m.RO spqrSha256IVAddr 32 ∧
    m.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV := by
  have h := lsro_read_chk hro (sym := spqrSha256IVSym)
    (bs := shaStateBytes sha256IV) (by decide +kernel)
  have haddr : spqrSha256IVAddr = lsmpl.ρ spqrSha256IVSym :=
    ls_resolve_data (tgt := spqrSha256IVSym) (by decide)
  rwa [← haddr, shaStateBytes_length] at h

/-- Relocatable `[LibsignalPlacement]` contract for `<Hmac<Sha256> as KeyInit>::new_from_slice [local#3]`
(Block `402`) under `LibsignalRoLoaded lsmpl`. -/
theorem new_from_slice3_placed_ro_ok [LibsignalPlacement] (F : ShaCompress)
    {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok (lsProg_402 H) (blkPl_402).base
      { newFromSliceSpec F with
        pre := fun x s0 => (newFromSliceSpec F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ } := by
  refine subroutine_ok_intro fun ⟨ret, keyA, key⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [newFromSliceSpec] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, ⟨hx0, hx1, hx2_nat, hkey_len⟩, hsep⟩
  have hb_out := IsBlock.memRegion ret 0x98
  have hb_key := IsBlock.pointsToBytes (a := keyA) key
  have hb_stk := IsBlock.memRegion (s0.sp - 544#64) 544
  have hsep_out : s0.mem ⊨ memRegion ret 0x98 ∗ (memRegion (s0.sp - 544#64) 544 ∗
      ((keyA ↦ₛ key) ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep; ac_nf at hsep ⊢
  have hsep_key : s0.mem ⊨ (keyA ↦ₛ key) ∗ (memRegion (s0.sp - 544#64) 544 ∗
      (memRegion ret 0x98 ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 544#64) 544 ∗
      (memRegion ret 0x98 ∗ (keyA ↦ₛ key) ∗ R) := by
    simp only [newFromSliceStack, stackAt] at hsep; ac_nf at hsep ⊢
  have hkey_eq : s0.mem.readBytes keyA key.length = key := (hb_key.read hsep_key).2
  have hrw_out : s0.mem.RW ret 0x98 := fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_stk : s0.mem.RW (s0.sp - 544#64) 544 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_placed_spqrSha256IV hro
  have hread_iv : s0.mem.Readable spqrSha256IVAddr 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hdisj_key : key.length = 0 ∨ DisjointRegions keyA key.length (s0.sp - 544#64) 544 := by
    rcases key with _ | ⟨k0, ks⟩
    · exact Or.inl rfl
    · exact Or.inr (hb_key.disjoint hb_stk (by simp) (by decide) hsep_key)
  have hx2_len : (s0.readReg64 .x2).toNat = key.length := hx2_nat
  have hrunsTo := new_from_slice3_placed_run (F := F) h_memcpy h_compress
    hpc hrun (by rw [hx2_len]; exact hkey_len) hiv_eq hread_iv
    (LibsignalSession.CryptoHmacSha256.disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk)
    (by rw [hx0]; exact hrw_out) hrw_stk
    (by rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out)
    (by rw [hx1, hx2_len]; exact hdisj_key)
    (by simpa [State.spAligned] using hsp)
  rw [hx1, hx2_len, hkey_eq] at hrunsTo
  refine hrunsTo.to_reaches_pc fun sf h5 _ _ htr hvregs => ?_
  rcases h5 with ⟨hpc_sf, hstat_sf, hcallee, hret_sf, hst_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_,
    LibsignalSession.CryptoHmacSha256.CallingConventionPreserved_of_calleeSaved hcallee hvregs⟩
  dsimp only [newFromSliceSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr, ?_⟩
  rw [hx0] at hret_sf hst_sf hframe_sf
  have hpost := LibsignalSession.CryptoHmacSha256.Frame.update_two_blocks hb_out
    (isBlock_nfsResult F ret key) hb_stk hb_stk hsep_out hframe_sf ⟨hret_sf, hst_sf⟩ trivial
  simp only [newFromSliceStack, stackAt]
  ac_nf at hpost ⊢

theorem new_from_slice3_placed_ok_withLsCodeLoaded_ro [LibsignalPlacement] (F : ShaCompress)
    {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok (lsProg_402 H) (blkPl_402).base
      (withLsCodeLoaded lsmpl
        { newFromSliceSpec F with
          pre := fun x s0 => (newFromSliceSpec F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ }) :=
  subroutine_ok_withLsCodeLoaded_of_plain (new_from_slice3_placed_ro_ok F h_memcpy h_compress)

end CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof

namespace CryptoVerification.SpqrV1.Kdf

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer

/-- `<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#3]` (`0x66fa0`)
meets `(newFromSliceSpec C.F).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
def NewFromSlice3OkExt (img : Obj.Image) (C : Crypto)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr newFromSlice3Name)
    ((newFromSliceSpec C.F).inImage img)

theorem newFromSlice3_fnAddr_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr newFromSlice3Name = b + 0x61ba8#64 := by
  unfold tripleRatchetProgAtExt newFromSlice3Name
  rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x61ba8]

/-- `<Hmac<Sha256> as KeyInit>::new_from_slice [local#3]` (`0x66fa0`, 541 instructions)
satisfies `(newFromSliceSpec C.F).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
theorem new_from_slice3_ok_ext (img : Obj.Image) (C : Crypto)
    {abs ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hle : ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns C.F abs) n = some f →
      Rust.withPanics ext n = some f) :
    NewFromSlice3OkExt img C ext := by
  unfold NewFromSlice3OkExt
  rw [newFromSlice3_fnAddr_ext]
  exact session_subroutine_ok_mono_ext himg hle
    (NewFromSlice3Proof.new_from_slice3_ok_sessionProg img C.F abs himg)

/-- Direct `RunsTo` on `tripleRatchetProgAtExt b ext` for `new_from_slice [local#3]` (`0x66fa0`). -/
theorem new_from_slice3_run_ext {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc ext : String → Option (State → State)} {s₀ : State}
    (hle : ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns F alloc) n = some f →
      Rust.withPanics ext n = some f)
    (hpc : s₀.pc = b + 0x61ba8#64)
    (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = LibsignalHmac.shaStateBytes sha256IV)
    (hb : (b &&& 0xfff#64) = 0#64)
    (hread_iv : s₀.mem.Readable (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32)
    (hdisj_iv_stack : DisjointRegions (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 544#64) 544)
    (hrw_out : LibsignalSession.CryptoHmacSha256.RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : LibsignalSession.CryptoHmacSha256.RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    LibsignalSession.CryptoHmacSha256.RunsTo (tripleRatchetProgAtExt b ext) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧
      s'.status = .Running ∧
      LibsignalSession.CryptoHmacSha256.CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      LibsignalSession.CryptoHmacSha256.HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F
        (s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat) [] ∧
      LibsignalSession.CryptoHmacSha256.Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  intro hL2
  have hL1 : (LibsignalSession.CryptoHmacSha256.P b F alloc).CodeLoaded s₀.mem := by
    rw [Program.codeLoaded_iff] at hL2 ⊢
    dsimp only [LibsignalSession.CryptoHmacSha256.P, tripleRatchetProgAtExt, Program.rebase] at hL2 ⊢
    exact hL2
  obtain ⟨s', hs, htr, hvregs, hpost, hL1'⟩ := NewFromSlice3Proof.new_from_slice3_run hpc hstat hlen hiv hb hread_iv
    hdisj_iv_stack hrw_out hrw_stack hdisj_out_stack hdisj_key_stack hal hL1
  have hL2' : (tripleRatchetProgAtExt b ext).CodeLoaded s'.mem := by
    rw [Program.codeLoaded_iff] at hL1' ⊢
    dsimp only [LibsignalSession.CryptoHmacSha256.P, tripleRatchetProgAtExt, Program.rebase] at hL1' ⊢
    exact hL1'
  have hnh : s'.status ≠ .Halted := by rw [hpost.2.1]; decide
  exact ⟨s', steps_mono libsignalSessionCode_stubs_offsets_fresh libsignalSessionCode_stubsDead
    hle hs hL1 hnh, htr, hvregs, hpost, hL2'⟩

end CryptoVerification.SpqrV1.Kdf

