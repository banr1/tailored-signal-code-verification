/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceLe64HalfExt
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.SpqrV1.Kdf.HooksExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice -- shake: keep

/-!
# Contract-Backed Second Half and Short-Key Path of `Hmac<Sha256>::new_from_slice`

Proves the shared second half (`0x6748c → lr`) and the full `key.length ≤ 64` `RunsToE` contract
(for both read-only and read-write keys) of `new_from_slice [local#3]`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf.Nfs3Ext

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.CBC
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
open CryptoVerification.LibsignalSessionRepr
open Obj
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame)
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof hiding
  NfsMemInv3 NfsRegInv3
  read64_write8_stack_iv write64_quad_400_iv write64_quad_0_ivsw
  Nfs3OpadPostHook Nfs3OpadMidState Nfs3OpadEndState
  Nfs3PreCompress2 Nfs3PostCompress2 rodata_sha256IV_0x837d8
open ProofLib.ProgramReflection
open CryptoVerification.CodeLayout

attribute [-arm64_norm, -simp] CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof.read64_write8_stack_iv

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
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
  Memory.read64_write8_base_off_disjoint
  Memory.read64_write8_base_zero_off
  Memory.read64_write8_base_off_zero
  truncate8_zeroExtend_xor_32
  truncate8_zeroExtend_xor_64

@[local simp, local arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [(ls_off% newFromSlice3Name + 1260) → (ls_off% newFromSlice3Name + 2164)]

/-! ## `S2FrameRO` Stack/KeyBlock Helpers and Second-Half Cut Predicates -/

theorem nfsSavedStack_write64_432_of_s2FrameRO {roRegs : List (BitVec 64 × ℕ)}
    {s₀ : State} {m m' : Memory} {sz : ℕ}
    (hs : NfsSavedStack s₀ (m.write64 (nfsSp s₀ + 432#64) 1#64))
    (hrw_stk : m.RW (nfsSp s₀) 544)
    (hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384)
    (hf : S2FrameRO roRegs m m'
      [(nfsSp s₀ + 112#64, sz), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hsz : sz ≤ 64) :
    NfsSavedStack s₀ (m'.write64 (nfsSp s₀ + 432#64) 1#64) := by
  have hread (k : BitVec 64) (hk : 464 ≤ k.toNat ∧ k.toNat + 8 ≤ 544) :
      (m'.write64 (nfsSp s₀ + 432#64) 1#64).read64 (nfsSp s₀ + k) =
      (m.write64 (nfsSp s₀ + 432#64) 1#64).read64 (nfsSp s₀ + k) := by
    have h1 : (m'.write64 (nfsSp s₀ + 432#64) 1#64).read64 (nfsSp s₀ + k) = m'.read64 (nfsSp s₀ + k) := by
      refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write64_self m' (nfsSp s₀ + 432#64) 1#64)) ?_
      rcases hk with ⟨hk1, hk2⟩
      clear * - hk1 hk2; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega
    have h2 : (m.write64 (nfsSp s₀ + 432#64) 1#64).read64 (nfsSp s₀ + k) = m.read64 (nfsSp s₀ + k) := by
      refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write64_self m (nfsSp s₀ + 432#64) 1#64)) ?_
      rcases hk with ⟨hk1, hk2⟩
      clear * - hk1 hk2; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega
    rw [h1, h2]
    exact s2FrameRO_hook_read64_stack_eq hf hrw_stk hd_stk_ext hk.2
      (by
        by_cases h0 : sz = 0
        · exact Or.inl h0
        · refine Or.inr ?_
          rcases hk with ⟨hk1, hk2⟩
          clear * - h0 hsz hk1 hk2
          constructor <;> bv_omega)
  exact {
    m432 := Memory.read64_write64_same m' (nfsSp s₀ + 432#64) 1#64
    m464 := (hread 464#64 (by decide)).trans hs.m464
    m472 := (hread 472#64 (by decide)).trans hs.m472
    m480 := (hread 480#64 (by decide)).trans hs.m480
    m496 := (hread 496#64 (by decide)).trans hs.m496
    m504 := (hread 504#64 (by decide)).trans hs.m504
    m512 := (hread 512#64 (by decide)).trans hs.m512
    m520 := (hread 520#64 (by decide)).trans hs.m520
    m528 := (hread 528#64 (by decide)).trans hs.m528
    m536 := (hread 536#64 (by decide)).trans hs.m536
  }

theorem readBytes_64_eq_keyBlock_of_s2FrameRO {roRegs : List (BitVec 64 × ℕ)}
    {sp : BitVec 64} {m1 m2 : Memory} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hrw_stk1 : m1.RW sp 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hzero1 : m1.readBytes (sp + 112#64) 64 = List.replicate 64 0#8)
    (hkey2 : m2.readBytes (sp + 112#64) key.length = key)
    (hf12 : S2FrameRO roRegs m1 m2
      [(sp + 112#64, key.length), (sp - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    m2.readBytes (sp + 112#64) 64 = keyBlock key := by
  have h64 : 64 = key.length + (64 - key.length) := (Nat.add_sub_of_le hlen).symm
  have hsplit2 : m2.readBytes (sp + 112#64) 64 =
      m2.readBytes (sp + 112#64) key.length ++
        m2.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) :=
    (congrArg (m2.readBytes (sp + 112#64)) h64).trans
      (Memory.readBytes_add m2 (sp + 112#64) key.length (64 - key.length))
  have hsplit1 : m1.readBytes (sp + 112#64) 64 =
      m1.readBytes (sp + 112#64) key.length ++
        m1.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) :=
    (congrArg (m1.readBytes (sp + 112#64)) h64).trans
      (Memory.readBytes_add m1 (sp + 112#64) key.length (64 - key.length))
  have htail1 : m1.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) =
      List.replicate (64 - key.length) 0#8 := by
    have hd := congrArg (List.drop key.length) (hsplit1.symm.trans hzero1)
    rwa [List.drop_left' (Memory.readBytes_length _ _ _), List.drop_replicate] at hd
  have htail2 : m2.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) =
      m1.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) := by
    have hrw_tail : RW m1 ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) :=
      hrw_stk1.sub (by clear * - hlen; bv_omega)
    refine Memory.readBytes_congr_region (by omega) fun b hb => ?_
    obtain ⟨hperm_b, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw_tail b hb)
    have hr : (m1.perm b).r = true := by rw [hperm_b]; rfl
    refine hf12.1 b hr hlf fun r hr_mem => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
    rcases hr_mem with rfl | rfl
    · clear * - hlen hb
      simp only [InRegion, OutsideRegion] at hb ⊢
      bv_omega
    · have hb_stk : InRegion sp 544 b := by
        clear * - hlen hb
        simp only [InRegion] at hb ⊢
        bv_omega
      exact hd_stk_ext.symm.outside hb_stk (by decide)
  rw [hsplit2, hkey2, htail2, htail1]
  rfl

structure Nfs3OpadPostHook (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (s₀ : State) (key : List (BitVec 8)) (s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% newFromSlice3Name + 1264)
  status  : s.status = .Running
  regInv  : NfsRegInv3 b s₀ s
  memInv  : NfsMemInv3 b s₀ s.mem
  ist_eq  : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes (innerState F key)
  blk_eq  : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8)
  ivsw_eq : s.mem.readBytes (nfsSp s₀) 32 =
    (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16

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

structure Nfs3OpadEndState (b : BitVec 64) (s₀ : State) (m_init m3 : Memory) (s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% newFromSlice3Name + 2060)
  status : s.status = .Running
  regInv : NfsRegInv3 b s₀ s
  x0_eq  : s.readReg64 .x0 = nfsSp s₀ + 176#64
  x1_eq  : s.readReg64 .x1 = nfsSp s₀ + 288#64
  x2_eq  : s.readReg64 .x2 = 1#64
  mem_eq : s.mem = ((m3.write128 (nfsSp s₀ + 176#64) (m_init.read128 (nfsSp s₀ + 16#64))).write128
    (nfsSp s₀ + 192#64) (m_init.read128 (nfsSp s₀))).write64 (nfsSp s₀ + 208#64) 1#64

structure Nfs3PreCompress2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (s₀ : State) (key : List (BitVec 8)) (s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% newFromSlice3Name + 2060)
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

structure Nfs3PostCompress2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (s₀ : State) (key : List (BitVec 8)) (s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% newFromSlice3Name + 2064)
  status : s.status = .Running
  regInv : NfsRegInv3 b s₀ s
  memInv : NfsMemInv3 b s₀ s.mem
  ist_eq : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes (innerState F key)
  ost_eq : s.mem.readBytes (nfsSp s₀ + 176#64) 32 = shaStateBytes (outerState F key)
  obl_eq : s.mem.read64 (nfsSp s₀ + 208#64) = 1#64

/-! ## Opad XOR Chunks (`hex:67490 → hex:677ac`) and Epilogue (`hex:677b0 → lr`) -/

set_option maxHeartbeats 1600000 in
theorem nfs3_opad_chunk0_ext {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {s₀ s : State} {key : List (BitVec 8)}
    (hs : Nfs3OpadPostHook b F s₀ key s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (Nfs3OpadMidState bv% (ls_off% newFromSlice3Name + 1480) 304#64 305#64 b s₀ s.mem (xorChunk s.mem (nfsSp s₀ + 288#64))) := by
  generalize hPost : (Nfs3OpadMidState _ _ _ _ _ _ _) = Post
  have hpc := hs.pc_eq
  have hstat := hs.status
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hs.regInv
  have hrw : s.mem.RW (nfsSp s₀) 544 := hs.memInv.rw_stack
  iterate 54 nfs3x_step
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
theorem nfs3_opad_chunk1_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {m_init m_cur : Memory}
    (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : Nfs3OpadMidState bv% (ls_off% newFromSlice3Name + 1480) 304#64 305#64 b s₀ m_init m_cur s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (Nfs3OpadMidState bv% (ls_off% newFromSlice3Name + 1672) 320#64 321#64 b s₀ m_init (xorChunk s.mem (nfsSp s₀ + 304#64))) := by
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
  iterate 48 nfs3x_step
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
theorem nfs3_opad_chunk2_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {m_init m_cur : Memory}
    (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : Nfs3OpadMidState bv% (ls_off% newFromSlice3Name + 1672) 320#64 321#64 b s₀ m_init m_cur s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (Nfs3OpadMidState bv% (ls_off% newFromSlice3Name + 1864) 336#64 337#64 b s₀ m_init (xorChunk s.mem (nfsSp s₀ + 320#64))) := by
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
  iterate 48 nfs3x_step
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
theorem nfs3_opad_chunk3_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {s₀ s : State} {m_init m_cur : Memory}
    (hrw_cur : m_cur.RW (nfsSp s₀) 544)
    (hs : Nfs3OpadMidState bv% (ls_off% newFromSlice3Name + 1864) 336#64 337#64 b s₀ m_init m_cur s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
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
  iterate 49 nfs3x_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    by simp only [arm64_norm, hx0], by simp only [arm64_norm, hx1], by simp only [arm64_norm],
    by simp only [xorChunk, Memory.write128, Memory.read128, BitVec.add_assoc, arm64_norm]⟩

theorem nfs3_opad_after_compress1_ext {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {s₀ s1 : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (h1 : Nfs3OpadPostHook b F s₀ key s1) :
    RunsTo (tripleRatchetProgAtExt b ext) s1
      (Nfs3PreCompress2 b F s₀ key) := by
  have hopad_len : ((keyBlock key).map (· ^^^ 0x5c#8)).length = 64 := by
    simp [keyBlock_length hlen]
  have hiv_len : (shaStateBytes sha256IV).length = 32 :=
    shaStateBytes_length sha256IV
  refine (nfs3_opad_chunk0_ext h1).trans fun s2 h2 => ?_
  have hrw1 : (xorChunk s1.mem (nfsSp s₀ + 288#64)).RW (nfsSp s₀) 544 :=
    rw_xorChunk _ h1.memInv.rw_stack
  refine (nfs3_opad_chunk1_ext hrw1 h2).trans fun s3 h3 => ?_
  have hrw2 : (xorChunk s2.mem (nfsSp s₀ + 304#64)).RW (nfsSp s₀) 544 :=
    rw_xorChunk _ (h2.mem_eq ▸ hrw1)
  refine (nfs3_opad_chunk2_ext hrw2 h3).trans fun s4 h4 => ?_
  have hrw3 : (xorChunk s3.mem (nfsSp s₀ + 320#64)).RW (nfsSp s₀) 544 :=
    rw_xorChunk _ (h3.mem_eq ▸ hrw2)
  refine (nfs3_opad_chunk3_ext hrw3 h4).mono fun s5 h5 => ?_
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

set_option maxHeartbeats 1600000 in
theorem nfs3_epilogue_ext {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {s₀ s : State} {key : List (BitVec 8)}
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hs : Nfs3PostCompress2 b F s₀ key s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s' =>
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
  iterate 25 nfs3x_step
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

/-! ## `compress256` #1 and #2 + Second Half (`hex:6748c → lr`) -/

theorem nfs3_bl_compress1_ext {b : BitVec 64} {ext : String → Option (State → State)} {s : State}
    (hpc : s.pc = b + bv% (ls_off% newFromSlice3Name + 1260))
    (hstat : s.status = .Running) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s1 =>
      s1 = (s.writeReg64 .lr (b + bv% (ls_off% newFromSlice3Name + 1264))).setPC (b + bv% (ls_off% "sha2::sha256::compress256"))) := by
  nfs3x_step
  exact RunsTo.refl rfl

theorem nfs3_bl_compress2_ext {b : BitVec 64} {ext : String → Option (State → State)} {s : State}
    (hpc : s.pc = b + bv% (ls_off% newFromSlice3Name + 2060))
    (hstat : s.status = .Running) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s1 =>
      s1 = (s.writeReg64 .lr (b + bv% (ls_off% newFromSlice3Name + 2064))).setPC (b + bv% (ls_off% "sha2::sha256::compress256"))) := by
  nfs3x_step
  exact RunsTo.refl rfl

theorem nfs3_compress1_ext {img : Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hComp : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((spqrCompress256ExternSpec F extHookStack).inImage img))
    {s₀ s : State} {m₀ : Memory} {key : List (BitVec 8)}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384)
    (hd_iv_ext : DisjointRegions (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (nfsSp s₀ - 16384#64) 16384)
    (hrw_extstk : RW s.mem (nfsSp s₀ - 16384#64) 16384)
    (hpc : s.pc = img.base + bv% (ls_off% newFromSlice3Name + 1260))
    (hstat : s.status = .Running)
    (hR : NfsRegInv3 img.base (s₀.setMem m₀) s)
    (hM : NfsMemInv3 img.base (s₀.setMem m₀) s.mem)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hist : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8))
    (hivsw : s.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (fun s' =>
      Nfs3OpadPostHook img.base F (s₀.setMem s'.mem) key s' ∧
      RW s'.mem (nfsSp s₀ - 16384#64) 16384 ∧
      S2Frame s.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)]) := by
  have hbl := RunsToE.of_hmacRunsTo (nfs3_bl_compress1_ext (ext := ext) hpc hstat)
  refine RunsToE.trans_frozen hfrz hsym hbl fun s1 hfrz1 hsym1' hs1 => ?_
  have hmem1 : s1.mem = s.mem := by rw [hs1]; rfl
  have hsp1 : s1.sp = nfsSp s₀ := by rw [hs1]; exact hR.sp_eq
  have hpc1 : s1.pc = img.base + bv% (ls_off% "sha2::sha256::compress256") := by rw [hs1]; rfl
  have hstat1 : s1.status = .Running := by rw [hs1]; exact hstat
  have hx0_1 : s1.readReg64 .x0 = nfsSp s₀ + 400#64 := by rw [hs1]; exact hx0
  have hx1_1 : s1.readReg64 .x1 = nfsSp s₀ + 288#64 := by rw [hs1]; exact hx1
  have hx2_1 : s1.readReg64 .x2 = 1#64 := by rw [hs1]; exact hx2
  have hist1 : s1.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV := by
    rw [hmem1]; exact hist
  have hblk1 : s1.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) := by
    rw [hmem1]; exact hblk
  have hal1 : (s1.sp &&& 15#64) = 0#64 := by rw [hsp1]; exact hR.sp_align
  have hrw_stk : RW s.mem (nfsSp s₀) 544 := hM.rw_stack
  have hrw_st : RW s1.mem (nfsSp s₀ + 400#64) 32 := by
    rw [hmem1]; exact hrw_stk.sub (by clear * -; bv_omega)
  have hrw_blk : RW s1.mem (nfsSp s₀ + 288#64) 64 := by
    rw [hmem1]; exact hrw_stk.sub (by clear * -; bv_omega)
  have hd_st_blk : DisjointRegions (nfsSp s₀ + 400#64) 32 (nfsSp s₀ + 288#64) 64 := by
    clear * -; simp only [DisjointRegions]; bv_omega
  have hd_st_stk : DisjointRegions (nfsSp s₀ + 400#64) 32
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1]
    exact hd_stk_ext.sub_left (nfsSp s₀ + 400#64) ⟨by decide, by clear * -; bv_omega⟩
  have hd_blk_stk : DisjointRegions (nfsSp s₀ + 288#64) 64
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1]
    exact hd_stk_ext.sub_left (nfsSp s₀ + 288#64) ⟨by decide, by clear * -; bv_omega⟩
  have hcomp := compress256_one_subroutine_runsTo hComp (by decide)
    hfrz1 hsym1' hpc1 hstat1 hx0_1 hx1_1 hx2_1 hist1 hblk1
    hrw_st hrw_blk (by rw [hmem1, hsp1]; exact hrw_extstk)
    hd_st_blk hd_st_stk hd_blk_stk hal1
  refine hcomp.mono fun s' ⟨hpc', hstat', hcc, hist', hblk', hfr⟩ => ?_
  have hfr' : S2Frame s.mem s'.mem [(nfsSp s₀ + 400#64, 32),
      (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    rwa [hmem1, hsp1] at hfr
  subst hs1
  refine ⟨{
    pc_eq := hpc'
    status := hstat'
    regInv := NfsRegInv3.setMem_iff.mpr (nfsRegInv3_of_cc (NfsRegInv3.setMem_iff.mp hR) hcc)
    memInv := NfsMemInv3.of_s2Frame_low hM hd_stk_ext hd_iv_ext hfr' ⟨by decide, by decide⟩
    ist_eq := hist'
    blk_eq := hblk'
    ivsw_eq := by
      have h0 : s'.mem.readBytes (nfsSp s₀ + 0#64) 32 = s.mem.readBytes (nfsSp s₀ + 0#64) 32 :=
        s2Frame_hook_readBytes_stack_eq hfr' hrw_stk hd_stk_ext ⟨by decide, by decide⟩ (by decide)
      rw [BitVec.add_zero] at h0
      exact h0.trans hivsw
  }, S2Frame.rw_of_rw hfr' _ _ hrw_extstk, s2Frame_of_hook_frame_16928 hfr' rfl (by decide)⟩

theorem nfs3_compress2_ext {img : Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hComp : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((spqrCompress256ExternSpec F extHookStack).inImage img))
    {s₀ s : State} {m₀ : Memory} {key : List (BitVec 8)}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384)
    (hd_iv_ext : DisjointRegions (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (nfsSp s₀ - 16384#64) 16384)
    (hrw_extstk : RW s.mem (nfsSp s₀ - 16384#64) 16384)
    (hs : Nfs3PreCompress2 img.base F (s₀.setMem m₀) key s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (fun s' =>
      Nfs3PostCompress2 img.base F (s₀.setMem s'.mem) key s' ∧
      S2Frame s.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)]) := by
  have hR := hs.regInv
  have hM := hs.memInv
  have hrw_stk : RW s.mem (nfsSp s₀) 544 := hM.rw_stack
  have hbl := RunsToE.of_hmacRunsTo (nfs3_bl_compress2_ext (ext := ext) hs.pc_eq hs.status)
  refine RunsToE.trans_frozen hfrz hsym hbl fun s1 hfrz1 hsym1' hs1 => ?_
  have hmem1 : s1.mem = s.mem := by rw [hs1]; rfl
  have hsp1 : s1.sp = nfsSp s₀ := by rw [hs1]; exact hR.sp_eq
  have hpc1 : s1.pc = img.base + bv% (ls_off% "sha2::sha256::compress256") := by rw [hs1]; rfl
  have hstat1 : s1.status = .Running := by rw [hs1]; exact hs.status
  have hx0_1 : s1.readReg64 .x0 = nfsSp s₀ + 176#64 := by rw [hs1]; exact hs.x0_eq
  have hx1_1 : s1.readReg64 .x1 = nfsSp s₀ + 288#64 := by rw [hs1]; exact hs.x1_eq
  have hx2_1 : s1.readReg64 .x2 = 1#64 := by rw [hs1]; exact hs.x2_eq
  have host1 : s1.mem.readBytes (nfsSp s₀ + 176#64) 32 = shaStateBytes sha256IV := by
    rw [hmem1]; exact hs.ost_eq
  have hblk1 : s1.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x5c#8) := by
    rw [hmem1]; exact hs.blk_eq
  have hal1 : (s1.sp &&& 15#64) = 0#64 := by rw [hsp1]; exact hR.sp_align
  have hrw_st : RW s1.mem (nfsSp s₀ + 176#64) 32 := by
    rw [hmem1]; exact hrw_stk.sub (by clear * -; bv_omega)
  have hrw_blk : RW s1.mem (nfsSp s₀ + 288#64) 64 := by
    rw [hmem1]; exact hrw_stk.sub (by clear * -; bv_omega)
  have hd_st_blk : DisjointRegions (nfsSp s₀ + 176#64) 32 (nfsSp s₀ + 288#64) 64 := by
    clear * -; simp only [DisjointRegions]; bv_omega
  have hd_st_stk : DisjointRegions (nfsSp s₀ + 176#64) 32
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1]
    exact hd_stk_ext.sub_left (nfsSp s₀ + 176#64) ⟨by decide, by clear * -; bv_omega⟩
  have hd_blk_stk : DisjointRegions (nfsSp s₀ + 288#64) 64
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1]
    exact hd_stk_ext.sub_left (nfsSp s₀ + 288#64) ⟨by decide, by clear * -; bv_omega⟩
  have hcomp := compress256_one_subroutine_runsTo hComp (by decide)
    hfrz1 hsym1' hpc1 hstat1 hx0_1 hx1_1 hx2_1 host1 hblk1
    hrw_st hrw_blk (by rw [hmem1, hsp1]; exact hrw_extstk)
    hd_st_blk hd_st_stk hd_blk_stk hal1
  refine hcomp.mono fun s' ⟨hpc', hstat', hcc, host', hblk', hfr⟩ => ?_
  have hfr' : S2Frame s.mem s'.mem [(nfsSp s₀ + 176#64, 32),
      (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    rwa [hmem1, hsp1] at hfr
  subst hs1
  refine ⟨{
    pc_eq := hpc'
    status := hstat'
    regInv := NfsRegInv3.setMem_iff.mpr (nfsRegInv3_of_cc (NfsRegInv3.setMem_iff.mp hR) hcc)
    memInv := NfsMemInv3.of_s2Frame_low hM hd_stk_ext hd_iv_ext hfr' ⟨by decide, by decide⟩
    ist_eq := (s2Frame_hook_readBytes_stack_eq hfr' hrw_stk hd_stk_ext
      ⟨by decide, by decide⟩ (by decide)).trans hs.ist_eq
    ost_eq := host'
    obl_eq := (s2Frame_hook_read64_stack_eq hfr' hrw_stk hd_stk_ext
      (by decide) (by decide)).trans hs.obl_eq
  }, s2Frame_of_hook_frame_16928 hfr' rfl (by decide)⟩

/-- Second half of `new_from_slice [local#3]` (`hex:6748c → s₀.readReg64 .lr`) on
`tripleRatchetProgAtExt`, shared by both `≤ 64` and `> 64` paths. -/
theorem nfs3_second_half_ext {img : Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hComp : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((spqrCompress256ExternSpec F extHookStack).inImage img))
    {s₀ s3 : State} {m₀ : Memory} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hfrz3 : img.FrozenLoaded s3)
    (hsym3 : s3.symtab = img.symtab)
    (hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384)
    (hd_iv_ext : DisjointRegions (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (nfsSp s₀ - 16384#64) 16384)
    (hrw_extstk3 : RW s3.mem (nfsSp s₀ - 16384#64) 16384)
    (hpc3 : s3.pc = img.base + bv% (ls_off% newFromSlice3Name + 1260))
    (hstat3 : s3.status = .Running)
    (hR3 : NfsRegInv3 img.base (s₀.setMem m₀) s3)
    (hM3 : NfsMemInv3 img.base (s₀.setMem m₀) s3.mem)
    (hx0_3 : s3.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1_3 : s3.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2_3 : s3.readReg64 .x2 = 1#64)
    (hist3 : s3.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk3 : s3.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8))
    (hivsw3 : s3.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s3 (fun sf =>
      sf.pc = s₀.readReg64 .lr ∧
      sf.status = .Running ∧
      CryptoVerification.LibsignalTripleRatchet.CalleeSaved s₀ sf ∧
      sf.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt sf.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      S2Frame m₀ sf.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)]) := by
  have hfr23 : S2Frame m₀ s3.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    s2Frame_of_r7b_frame_16928 hM3.frame
  have hc1 := nfs3_compress1_ext hComp hfrz3 hsym3 hd_stk_ext hd_iv_ext hrw_extstk3
    hpc3 hstat3 hR3 hM3 hx0_3 hx1_3 hx2_3 hist3 hblk3 hivsw3
  refine RunsToE.trans_frozen hfrz3 hsym3 hc1 fun s4 hfrz4 hsym4' ⟨hpost4, hrw_extstk4, hfr34⟩ => ?_
  have hfr24 : S2Frame m₀ s4.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    S2Frame.trans hfr23 hfr34
  have hopad := RunsToE.of_hmacRunsTo (nfs3_opad_after_compress1_ext (ext := ext) hlen hpost4)
  refine RunsToE.trans_frozen hfrz4 hsym4' hopad fun s5 hfrz5 hsym5' hpre5 => ?_
  have hfr45 : S2Frame s4.mem s5.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    s2Frame_of_r7b_frame_16928 hpre5.memInv.frame
  have hfr25 : S2Frame m₀ s5.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    S2Frame.trans hfr24 hfr45
  have hrw_extstk5 : RW s5.mem (nfsSp s₀ - 16384#64) 16384 :=
    (Frame.rw_iff hpre5.memInv.frame _ _).mpr hrw_extstk4
  have hc2 := nfs3_compress2_ext hComp hfrz5 hsym5' hd_stk_ext hd_iv_ext hrw_extstk5 hpre5
  refine RunsToE.trans_frozen hfrz5 hsym5' hc2 fun s6 _ _ ⟨hpost6, hfr56⟩ => ?_
  have hfr26 : S2Frame m₀ s6.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    S2Frame.trans hfr25 hfr56
  have hep := RunsToE.of_hmacRunsTo (nfs3_epilogue_ext (ext := ext) (s₀ := s₀.setMem s6.mem) hal hpost6)
  refine hep.mono fun sf ⟨hpc_sf, hstat_sf, hcs_sf, hret_sf, hhm_sf, hfr6f⟩ => ?_
  exact ⟨hpc_sf, hstat_sf, ⟨hcs_sf.1, hcs_sf.2⟩, hret_sf, hhm_sf,
    S2Frame.trans hfr26 (s2Frame_of_r7b_frame_16928 hfr6f)⟩

/-! ## Full `key.length ≤ 64` Execution (`nfs3_le64_runsToE_ext`) -/

/-- Full `key.length ≤ 64` execution of `new_from_slice [local#3]` under `Nfs3GenPreExt`,
handling both `keyRO = true` and `keyRO = false` via `memcpy_any_subroutine_runsTo`. -/
theorem nfs3_le64_runsToE_ext {img : Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hHooks : SpqrKdfHooksExt img F ext)
    {keyRO : Bool} {roRegs : List (BitVec 64 × ℕ)} {s₀ : State}
    (hpre : Nfs3GenPreExt img keyRO roRegs s₀)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧
      s'.status = .Running ∧
      CryptoVerification.LibsignalTripleRatchet.CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F
        (effectiveHmacKey F (s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)) [] ∧
      S2FrameRO roRegs s₀.mem s'.mem
        [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)]) := by
  set key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
  have hkey_len_eq : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  have hkey_len : key.length ≤ 64 := hkey_len_eq ▸ hlen
  have hrw_stk : RW s₀.mem (s₀.sp - 544#64) 544 :=
    hpre.rw_stk.sub (by clear * -; bv_omega)
  have hrw_extstk : RW s₀.mem (nfsSp s₀ - 16384#64) 16384 :=
    hpre.rw_stk.sub (by clear * -; simp only [nfsSp]; bv_omega)
  have hdisj_out_stk : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544 :=
    hpre.disj_out_stk.sub_right _ ⟨by decide, by clear * -; bv_omega⟩
  have hdisj_iv_stk : DisjointRegions (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (nfsSp s₀) 544 :=
    hpre.disj_iv_stk.sub_right _ ⟨by decide, by clear * -; simp only [nfsSp]; bv_omega⟩
  have hdisj_iv_extstk : DisjointRegions (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 (nfsSp s₀ - 16384#64) 16384 :=
    hpre.disj_iv_stk.sub_right _ ⟨by decide, by clear * -; simp only [nfsSp]; bv_omega⟩
  have hdisj_stk_extstk : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384 := by
    have hd := hpre.disj_iv_stk
    clear * - hd
    simp only [DisjointRegions, nfsSp] at hd ⊢
    bv_omega
  have hdisj_key_stk : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544 := by
    by_cases h0 : (s₀.readReg64 .x2).toNat = 0
    · exact Or.inl h0
    · refine Or.inr (SpqrKdfExt.disjointRegions_of_outside (by omega) (by decide) fun a ha => ?_)
      have hout := hpre.out_key_stk a ha
      clear * - hout
      simp only [OutsideRegion] at hout ⊢
      bv_omega
  have hseg0a := RunsToE.of_hmacRunsTo
    (nfs3_seg0a_ext (ext := ext) hpre.pc_eq hpre.status hlen hpre.base_al hrw_stk hpre.sp_aligned)
  refine RunsToE.trans_frozen hpre.frz hpre.sym hseg0a fun s1 hfrz1 hsym1' h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hsp1, hal1, hx29_1, hx19_1, hx22_1, hx25_1, hx26_1, hx27_1,
    hx0_1, hx1_1, hx2_1, hlr_1, hzero1, hsaved1, hfr1_r7b⟩
  have hfr01 : S2Frame s₀.mem s1.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    s2Frame_of_r7b_stack_frame_16928 hfr1_r7b
  have hrw_stk1 : RW s1.mem (nfsSp s₀) 544 :=
    (Frame.rw_iff hfr1_r7b _ _).mpr hrw_stk
  have hrw_out1 : RW s1.mem (s₀.readReg64 .x0) 0x98 :=
    (Frame.rw_iff hfr1_r7b _ _).mpr hpre.rw_out
  have hrw_extstk1 : RW s1.mem (nfsSp s₀ - 16384#64) 16384 :=
    (Frame.rw_iff hfr1_r7b _ _).mpr hrw_extstk
  have hread_iv1 : s1.mem.Readable (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 :=
    (Frame.readable_iff hfr1_r7b _ _).mpr hpre.ro_iv_read
  have hiv_s1 : s1.mem.readBytes (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 = shaStateBytes sha256IV :=
    (hfr1_r7b.readBytes_eq (by simp [hdisj_iv_stk.symm]) (by decide)).trans hpre.ro_iv_bytes
  have hread_key1 : s1.mem.Readable (s₀.readReg64 .x1) key.length :=
    (Frame.readable_iff hfr1_r7b _ _).mpr (hkey_len_eq ▸ hpre.key_read)
  have hkey_s1 : s1.mem.readBytes (s₀.readReg64 .x1) key.length = key := by
    rw [hkey_len_eq]
    rcases hdisj_key_stk with h0 | hd
    · dsimp only [key]; rw [h0]; rfl
    · have hd' : DisjointRegions (nfsSp s₀) 544 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := hd.symm
      exact hfr1_r7b.readBytes_eq (by simp [hd']) (by omega)
  let roRegs' : List (BitVec 64 × ℕ) :=
    if keyRO then [(s₀.readReg64 .x1, key.length)] else []
  have hsrc_perm1 : if keyRO then s1.mem.Readable (s₀.readReg64 .x1) key.length ∧
      (∀ a, InRegion (s₀.readReg64 .x1) key.length a → ∃ r ∈ roRegs', InRegion r.1 r.2 a)
    else RW s1.mem (s₀.readReg64 .x1) key.length := by
    cases hkr : keyRO
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hkp := hpre.key_perm
      rw [hkr] at hkp
      simp only [Bool.false_eq_true, ↓reduceIte] at hkp
      exact (Frame.rw_iff hfr1_r7b _ _).mpr (hkey_len_eq ▸ hkp)
    · simp only [↓reduceIte, roRegs', hkr]
      exact ⟨hread_key1, fun a ha => ⟨(s₀.readReg64 .x1, key.length), List.Mem.head _, ha⟩⟩
  have hd_dst_stk1 : key.length = 0 ∨ DisjointRegions (nfsSp s₀ + 112#64) key.length
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1]
    refine Or.inr ?_
    clear * - hdisj_stk_extstk hkey_len
    simp only [DisjointRegions, extHookStack] at hdisj_stk_extstk ⊢
    bv_omega
  have hout_src_dst1 : ∀ a, InRegion (s₀.readReg64 .x1) key.length a →
      OutsideRegion (nfsSp s₀ + 112#64) key.length a := by
    intro a ha
    have hout := hpre.out_key_stk a (hkey_len_eq ▸ ha)
    clear * - hout hkey_len
    simp only [OutsideRegion, nfsSp] at hout ⊢
    bv_omega
  have hout_src_stk1 : ∀ a, InRegion (s₀.readReg64 .x1) key.length a →
      OutsideRegion (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack a := by
    rw [hsp1]
    intro a ha
    have hout := hpre.out_key_stk a (hkey_len_eq ▸ ha)
    clear * - hout
    simp only [OutsideRegion, nfsSp, extHookStack] at hout ⊢
    bv_omega
  have hmemcpy1 := memcpy_any_subroutine_runsTo hHooks keyRO roRegs' hfrz1 hsym1' hpc1 hstat1
    hx0_1 hx1_1 (by rw [hx2_1, hkey_len_eq]) hkey_s1
    (hrw_stk1.sub (by clear * - hkey_len; bv_omega)) hsrc_perm1
    (by rw [hsp1]; exact hrw_extstk1)
    hd_dst_stk1 hout_src_dst1 hout_src_stk1 (by rw [hsp1]; exact hal1)
  refine RunsToE.trans_frozen hfrz1 hsym1' hmemcpy1 fun s2 hfrz2 hsym2' ⟨hpc2, hstat2, hcc12, hx0_2, hdst2, _, hfr12⟩ => ?_
  rw [hlr_1] at hpc2
  have hfr12_stk : S2FrameRO roRegs' s1.mem s2.mem
      [(nfsSp s₀ + 112#64, key.length), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    rwa [hsp1] at hfr12
  have hfr02 : S2FrameRO roRegs' s₀.mem s2.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    S2FrameRO.trans (S2FrameRO.of_s2frame hfr01)
      (s2FrameRO_of_hook_frame_16928 hfr12_stk rfl (by clear * - hkey_len; bv_omega))
  have hro'_out_16928 : ∀ r ∈ roRegs', ∀ a, InRegion r.1 r.2 a →
      OutsideRegion (s₀.sp - 16928#64) 16928 a := by
    intro r hr a ha
    cases hkr : keyRO
    · simp [roRegs', hkr] at hr
    · simp only [roRegs', hkr, ↓reduceIte, List.mem_singleton] at hr
      subst hr
      exact hpre.out_key_stk a (hkey_len_eq ▸ ha)
  have hro'_out_out : ∀ r ∈ roRegs', ∀ a, InRegion r.1 r.2 a →
      OutsideRegion (s₀.readReg64 .x0) 0x98 a := by
    intro r hr a ha
    cases hkr : keyRO
    · simp [roRegs', hkr] at hr
    · simp only [roRegs', hkr, ↓reduceIte, List.mem_singleton] at hr
      subst hr
      exact hpre.out_key_out a (hkey_len_eq ▸ ha)
  have hrw_stk2 : RW s2.mem (nfsSp s₀) 544 := by
    refine hfr12_stk.rw_of_rw _ _ (fun r hr a ha => ?_) hrw_stk1
    have hout := hro'_out_16928 r hr a ha
    clear * - hout; simp only [OutsideRegion, nfsSp] at hout ⊢; bv_omega
  have hrw_out2 : RW s2.mem (s₀.readReg64 .x0) 0x98 :=
    hfr12_stk.rw_of_rw _ _ hro'_out_out hrw_out1
  have hrw_extstk2 : RW s2.mem (nfsSp s₀ - 16384#64) 16384 := by
    refine hfr12_stk.rw_of_rw _ _ (fun r hr a ha => ?_) hrw_extstk1
    have hout := hro'_out_16928 r hr a ha
    clear * - hout; simp only [OutsideRegion, nfsSp] at hout ⊢; bv_omega
  have hkb2 : s2.mem.readBytes (nfsSp s₀ + 112#64) 64 = keyBlock key :=
    readBytes_64_eq_keyBlock_of_s2FrameRO hkey_len hrw_stk1 hdisj_stk_extstk hzero1 hdst2 hfr12_stk
  have hsaved2_432 : NfsSavedStack s₀ (s2.mem.write64 (nfsSp s₀ + 432#64) 1#64) :=
    nfsSavedStack_write64_432_of_s2FrameRO hsaved1 hrw_stk1 hdisj_stk_extstk hfr12_stk hkey_len
  have hread_iv2 : s2.mem.Readable (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 :=
    hfr12_stk.readable_of_readable _ _ hread_iv1
  have hiv_eq2 : s2.mem.readBytes (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 = shaStateBytes sha256IV := by
    refine (hfr12_stk.readBytes_eq hread_iv1 (fun r hr => ?_) (by decide)).trans hiv_s1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · clear * - hdisj_iv_stk hkey_len
      simp only [DisjointRegions] at hdisj_iv_stk ⊢
      bv_omega
    · exact hdisj_iv_extstk.symm
  have hA2_432 : AgreesOutside s2.mem (s2.mem.write64 (nfsSp s₀ + 432#64) 1#64) (nfsSp s₀ + 432#64) 8 :=
    AgreesOutside.write64_self s2.mem (nfsSp s₀ + 432#64) 1#64
  have hf2_432 : Frame s2.mem (s2.mem.write64 (nfsSp s₀ + 432#64) 1#64) [(nfsSp s₀ + 432#64, 8)] :=
    agreesOutside_toFrame hA2_432
  have hM2_432 : NfsMemInv3 img.base (s₀.setMem s2.mem) (s2.mem.write64 (nfsSp s₀ + 432#64) 1#64) := {
    rw_stack := (Frame.rw_iff hf2_432 _ _).mpr hrw_stk2
    rw_out := (Frame.rw_iff hf2_432 _ _).mpr hrw_out2
    readable_iv := (Frame.readable_iff hf2_432 _ _).mpr hread_iv2
    iv_bytes := by
      have hd432 : DisjointRegions (nfsSp s₀ + 432#64) 8
          (img.base + bv% (ls_xref% (ls_off% newFromSlice3Name + 40) (ls_off% newFromSlice3Name + 44))) 32 := by
        clear * - hdisj_iv_stk; simp only [DisjointRegions, nfsSp] at hdisj_iv_stk ⊢; bv_omega
      exact (hf2_432.readBytes_eq (by simp [hd432]) (by decide)).trans hiv_eq2
    disj_iv_stack := hdisj_iv_stk
    disj_out_stack := hdisj_out_stk
    saved := nfsSavedStack_setMem_iff.mpr hsaved2_432
    frame := Frame.of_agreesOutside_stack (Frame.refl s2.mem _) hA2_432 (by decide)
  }
  have hto_c1 := RunsToE.of_hmacRunsTo
    (nfs3_after_memcpy_to_compress1_ext (ext := ext) hkey_len hpre.sp_aligned hpre.base_al hpc2 hstat2
      (hcc12.1.trans hsp1) hal1
      (hcc12.2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1)
      (hcc12.2.1.trans hx19_1)
      (hcc12.2.2.2.2.1.trans hx22_1)
      (hcc12.2.2.2.2.2.2.2.1.trans hx25_1)
      (hcc12.2.2.2.2.2.2.2.2.1.trans hx26_1)
      (hcc12.2.2.2.2.2.2.2.2.2.1.trans hx27_1)
      hM2_432 hkb2)
  refine RunsToE.trans_frozen hfrz2 hsym2' hto_c1 fun s3 hfrz3 hsym3'
      ⟨hpc3, hstat3, hR3, hM3, hx0_3, hx1_3, hx2_3, hist3, hblk3, hivsw3⟩ => ?_
  have hrw_extstk3 : RW s3.mem (nfsSp s₀ - 16384#64) 16384 :=
    (Frame.rw_iff hM3.frame _ _).mpr hrw_extstk2
  refine (nfs3_second_half_ext hHooks.compress256 hkey_len hpre.sp_aligned hfrz3 hsym3'
    hdisj_stk_extstk hdisj_iv_extstk hrw_extstk3 hpc3 hstat3 hR3 hM3
    hx0_3 hx1_3 hx2_3 hist3 hblk3 hivsw3).mono fun sf hsf => ?_
  rcases hsf with ⟨hpc_sf, hstat_sf, hcs_sf, hret_sf, hhm_sf, hfr2f⟩
  have hfr0f' : S2FrameRO roRegs' s₀.mem sf.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    S2FrameRO.trans hfr02 (S2FrameRO.of_s2frame hfr2f)
  have hfr0f : S2FrameRO roRegs s₀.mem sf.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] := by
    refine hfr0f'.mono_ro fun a hout ro hro_mem => ?_
    cases hkr : keyRO
    · simp [roRegs', hkr] at hro_mem
    · simp only [roRegs', hkr, ↓reduceIte, List.mem_singleton] at hro_mem
      subst hro_mem
      rw [outsideRegion_iff_not_inRegion]
      intro hin
      have hkp := hpre.key_perm
      rw [hkr] at hkp
      simp only [↓reduceIte] at hkp
      obtain ⟨r, hr_mem, hin_r⟩ := hkp.2 a (hkey_len_eq ▸ hin)
      exact (outsideRegion_iff_not_inRegion r.1 r.2 a).mp (hout r hr_mem) hin_r
  rw [effectiveHmacKey_of_le F hkey_len]
  exact ⟨hpc_sf, hstat_sf, hcs_sf, hret_sf, hhm_sf, hfr0f⟩

end CryptoVerification.SpqrV1.Kdf.Nfs3Ext
