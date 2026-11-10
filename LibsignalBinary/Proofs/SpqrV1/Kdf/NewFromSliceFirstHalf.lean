/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.KdfCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed

/-!
# `Hmac<Sha256>::new_from_slice [local#3]`: First Half

Symbolic execution of the `key.length ≤ 64` prologue, key copy, and ipad XOR chunks
(`0x66fa0 → 0x6748c`, fixed-base and Block `402` `[LibsignalPlacement]`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.CBC
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
open ProofLib.ProgramReflection
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Kdf

set_option maxRecDepth 2000000
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
gen_decodes libsignalSessionCode_tree libsignalSessionCode [0x61ba8 → 0x62098]

macro (priority := high) "sess_step" : tactic =>
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

@[scoped simp, arm64_norm]
theorem adrp_421832_mask : (421832#64 &&& 18446744073709547520#64 : BitVec 64) = 417792#64 := rfl

theorem nfs3_adrp_x22_0x66fc8 {b : BitVec 64} (hb : (b &&& 0xfff#64) = 0#64) :
    ((b + 0x61bd0#64) &&& 0xfffffffffffff000#64) + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64 - 0x61000) = b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64) := by
  bv_bits

theorem nfs3_adrp_x22_0x66fc8_assoc {b : BitVec 64} (hb : (b &&& 0xfff#64) = 0#64) :
    (((b + 0x61bd0#64) &&& 0xfffffffffffff000#64) + bv% (page% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64) - 0x61000)) + bv% ((ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64) % 4096) = b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64) := by
  bv_bits

/-- Common memory invariant across Chunks 1..8 of `new_from_slice`. -/
structure NfsMemInv3 (b : BitVec 64) (s₀ : State) (m : Memory) : Prop where
  rw_stack : m.RW (nfsSp s₀) 544
  rw_out : m.RW (s₀.readReg64 .x0) 0x98
  readable_iv : m.Readable (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32
  iv_bytes : m.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV
  disj_iv_stack : DisjointRegions (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (nfsSp s₀) 544
  disj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (nfsSp s₀) 544
  saved : NfsSavedStack s₀ m
  frame : Frame s₀.mem m [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)]

/-- Common register invariant across Chunks 1..8 of `new_from_slice`. -/
structure NfsRegInv3 (b : BitVec 64) (s₀ s : State) : Prop where
  sp_eq : s.sp = nfsSp s₀
  sp_align : (nfsSp s₀ &&& 0b1111#64) = 0#64
  x29_eq : s.readReg64 .x29 = nfsSp s₀ + 464#64
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq : s.readReg64 .x20 = 1#64
  x22_eq : s.readReg64 .x22 = b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)
  x25_eq : s.readReg64 .x25 = s₀.readReg64 .x25
  x26_eq : s.readReg64 .x26 = s₀.readReg64 .x26
  x27_eq : s.readReg64 .x27 = s₀.readReg64 .x27

theorem NfsMemInv3.of_agreesOutside_low {b : BitVec 64} {s₀ : State} {m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hM : NfsMemInv3 b s₀ m)
    (hA : AgreesOutside m m' (nfsSp s₀ + off) sz)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ 432) :
    NfsMemInv3 b s₀ m' := by
  have hf := agreesOutside_toFrame hA
  have hdisj_iv : DisjointRegions (nfsSp s₀ + off) sz (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
    refine hM.disj_iv_stack.symm.sub_left (nfsSp s₀ + off) ⟨hoff.1, ?_⟩
    rcases hoff with ⟨_, _⟩
    bv_omega
  exact {
    rw_stack := (Frame.rw_iff hf _ _).mpr hM.rw_stack
    rw_out := (Frame.rw_iff hf _ _).mpr hM.rw_out
    readable_iv := (Frame.readable_iff hf _ _).mpr hM.readable_iv
    iv_bytes := (Frame.readBytes_eq hf (by simp [hdisj_iv]) (by decide)).trans hM.iv_bytes
    disj_iv_stack := hM.disj_iv_stack
    disj_out_stack := hM.disj_out_stack
    saved := hM.saved.of_agreesOutside_low hA hoff
    frame := Frame.of_agreesOutside_stack hM.frame hA (by omega)
  }

theorem NfsMemInv3.writeBytes_low {b : BitVec 64} {s₀ : State} {m : Memory}
    (hM : NfsMemInv3 b s₀ m) (off : BitVec 64) (bs : List (BitVec 8))
    (hoff : 0 < bs.length ∧ off.toNat + bs.length ≤ 432) :
    NfsMemInv3 b s₀ (m.writeBytes (nfsSp s₀ + off) bs) :=
  hM.of_agreesOutside_low (ProofLib.agreesOutside_writeBytes m (nfsSp s₀ + off) bs) hoff

theorem NfsMemInv3.write64_low {b : BitVec 64} {s₀ : State} {m : Memory}
    (hM : NfsMemInv3 b s₀ m) (off : BitVec 64) (v : BitVec 64)
    (hoff : off.toNat + 8 ≤ 432 := by decide) :
    NfsMemInv3 b s₀ (m.write64 (nfsSp s₀ + off) v) :=
  hM.of_agreesOutside_low (AgreesOutside.write64_self m (nfsSp s₀ + off) v) ⟨by decide, hoff⟩

theorem NfsMemInv3.write128_low {b : BitVec 64} {s₀ : State} {m : Memory}
    (hM : NfsMemInv3 b s₀ m) (off : BitVec 64) (v : BitVec 128)
    (hoff : off.toNat + 16 ≤ 432 := by decide) :
    NfsMemInv3 b s₀ (m.write128 (nfsSp s₀ + off) v) :=
  hM.of_agreesOutside_low (AgreesOutside.write128_self m (nfsSp s₀ + off) v) ⟨by decide, hoff⟩

/-! ## Segment 0 (`0x66fa0 → 0x6717c`, 28 steps) and Chunk 1 (`0x6717c → 0x67244`, 50 steps) -/

set_option maxHeartbeats 3200000 in
theorem nfs_seg0 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
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
      s'.pc = b + 0x61d84#64 ∧
      s'.status = .Running ∧
      NfsRegInv3 b s₀ s' ∧
      NfsMemInv3 b s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readVReg128 2#5 = s'.mem.read64 (nfsSp s₀ + 152#64) ++ s'.mem.read64 (nfsSp s₀ + 144#64) ∧
      s'.readVReg128 0#5 = s'.mem.read64 (nfsSp s₀ + 168#64) ++ s'.mem.read64 (nfsSp s₀ + 160#64) ∧
      s'.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  intro key
  generalize hPost : (fun s' : State => _) = Post
  have hkey_len : key.length ≤ 64 := by
    dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hkey_len
  have hsp₀ : s₀.sp = nfsSp s₀ + 544#64 := nfs_sp_eq_add s₀
  have hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64 := nfs_sp_align hal
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hRW_stack : s₀.mem.RW (nfsSp s₀) 544 := hrw_stack
  have hcond : BitVec.ule 0x41#64 (s₀.readReg64 .x2) = false := nfs_ule_65_false hlen
  have hadrp1 := nfs3_adrp_x22_0x66fc8_assoc hb
  have hadrp2 := nfs3_adrp_x22_0x66fc8 hb
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  have hA_pro : AgreesOutside s₀.mem (nfsPrologueMem s₀) (nfsSp s₀ + 464#64) 80 :=
    agreesOutside_nfsPrologueMem s₀
  have hA_zero : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8))
      (nfsSp s₀ + 112#64) 64 := by
    simpa using ProofLib.agreesOutside_writeBytes (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (List.replicate 64 0#8)
  have hread_key : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).readBytes
      (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key := by
    rcases hdisj_key_stack with h0 | hdisj_key_stack
    · simp only [key, h0, Memory.readBytes]
    have hdisj_key_pro : DisjointRegions (nfsSp s₀ + 464#64) 80 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack
      simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢
      bv_omega
    have hdisj_key_112 : DisjointRegions (nfsSp s₀ + 112#64) 64 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack
      simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢
      bv_omega
    rw [(agreesOutside_toFrame hA_zero).readBytes_eq (by simp [hdisj_key_112]) (by omega),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdisj_key_pro]) (by omega)]
  have hrw_memcpy : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW
      (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat := by
    have hrw0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW (nfsSp s₀) 544 :=
      (Frame.rw_iff (agreesOutside_toFrame hA_zero) _ _).mpr
        ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
    exact hrw0.sub (by clear * - hlen; bv_omega)
  refine RunsTo.sess_memcpy_step
    (hrun := by simp only [arm64_norm, hstat])
    (hpc := rfl)
    (hx0 := by simp only [arm64_norm])
    (hx1 := by simp only [arm64_norm])
    (hx2 := by simp only [arm64_norm])
    (hlr := by simp only [arm64_norm]; rfl)
    (hmem := write64_oct_zero_eq_writeBytes_64 (nfsPrologueMem s₀) (nfsSp s₀))
    (hread := hread_key)
    (hrw := hrw_memcpy)
    ?_
  rw [writeBytes_key_over_zero64]
  have hA_k0 : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)) (nfsSp s₀ + 112#64) 64 := by
    have h := ProofLib.agreesOutside_writeBytes (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key)
    rwa [hkb_len] at h
  have hRW_k0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hA_k0) _ _).mpr
      ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost
  refine RunsTo.refl ?_
  set m_k0 := (nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)
  have hk0_64 : m_k0.readBytes (nfsSp s₀ + 112#64) 64 = keyBlock key :=
    Layout.readBytes_writeBytes_eq (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key) 64 hkb_len (by decide)
  have hk0_take32 : m_k0.readBytes (nfsSp s₀ + 112#64) 32 = (keyBlock key).take 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 0 32 (by omega)
    simpa using h
  have hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 32 32 (by omega)
    have hadd : (nfsSp s₀ + 112#64) + BitVec.ofNat 64 32 = nfsSp s₀ + 144#64 := by clear * -; bv_omega
    rw [hadd, List.take_of_length_le (by simp [hkb_len])] at h
    exact h
  have hA_432 : AgreesOutside m_k0 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) (nfsSp s₀ + 432#64) 8 :=
    AgreesOutside.write64_self m_k0 (nfsSp s₀ + 432#64) 1#64
  have hf_k0 : Frame s₀.mem (m_k0.write64 (nfsSp s₀ + 432#64) 1#64)
      [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := by
    have hf0 : Frame s₀.mem s₀.mem [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := Frame.refl _ _
    have hf1 := Frame.of_agreesOutside_stack hf0 hA_pro (by decide)
    have hf2 := Frame.of_agreesOutside_stack hf1 hA_k0 (by decide)
    exact Frame.of_agreesOutside_stack hf2 hA_432 (by decide)
  have hM_432 : NfsMemInv3 b s₀ (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) := {
    rw_stack := (Frame.rw_iff hf_k0 _ _).mpr hrw_stack
    rw_out := (Frame.rw_iff hf_k0 _ _).mpr hrw_out
    readable_iv := (Frame.readable_iff hf_k0 _ _).mpr hread_iv
    iv_bytes := by
      have hd432 : DisjointRegions (nfsSp s₀ + 432#64) 8 (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdk0 : DisjointRegions (nfsSp s₀ + 112#64) 64 (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdpro : DisjointRegions (nfsSp s₀ + 464#64) 80 (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      rw [(agreesOutside_toFrame hA_432).readBytes_eq (by simp [hd432]) (by decide),
          (agreesOutside_toFrame hA_k0).readBytes_eq (by simp [hdk0]) (by decide),
          (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdpro]) (by decide), hiv]
    disj_iv_stack := hdisj_iv_stack
    disj_out_stack := hdisj_out_stack
    saved := nfsSavedStack_prologue_432 s₀ m_k0 hA_k0
    frame := hf_k0
  }
  have hM_final : NfsMemInv3 b s₀
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)) :=
    (hM_432.writeBytes_low 288#64 _ (by simp [slice16_length])).writeBytes_low
      304#64 _ (by simp [slice16_length])
  have h144_eq :
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)).readBytes (nfsSp s₀ + 144#64) 32 =
      (keyBlock key).drop 32 := by
    rw [readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        (agreesOutside_toFrame hA_432).readBytes_eq
          (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
        hk0_drop32]
  refine ⟨by simp only [arm64_norm], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm], hal_nfs, by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩,
    ?_,
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact hM_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact h144_eq
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)

set_option hygiene false in
local macro "nfs3_chunk1_body" : tactic => `(tactic| (
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
          hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 288#64 (keyBlock key) 0 hs0
  obtain ⟨hb16, hb17, -⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 304#64 (keyBlock key) 16 hs16
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14 hb15 hb16 hb17
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm, hx8], by simp only [arm64_norm, hx0],
    by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx2],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_288_xor _ _ _ _ (keyBlock_length hlen)]
    exact hM.writeBytes_low 288#64 _ (by simp [slice16_length])
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_288_xor _ _ _ _ (keyBlock_length hlen)]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_288_xor _ _ _ _ (keyBlock_length hlen)]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs16))

set_option maxHeartbeats 1600000 in
theorem nfs_chunk1 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hpc : s.pc = b + 0x61d84#64)
    (hstat : s.status = .Running)
    (hR : NfsRegInv3 b s₀ s)
    (hM : NfsMemInv3 b s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) :
    RunsTo (P b F alloc) s (fun s' =>
      s'.pc = b + 0x61e4c#64 ∧
      s'.status = .Running ∧
      NfsRegInv3 b s₀ s' ∧
      NfsMemInv3 b s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readReg64 .x10 = (byteAt (keyBlock key) 16).zeroExtend 64 ∧
      s'.readReg64 .x11 = (byteAt (keyBlock key) 17).zeroExtend 64 ∧
      s'.readVReg128 2#5 = s.readVReg128 2#5 ∧
      s'.readVReg128 0#5 = s.readVReg128 0#5 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  nfs3_chunk1_body

@[scoped simp, arm64_norm]
theorem read64_write8_stack_iv {b : BitVec 64} {s₀ : State}
    (hdisj : DisjointRegions (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (nfsSp s₀) 544)
    (m : Memory) (off c : BitVec 64) (v : BitVec 8)
    (hc : decide (c.toNat < 544) = true)
    (hoff : decide (num% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64) ≤ off.toNat ∧ off.toNat + 8 ≤ num% (ls_str% "Signal_PQCKA_V1_MLKEM768:ekheader")) = true) :
    (m.write8 (nfsSp s₀ + c) v).read64 (b + off) = m.read64 (b + off) := by
  have hc' : c.toNat < 544 := of_decide_eq_true hc
  have ⟨hoff1, hoff2⟩ : num% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64) ≤ off.toNat ∧ off.toNat + 8 ≤ num% (ls_str% "Signal_PQCKA_V1_MLKEM768:ekheader") := of_decide_eq_true hoff
  refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write8_self m (nfsSp s₀ + c) v)) ?_
  clear * - hdisj hc' hoff1 hoff2
  simp only [List.mem_singleton, forall_eq, DisjointRegions] at hdisj ⊢
  bv_omega

theorem write64_quad_400_iv (b : BitVec 64) (m₁ m₂ : Memory) (sp : BitVec 64)
    (hiv : m₂.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV) :
    ((((m₁.write64 (sp + 400#64) (m₂.read64 (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)))).write64
      (sp + 408#64) (m₂.read64 (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 72)))).write64
      (sp + 416#64) (m₂.read64 (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 80)))).write64
      (sp + 424#64) (m₂.read64 (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 88)))) =
    m₁.writeBytes (sp + 400#64) (shaStateBytes sha256IV) := by
  have hd1 : sp + 408#64 = (sp + 400#64) + 8#64 := by bv_omega
  have hd2 : sp + 416#64 = (sp + 400#64) + 16#64 := by bv_omega
  have hd3 : sp + 424#64 = (sp + 400#64) + 24#64 := by bv_omega
  have hs1 : b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 72) = (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) + 8#64 := by bv_omega
  have hs2 : b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 80) = (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) + 16#64 := by bv_omega
  have hs3 : b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 88) = (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) + 24#64 := by bv_omega
  rw [hd1, hd2, hd3, hs1, hs2, hs3, write64_quad_read64_eq_writeBytes_32, hiv]

theorem write64_quad_0_ivsw (b : BitVec 64) (m₁ m₂ : Memory) (sp : BitVec 64)
    (hiv : m₂.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV) :
    ((((m₁.write64 sp (m₂.read64 (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 80)))).write64
      (sp + 8#64) (m₂.read64 (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 88)))).write64
      (sp + 16#64) (m₂.read64 (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)))).write64
      (sp + 24#64) (m₂.read64 (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 72)))) =
    m₁.writeBytes sp ((shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  have hd3 : sp + 24#64 = (sp + 16#64) + 8#64 := by bv_omega
  have hs1 : b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 88) = (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 80)) + 8#64 := by bv_omega
  have hs2 : b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 72) = (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) + 8#64 := by bv_omega
  have hlen : (shaStateBytes sha256IV).length = 32 := shaStateBytes_length sha256IV
  have htake : m₂.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 16 = (shaStateBytes sha256IV).take 16 := by
    have h := readBytes_slice_of_readBytes_eq m₂ (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) (shaStateBytes sha256IV)
      (by rw [hlen]; exact hiv) 0 16 (by omega)
    simpa using h
  have hdrop : m₂.readBytes (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 80)) 16 = (shaStateBytes sha256IV).drop 16 := by
    have h := readBytes_slice_of_readBytes_eq m₂ (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) (shaStateBytes sha256IV)
      (by rw [hlen]; exact hiv) 16 16 (by omega)
    have hadd : (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) + BitVec.ofNat 64 16 = b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 80) := by bv_omega
    rw [hadd, List.take_of_length_le (by simp [hlen])] at h
    exact h
  rw [hd3, hs1, hs2, write64_pair_read64_eq_writeBytes_16, write64_pair_read64_eq_writeBytes_16,
      hdrop, htake, writeBytes_append]
  have hlen_drop : ((shaStateBytes sha256IV).drop 16).length = 16 := by simp [hlen]
  rw [hlen_drop]

theorem writeBytes_ivsw_write8_351_comm (m : Memory) (sp : BitVec 64) (v : BitVec 8) :
    (m.writeBytes sp ((shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16)).write8
      (sp + 351#64) v =
    (m.write8 (sp + 351#64) v).writeBytes
      sp ((shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  refine ProofLib.write8_writeBytes_comm m (sp + 351#64) v sp _ ?_
  have hlen : ((shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16).length = 32 := by
    simp [shaStateBytes_length]
  rw [hlen]
  clear * -
  simp only [OutsideRegion]
  bv_omega

theorem NfsMemInv3.writeBytes_zero {b : BitVec 64} {s₀ : State} {m : Memory}
    (hM : NfsMemInv3 b s₀ m) (bs : List (BitVec 8))
    (hbs : 0 < bs.length ∧ bs.length ≤ 432) :
    NfsMemInv3 b s₀ (m.writeBytes (nfsSp s₀) bs) := by
  rw [← BitVec.add_zero (nfsSp s₀)]
  exact hM.writeBytes_low 0#64 bs (by simpa using hbs)

theorem readBytes_16_writeBytes_0_400 (m : Memory) (sp off : BitVec 64)
    (bs0 bs400 : List (BitVec 8)) (h0 : bs0.length = 32) (h400 : bs400.length = 32)
    (hoff : 32 ≤ off.toNat ∧ off.toNat + 16 ≤ 400 := by decide) :
    ((m.writeBytes sp bs0).writeBytes (sp + 400#64) bs400).readBytes (sp + off) 16 =
      m.readBytes (sp + off) 16 := by
  rcases hoff with ⟨h1, h2⟩
  rw [Layout.readBytes_writeBytes_of_disjoint _ (sp + 400#64) bs400 (sp + off) 16
        (by rw [h400]; clear * - h1 h2; simp only [DisjointRegions]; bv_omega) (by decide),
      Layout.readBytes_writeBytes_of_disjoint m sp bs0 (sp + off) 16
        (by rw [h0]; clear * - h1 h2; simp only [DisjointRegions]; bv_omega) (by decide)]

theorem readBytes_64_of_four_slice16 (m : Memory) (sp : BitVec 64) (l : List (BitVec 8))
    (hl : l.length = 64)
    (h0 : m.readBytes (sp + 288#64) 16 = slice16 l 0)
    (h16 : m.readBytes (sp + 304#64) 16 = slice16 l 16)
    (h32 : m.readBytes (sp + 320#64) 16 = slice16 l 32)
    (h48 : m.readBytes (sp + 336#64) 16 = slice16 l 48) :
    m.readBytes (sp + 288#64) 64 = l := by
  have ha1 : (sp + 288#64) + BitVec.ofNat 64 32 = sp + 320#64 := by clear * -; bv_omega
  have ha2 : (sp + 288#64) + BitVec.ofNat 64 16 = sp + 304#64 := by clear * -; bv_omega
  have ha3 : (sp + 320#64) + BitVec.ofNat 64 16 = sp + 336#64 := by clear * -; bv_omega
  rw [LibsignalAesCbc.Run.Bytes.readBytes_add m (sp + 288#64) 32 32, ha1,
      LibsignalAesCbc.Run.Bytes.readBytes_add m (sp + 288#64) 16 16, ha2,
      LibsignalAesCbc.Run.Bytes.readBytes_add m (sp + 320#64) 16 16, ha3,
      h0, h16, h32, h48,
      ← slice16_0_16_eq_take_32 l hl, ← slice16_32_48_eq_drop_32 l hl,
      List.take_append_drop]

set_option hygiene false in
local macro "nfs3_chunk2_body" : tactic => `(tactic| (
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hlen
  obtain ⟨hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23,
          hb24, hb25, hb26, hb27, hb28, hb29, hb30, hb31⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 304#64 (keyBlock key) 16 hs16
  obtain ⟨hb32, hb33, -⟩ :=
    read8_16_of_readBytes_slice16 m_k0 (nfsSp s₀) 144#64 (keyBlock key) 32
      (readBytes_16_of_drop_32 m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32)
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb16 hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb24 hb25 hb26 hb27 hb28 hb29 hb30 hb31 hb32 hb33
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost
  refine RunsTo.refl ?_
  have hM_final : NfsMemInv3 _ s₀
      (((s.mem.writeBytes (nfsSp s₀ + 304#64) (slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16)).writeBytes
        (nfsSp s₀ + 320#64) (slice16 (keyBlock key) 32)).writeBytes
        (nfsSp s₀ + 336#64) (slice16 (keyBlock key) 48)) :=
    (((hM.writeBytes_low 304#64 _ (by simp [slice16_length])).writeBytes_low
      320#64 _ (by simp [slice16_length])).writeBytes_low
      336#64 _ (by simp [slice16_length]))
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm, hx8], by simp only [arm64_norm, hx0],
    by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx2],
    by simp only [arm64_norm], by simp only [arm64_norm],
    ?_, ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact hM_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      ((readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
        ((readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs0))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      ((readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
        (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_320_eq_writeBytes_slice16 _ m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_drop32]
    simp (config := { decide := true }) only [writeBytes_slice16_write8_comm]
    rw [write8_16_stack_304_xor _ _ _ _ hkb_len]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)))

set_option maxHeartbeats 1600000 in
theorem nfs_chunk2 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ s : State} {m_k0 : Memory}
    {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hpc : s.pc = b + 0x61e4c#64)
    (hstat : s.status = .Running)
    (hR : NfsRegInv3 b s₀ s)
    (hM : NfsMemInv3 b s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx10 : s.readReg64 .x10 = (byteAt (keyBlock key) 16).zeroExtend 64)
    (hx11 : s.readReg64 .x11 = (byteAt (keyBlock key) 17).zeroExtend 64)
    (hq2 : s.readVReg128 2#5 = m_k0.read64 (nfsSp s₀ + 152#64) ++ m_k0.read64 (nfsSp s₀ + 144#64))
    (hq0 : s.readVReg128 0#5 = m_k0.read64 (nfsSp s₀ + 168#64) ++ m_k0.read64 (nfsSp s₀ + 160#64))
    (hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) :
    RunsTo (P b F alloc) s (fun s' =>
      s'.pc = b + 0x61f14#64 ∧
      s'.status = .Running ∧
      NfsRegInv3 b s₀ s' ∧
      NfsMemInv3 b s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readReg64 .x11 = (byteAt (keyBlock key) 32 ^^^ 0x36#8).zeroExtend 64 ∧
      s'.readReg64 .x9 = (byteAt (keyBlock key) 33).zeroExtend 64 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16 ∧
      s'.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 (keyBlock key) 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) := by
  nfs3_chunk2_body

set_option hygiene false in
local macro "nfs3_chunk3_body" : tactic => `(tactic| (
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hlen
  obtain ⟨-, -, hb34, hb35, hb36, hb37, hb38, hb39,
          hb40, hb41, hb42, hb43, hb44, hb45, hb46, hb47⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 320#64 (keyBlock key) 32 hs32
  obtain ⟨hb48, hb49, -⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 336#64 (keyBlock key) 48 hs48
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb34 hb35 hb36 hb37 hb38 hb39 hb40 hb41 hb42 hb43 hb44 hb45 hb46 hb47 hb48 hb49
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
     by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩,
    ?_,
    by simp only [arm64_norm, hx8], by simp only [arm64_norm, hx0],
    by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx2],
    by simp only [arm64_norm], by simp only [arm64_norm],
    ?_, ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact hM.writeBytes_low 320#64 _ (by simp [slice16_length])
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs0
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs16
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write8_16_stack_320_xor _ _ _ _ hkb_len]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs48))

set_option maxHeartbeats 1600000 in
theorem nfs_chunk3 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hpc : s.pc = b + 0x61f14#64)
    (hstat : s.status = .Running)
    (hR : NfsRegInv3 b s₀ s)
    (hM : NfsMemInv3 b s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx11 : s.readReg64 .x11 = (byteAt (keyBlock key) 32 ^^^ 0x36#8).zeroExtend 64)
    (hx9 : s.readReg64 .x9 = (byteAt (keyBlock key) 33).zeroExtend 64)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16)
    (hs32 : s.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 (keyBlock key) 32)
    (hs48 : s.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) :
    RunsTo (P b F alloc) s (fun s' =>
      s'.pc = b + 0x61fd4#64 ∧
      s'.status = .Running ∧
      NfsRegInv3 b s₀ s' ∧
      NfsMemInv3 b s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readReg64 .x9 = (byteAt (keyBlock key) 48 ^^^ 0x36#8).zeroExtend 64 ∧
      s'.readReg64 .x10 = (byteAt (keyBlock key) 49).zeroExtend 64 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16 ∧
      s'.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) := by
  nfs3_chunk3_body

set_option hygiene false in
local macro "nfs3_chunk4_mid " bTerm:term:max : tactic => `(tactic| (
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost; refine RunsTo.refl ?_
  set ivsw := (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16
  set iv := shaStateBytes sha256IV
  have hivsw_len : ivsw.length = 32 := by simp [ivsw, shaStateBytes_length]
  have hiv_len : iv.length = 32 := shaStateBytes_length sha256IV
  set m_xor := s.mem.writeBytes (nfsSp s₀ + 336#64) (slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 48)
  set m_final := (m_xor.writeBytes (nfsSp s₀) ivsw).writeBytes (nfsSp s₀ + 400#64) iv
  have hM_final : NfsMemInv3 $bTerm s₀ m_final :=
    ((hM.writeBytes_low 336#64 _ (by simp [slice16_length])).writeBytes_zero ivsw (by simp [hivsw_len])).writeBytes_low 400#64 iv (by simp [hiv_len])
  have hist_final : m_final.readBytes (nfsSp s₀ + 400#64) 32 = iv := Layout.readBytes_writeBytes_eq _ (nfsSp s₀ + 400#64) iv 32 hiv_len (by decide)
  have hivsw_final : m_final.readBytes (nfsSp s₀) 32 = ivsw := by
    rw [Layout.readBytes_writeBytes_of_disjoint _ (nfsSp s₀ + 400#64) iv (nfsSp s₀) 32
          (by rw [hiv_len]; clear * -; simp only [DisjointRegions]; bv_omega) (by decide),
        Layout.readBytes_writeBytes_eq m_xor (nfsSp s₀) ivsw 32 hivsw_len (by decide)]
  have hblk_final : m_final.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) := by
    refine readBytes_64_of_four_slice16 m_final (nfsSp s₀) ((keyBlock key).map (· ^^^ 0x36#8)) (by simp [hkb_len]) ?_ ?_ ?_ ?_
    · rw [readBytes_16_writeBytes_0_400 m_xor (nfsSp s₀) 288#64 ivsw iv hivsw_len hiv_len]
      exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs0
    · rw [readBytes_16_writeBytes_0_400 m_xor (nfsSp s₀) 304#64 ivsw iv hivsw_len hiv_len]
      exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs16
    · rw [readBytes_16_writeBytes_0_400 m_xor (nfsSp s₀) 320#64 ivsw iv hivsw_len hiv_len]
      exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans hs32
    · rw [readBytes_16_writeBytes_0_400 m_xor (nfsSp s₀) 336#64 ivsw iv hivsw_len hiv_len]
      exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)
  refine ⟨by simp only [arm64_norm, hpc], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29], by simp only [arm64_norm, hx19],
     by simp only [arm64_norm, hx20], by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩, ?_,
    by simp only [arm64_norm, hx0], by simp only [arm64_norm, hx1], by simp only [arm64_norm, hx2], ?_, ?_, ?_⟩))

set_option maxHeartbeats 1600000 in
theorem nfs_chunk4 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64) (hal : (s₀.sp &&& 0b1111#64) = 0#64) (hb : (b &&& 0xfff#64) = 0#64)
    (hpc : s.pc = b + 0x61fd4#64) (hstat : s.status = .Running)
    (hR : NfsRegInv3 b s₀ s) (hM : NfsMemInv3 b s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64) (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64) (hx2 : s.readReg64 .x2 = 1#64)
    (hx9 : s.readReg64 .x9 = (byteAt (keyBlock key) 48 ^^^ 0x36#8).zeroExtend 64)
    (hx10 : s.readReg64 .x10 = (byteAt (keyBlock key) 49).zeroExtend 64)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16)
    (hs32 : s.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 32)
    (hs48 : s.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) :
    RunsTo (P b F alloc) s (fun s' =>
      s'.pc = b + 0x62094#64 ∧ s'.status = .Running ∧
      NfsRegInv3 b s₀ s' ∧ NfsMemInv3 b s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧ s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 = (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  have hread_iv : s.mem.Readable (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := hM.readable_iv
  have hdisj_iv : DisjointRegions (b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (nfsSp s₀) 544 := hM.disj_iv_stack
  have hread_iv_eq := read64_write8_stack_iv hM.disj_iv_stack
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hlen
  obtain ⟨-, -, hb50, hb51, hb52, hb53, hb54, hb55, hb56, hb57, hb58, hb59, hb60, hb61, hb62, hb63⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 336#64 (keyBlock key) 48 hs48
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb50 hb51 hb52 hb53 hb54 hb55 hb56 hb57 hb58 hb59 hb60 hb61 hb62 hb63
  nfs3_chunk4_mid b
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv b _ s.mem (nfsSp s₀) hM.iv_bytes, write64_quad_0_ivsw b _ s.mem (nfsSp s₀) hM.iv_bytes,
        writeBytes_ivsw_write8_351_comm, write8_16_stack_336_xor _ _ _ _ hkb_len]; exact hM_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv b _ s.mem (nfsSp s₀) hM.iv_bytes, write64_quad_0_ivsw b _ s.mem (nfsSp s₀) hM.iv_bytes,
        writeBytes_ivsw_write8_351_comm, write8_16_stack_336_xor _ _ _ _ hkb_len]; exact hist_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv b _ s.mem (nfsSp s₀) hM.iv_bytes, write64_quad_0_ivsw b _ s.mem (nfsSp s₀) hM.iv_bytes,
        writeBytes_ivsw_write8_351_comm, write8_16_stack_336_xor _ _ _ _ hkb_len]; exact hblk_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv b _ s.mem (nfsSp s₀) hM.iv_bytes, write64_quad_0_ivsw b _ s.mem (nfsSp s₀) hM.iv_bytes,
        writeBytes_ivsw_write8_351_comm, write8_16_stack_336_xor _ _ _ _ hkb_len]; exact hivsw_final

set_option maxHeartbeats 1600000 in
/-- Combined first half of `new_from_slice` (`0x66fa0 → 0x6748c`). -/
theorem nfs_first_half {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
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
      s'.pc = b + 0x62094#64 ∧
      s'.status = .Running ∧
      NfsRegInv3 b s₀ s' ∧
      NfsMemInv3 b s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 =
        (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  intro key
  have hkey_len : key.length ≤ 64 := by
    dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  refine (nfs_seg0 hpc hstat hlen hiv hb hread_iv hdisj_iv_stack hrw_out hrw_stack
    hdisj_out_stack hdisj_key_stack hal).trans fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx8_1, hx0_1, hx1_1, hx2_1, hq2_1, hq0_1, hk0_1, hs0_1, hs16_1⟩
  refine (nfs_chunk1 hkey_len hpc1 hstat1 hR1 hM1 hx8_1 hx0_1 hx1_1 hx2_1 hs0_1 hs16_1).trans fun s2 h2 => ?_
  rcases h2 with ⟨hpc2, hstat2, hR2, hM2, hx8_2, hx0_2, hx1_2, hx2_2, hx10_2, hx11_2, hq2_2, hq0_2, hs0_2, hs16_2⟩
  refine (nfs_chunk2 hkey_len hal hpc2 hstat2 hR2 hM2 hx8_2 hx0_2 hx1_2 hx2_2 hx10_2 hx11_2
    (hq2_2.trans hq2_1) (hq0_2.trans hq0_1) hk0_1 hs0_2 hs16_2).trans fun s3 h3 => ?_
  rcases h3 with ⟨hpc3, hstat3, hR3, hM3, hx8_3, hx0_3, hx1_3, hx2_3, hx11_3, hx9_3, hs0_3, hs16_3, hs32_3, hs48_3⟩
  refine (nfs_chunk3 hkey_len hpc3 hstat3 hR3 hM3 hx8_3 hx0_3 hx1_3 hx2_3 hx11_3 hx9_3
    hs0_3 hs16_3 hs32_3 hs48_3).trans fun s4 h4 => ?_
  rcases h4 with ⟨hpc4, hstat4, hR4, hM4, hx8_4, hx0_4, hx1_4, hx2_4, hx9_4, hx10_4, hs0_4, hs16_4, hs32_4, hs48_4⟩
  exact nfs_chunk4 hkey_len hal hb hpc4 hstat4 hR4 hM4 hx8_4 hx0_4 hx1_4 hx2_4 hx9_4 hx10_4
    hs0_4 hs16_4 hs32_4 hs48_4

/-! ## Relocatable `[LibsignalPlacement]` First Half of `new_from_slice [local#3]` (Block `402`) -/

abbrev spqrSha256IVSym : String := "spqr:.rodata.cst32+0x40"
abbrev spqrSha256IVAddr [LibsignalPlacement] : BitVec 64 := lsρ spqrSha256IVSym

abbrev nfs3PlacedFakeB [LibsignalPlacement] : BitVec 64 :=
  spqrSha256IVAddr - bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)

@[simp, arm64_norm]
theorem nfs3PlacedFakeB_add_iv [LibsignalPlacement] :
    nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64) = spqrSha256IVAddr :=
  BitVec.sub_add_cancel _ _

theorem RunsTo.pairStep_402_0x28 [LibsignalPlacement]
    {H : String → Option (State → State)} {s₀ s : State} {P_post : State → Prop}
    (hpc : s.pc = (blkPl_402).base + 40#64)
    (hrun : s.status = .Running)
    (hnext : RunsToFrom (lsProg_402 H) s₀
      ((s.writeReg64 (.gpr 22#5) spqrSha256IVAddr).setPC ((blkPl_402).base + 48#64)) P_post) :
    RunsToFrom (lsProg_402 H) s₀ s P_post := by
  let s₁ := (s.writeReg64 (.gpr 22#5) spqrSha256IVAddr).setPC ((blkPl_402).base + 48#64)
  have hwp : SepWP (lsProg_402 H) ((blkPl_402).base + 48#64) s emp (fun sf _ => sf = s₁) := by
    refine blkPC_402_pairStep_0x28 (blkPl_402).base H rfl hpc hrun ?_
    simpa [s₁, arm64_norm, spqrSha256IVAddr, spqrSha256IVSym] using
      (SepWP.done (prog := lsProg_402 H) (s := s₁) (P := emp) (post := fun sf _ => sf = s₁)
        rfl (by simpa [s₁, State.setPC, State.writeReg64] using hrun) rfl)
  intro hL
  have hreaches := SepWP.reaches_of_sepWP hwp (R := emp) (by simp) hL
  obtain ⟨sf, hst1, ⟨_, _, rfl⟩ | ⟨_, hoom⟩⟩ := hreaches
  · obtain ⟨s', hst2, htr, hvregs, hP, hL'⟩ := hnext hL
    exact ⟨s', hst1.trans hst2, htr, hvregs, hP, hL'⟩
  · exact hoom.elim

@[scoped simp, arm64_norm]
theorem read64_write8_stack_iv3_placed_zero [LibsignalPlacement] {s₀ : State}
    (hdisj : DisjointRegions spqrSha256IVAddr 32 (nfsSp s₀) 544)
    (m : Memory) (c : BitVec 64) (v : BitVec 8)
    (hc : decide (c.toNat < 544) = true) :
    (m.write8 (nfsSp s₀ + c) v).read64 spqrSha256IVAddr = m.read64 spqrSha256IVAddr := by
  have hc' : c.toNat < 544 := of_decide_eq_true hc
  refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write8_self m (nfsSp s₀ + c) v)) ?_
  clear * - hdisj hc'
  simp only [List.mem_singleton, forall_eq, DisjointRegions] at hdisj ⊢
  bv_omega

@[scoped simp, arm64_norm]
theorem read64_write8_stack_iv3_placed_off [LibsignalPlacement] {s₀ : State}
    (hdisj : DisjointRegions spqrSha256IVAddr 32 (nfsSp s₀) 544)
    (m : Memory) (off c : BitVec 64) (v : BitVec 8)
    (hc : decide (c.toNat < 544) = true)
    (hoff : decide (off.toNat + 8 ≤ 32) = true) :
    (m.write8 (nfsSp s₀ + c) v).read64 (spqrSha256IVAddr + off) = m.read64 (spqrSha256IVAddr + off) := by
  have hc' : c.toNat < 544 := of_decide_eq_true hc
  have hoff' : off.toNat + 8 ≤ 32 := of_decide_eq_true hoff
  refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write8_self m (nfsSp s₀ + c) v)) ?_
  clear * - hdisj hc' hoff'
  simp only [List.mem_singleton, forall_eq, DisjointRegions] at hdisj ⊢
  bv_omega

theorem write64_quad_400_iv3_placed [LibsignalPlacement] (m₁ m₂ : Memory) (sp : BitVec 64)
    (hiv : m₂.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV) :
    ((((m₁.write64 (sp + 400#64) (m₂.read64 spqrSha256IVAddr)).write64
      (sp + 408#64) (m₂.read64 (spqrSha256IVAddr + 8#64))).write64
      (sp + 416#64) (m₂.read64 (spqrSha256IVAddr + 16#64))).write64
      (sp + 424#64) (m₂.read64 (spqrSha256IVAddr + 24#64))) =
    m₁.writeBytes (sp + 400#64) (shaStateBytes sha256IV) := by
  have hd1 : sp + 408#64 = (sp + 400#64) + 8#64 := by bv_omega
  have hd2 : sp + 416#64 = (sp + 400#64) + 16#64 := by bv_omega
  have hd3 : sp + 424#64 = (sp + 400#64) + 24#64 := by bv_omega
  rw [hd1, hd2, hd3, write64_quad_read64_eq_writeBytes_32, hiv]

theorem write64_quad_0_ivsw3_placed [LibsignalPlacement] (m₁ m₂ : Memory) (sp : BitVec 64)
    (hiv : m₂.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV) :
    ((((m₁.write64 sp (m₂.read64 (spqrSha256IVAddr + 16#64))).write64
      (sp + 8#64) (m₂.read64 (spqrSha256IVAddr + 24#64))).write64
      (sp + 16#64) (m₂.read64 spqrSha256IVAddr)).write64
      (sp + 24#64) (m₂.read64 (spqrSha256IVAddr + 8#64))) =
    m₁.writeBytes sp ((shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  have hd3 : sp + 24#64 = (sp + 16#64) + 8#64 := by bv_omega
  have hs1 : spqrSha256IVAddr + 24#64 = (spqrSha256IVAddr + 16#64) + 8#64 := by bv_omega
  have hlen : (shaStateBytes sha256IV).length = 32 := shaStateBytes_length sha256IV
  have htake : m₂.readBytes spqrSha256IVAddr 16 = (shaStateBytes sha256IV).take 16 := by
    have h := readBytes_slice_of_readBytes_eq m₂ spqrSha256IVAddr (shaStateBytes sha256IV)
      (by rw [hlen]; exact hiv) 0 16 (by omega)
    simpa using h
  have hdrop : m₂.readBytes (spqrSha256IVAddr + 16#64) 16 = (shaStateBytes sha256IV).drop 16 := by
    have h := readBytes_slice_of_readBytes_eq m₂ spqrSha256IVAddr (shaStateBytes sha256IV)
      (by rw [hlen]; exact hiv) 16 16 (by omega)
    have hadd : spqrSha256IVAddr + BitVec.ofNat 64 16 = spqrSha256IVAddr + 16#64 := rfl
    rw [hadd, List.take_of_length_le (by simp [hlen])] at h
    exact h
  rw [hd3, hs1, write64_pair_read64_eq_writeBytes_16, write64_pair_read64_eq_writeBytes_16,
      hdrop, htake, writeBytes_append]
  have hlen_drop : ((shaStateBytes sha256IV).drop 16).length = 16 := by simp [hlen]
  rw [hlen_drop]

set_option maxHeartbeats 3200000 in
theorem nfs_seg0_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (h_memcpy : H lsMemcpySym = some memcpyHook) {s₀ : State}
    (hpc : s₀.pc = (blkPl_402).base) (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s₀ (fun s' =>
      s'.pc = (blkPl_402).base + 476#64 ∧ s'.status = .Running ∧
      NfsRegInv3 nfs3PlacedFakeB s₀ s' ∧ NfsMemInv3 nfs3PlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧ s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.readVReg128 2#5 = s'.mem.read64 (nfsSp s₀ + 152#64) ++ s'.mem.read64 (nfsSp s₀ + 144#64) ∧
      s'.readVReg128 0#5 = s'.mem.read64 (nfsSp s₀ + 168#64) ++ s'.mem.read64 (nfsSp s₀ + 160#64) ∧
      s'.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  intro key; generalize hPost : (fun s' : State => _) = Post
  have hkey_len : key.length ≤ 64 := by dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hkey_len
  have hsp₀ : s₀.sp = nfsSp s₀ + 544#64 := nfs_sp_eq_add s₀
  have hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64 := nfs_sp_align hal
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hRW_stack : s₀.mem.RW (nfsSp s₀) 544 := hrw_stack
  have hcond : BitVec.ule 0x41#64 (s₀.readReg64 .x2) = false := nfs_ule_65_false hlen
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  refine RunsTo.pairStep_402_0x28 (by simp only [arm64_norm, hpc]) (by simp only [arm64_norm, hstat]) ?_
  sess_step; sess_step; sess_step; sess_step; sess_step
  have hA_pro : AgreesOutside s₀.mem (nfsPrologueMem s₀) (nfsSp s₀ + 464#64) 80 := agreesOutside_nfsPrologueMem s₀
  have hA_zero : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)) (nfsSp s₀ + 112#64) 64 := by
    simpa using ProofLib.agreesOutside_writeBytes (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (List.replicate 64 0#8)
  have hread_key : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).readBytes
      (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key := by
    rcases hdisj_key_stack with h0 | hdisj_key_stack
    · simp only [key, h0, Memory.readBytes]
    have hdisj_key_pro : DisjointRegions (nfsSp s₀ + 464#64) 80 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    have hdisj_key_112 : DisjointRegions (nfsSp s₀ + 112#64) 64 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    rw [(agreesOutside_toFrame hA_zero).readBytes_eq (by simp [hdisj_key_112]) (by omega),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdisj_key_pro]) (by omega)]
  have hrw_memcpy : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW
      (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat := by
    have hrw0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW (nfsSp s₀) 544 :=
      (Frame.rw_iff (agreesOutside_toFrame hA_zero) _ _).mpr ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
    exact hrw0.sub (by clear * - hlen; bv_omega)
  refine RunsTo.placed_memcpy_step h_memcpy (hrun := by simp only [arm64_norm, hstat])
    (hpc := by simp only [arm64_norm, lsMemcpySym]) (hx0 := by simp only [arm64_norm])
    (hx1 := by simp only [arm64_norm]) (hx2 := by simp only [arm64_norm]) (hlr := by simp only [arm64_norm]; rfl)
    (hmem := write64_oct_zero_eq_writeBytes_64 (nfsPrologueMem s₀) (nfsSp s₀)) (hread := hread_key) (hrw := hrw_memcpy) ?_
  rw [writeBytes_key_over_zero64]
  have hA_k0 : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)) (nfsSp s₀ + 112#64) 64 := by
    have h := ProofLib.agreesOutside_writeBytes (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key); rwa [hkb_len] at h
  have hRW_k0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hA_k0) _ _).mpr ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost; refine RunsTo.refl ?_
  set m_k0 := (nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)
  have hk0_64 : m_k0.readBytes (nfsSp s₀ + 112#64) 64 = keyBlock key :=
    Layout.readBytes_writeBytes_eq (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key) 64 hkb_len (by decide)
  have hk0_take32 : m_k0.readBytes (nfsSp s₀ + 112#64) 32 = (keyBlock key).take 32 := by
    simpa using readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key) (by rw [hkb_len]; exact hk0_64) 0 32 (by omega)
  have hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key) (by rw [hkb_len]; exact hk0_64) 32 32 (by omega)
    have hadd : (nfsSp s₀ + 112#64) + BitVec.ofNat 64 32 = nfsSp s₀ + 144#64 := by clear * -; bv_omega
    rw [hadd, List.take_of_length_le (by simp [hkb_len])] at h; exact h
  have hA_432 : AgreesOutside m_k0 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) (nfsSp s₀ + 432#64) 8 :=
    AgreesOutside.write64_self m_k0 (nfsSp s₀ + 432#64) 1#64
  have hf_k0 : Frame s₀.mem (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := by
    have hf0 : Frame s₀.mem s₀.mem [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := Frame.refl _ _
    have hf1 := Frame.of_agreesOutside_stack hf0 hA_pro (by decide)
    have hf2 := Frame.of_agreesOutside_stack hf1 hA_k0 (by decide)
    exact Frame.of_agreesOutside_stack hf2 hA_432 (by decide)
  have hM_432 : NfsMemInv3 nfs3PlacedFakeB s₀ (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) := {
    rw_stack := (Frame.rw_iff hf_k0 _ _).mpr hrw_stack, rw_out := (Frame.rw_iff hf_k0 _ _).mpr hrw_out
    readable_iv := by rw [nfs3PlacedFakeB_add_iv]; exact (Frame.readable_iff hf_k0 _ _).mpr hread_iv
    iv_bytes := by
      rw [nfs3PlacedFakeB_add_iv]
      have hd432 : DisjointRegions (nfsSp s₀ + 432#64) 8 spqrSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdk0 : DisjointRegions (nfsSp s₀ + 112#64) 64 spqrSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdpro : DisjointRegions (nfsSp s₀ + 464#64) 80 spqrSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      rw [(agreesOutside_toFrame hA_432).readBytes_eq (by simp [hd432]) (by decide),
          (agreesOutside_toFrame hA_k0).readBytes_eq (by simp [hdk0]) (by decide),
          (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdpro]) (by decide), hiv]
    disj_iv_stack := by rw [nfs3PlacedFakeB_add_iv]; exact hdisj_iv_stack
    disj_out_stack := hdisj_out_stack, saved := nfsSavedStack_prologue_432 s₀ m_k0 hA_k0, frame := hf_k0 }
  have hM_final : NfsMemInv3 nfs3PlacedFakeB s₀
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)) :=
    (hM_432.writeBytes_low 288#64 _ (by simp [slice16_length])).writeBytes_low 304#64 _ (by simp [slice16_length])
  have h144_eq : (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes (nfsSp s₀ + 288#64)
        (slice16 (keyBlock key) 0)).writeBytes (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)).readBytes
        (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 := by
    rw [readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        (agreesOutside_toFrame hA_432).readBytes_eq
          (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide), hk0_drop32]
  refine ⟨by simp only [arm64_norm], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm], hal_nfs, by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩, ?_,
    by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm], ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact hM_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact h144_eq
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)

set_option maxHeartbeats 1600000 in
theorem nfs_chunk1_placed [LibsignalPlacement] {H : String → Option (State → State)} {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64) (hpc : s.pc = (blkPl_402).base + 476#64) (hstat : s.status = .Running)
    (hR : NfsRegInv3 nfs3PlacedFakeB s₀ s) (hM : NfsMemInv3 nfs3PlacedFakeB s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64) (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64) (hx2 : s.readReg64 .x2 = 1#64)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) :
    RunsTo (lsProg_402 H) s (fun s' =>
      s'.pc = (blkPl_402).base + 676#64 ∧ s'.status = .Running ∧
      NfsRegInv3 nfs3PlacedFakeB s₀ s' ∧ NfsMemInv3 nfs3PlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧ s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.readReg64 .x10 = (byteAt (keyBlock key) 16).zeroExtend 64 ∧
      s'.readReg64 .x11 = (byteAt (keyBlock key) 17).zeroExtend 64 ∧
      s'.readVReg128 2#5 = s.readVReg128 2#5 ∧ s'.readVReg128 0#5 = s.readVReg128 0#5 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  nfs3_chunk1_body

set_option maxHeartbeats 1600000 in
theorem nfs_chunk2_placed [LibsignalPlacement] {H : String → Option (State → State)} {s₀ s : State} {m_k0 : Memory} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64) (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hpc : s.pc = (blkPl_402).base + 676#64) (hstat : s.status = .Running)
    (hR : NfsRegInv3 nfs3PlacedFakeB s₀ s) (hM : NfsMemInv3 nfs3PlacedFakeB s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64) (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64) (hx2 : s.readReg64 .x2 = 1#64)
    (hx10 : s.readReg64 .x10 = (byteAt (keyBlock key) 16).zeroExtend 64)
    (hx11 : s.readReg64 .x11 = (byteAt (keyBlock key) 17).zeroExtend 64)
    (hq2 : s.readVReg128 2#5 = m_k0.read64 (nfsSp s₀ + 152#64) ++ m_k0.read64 (nfsSp s₀ + 144#64))
    (hq0 : s.readVReg128 0#5 = m_k0.read64 (nfsSp s₀ + 168#64) ++ m_k0.read64 (nfsSp s₀ + 160#64))
    (hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) :
    RunsTo (lsProg_402 H) s (fun s' =>
      s'.pc = (blkPl_402).base + 876#64 ∧ s'.status = .Running ∧
      NfsRegInv3 nfs3PlacedFakeB s₀ s' ∧ NfsMemInv3 nfs3PlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧ s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.readReg64 .x11 = (byteAt (keyBlock key) 32 ^^^ 0x36#8).zeroExtend 64 ∧
      s'.readReg64 .x9 = (byteAt (keyBlock key) 33).zeroExtend 64 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16 ∧
      s'.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 (keyBlock key) 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) := by
  nfs3_chunk2_body

set_option maxHeartbeats 1600000 in
theorem nfs_chunk3_placed [LibsignalPlacement] {H : String → Option (State → State)} {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64) (hpc : s.pc = (blkPl_402).base + 876#64) (hstat : s.status = .Running)
    (hR : NfsRegInv3 nfs3PlacedFakeB s₀ s) (hM : NfsMemInv3 nfs3PlacedFakeB s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64) (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64) (hx2 : s.readReg64 .x2 = 1#64)
    (hx11 : s.readReg64 .x11 = (byteAt (keyBlock key) 32 ^^^ 0x36#8).zeroExtend 64)
    (hx9 : s.readReg64 .x9 = (byteAt (keyBlock key) 33).zeroExtend 64)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16)
    (hs32 : s.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 (keyBlock key) 32)
    (hs48 : s.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) :
    RunsTo (lsProg_402 H) s (fun s' =>
      s'.pc = (blkPl_402).base + 1068#64 ∧ s'.status = .Running ∧
      NfsRegInv3 nfs3PlacedFakeB s₀ s' ∧ NfsMemInv3 nfs3PlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧ s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.readReg64 .x9 = (byteAt (keyBlock key) 48 ^^^ 0x36#8).zeroExtend 64 ∧
      s'.readReg64 .x10 = (byteAt (keyBlock key) 49).zeroExtend 64 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16 ∧
      s'.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) := by
  nfs3_chunk3_body

set_option maxHeartbeats 1600000 in
theorem nfs_chunk4_placed [LibsignalPlacement] {H : String → Option (State → State)} {s₀ s : State} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64) (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hpc : s.pc = (blkPl_402).base + 1068#64) (hstat : s.status = .Running)
    (hR : NfsRegInv3 nfs3PlacedFakeB s₀ s) (hM : NfsMemInv3 nfs3PlacedFakeB s₀ s.mem)
    (hx8 : s.readReg64 .x8 = 0x36#64) (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64) (hx2 : s.readReg64 .x2 = 1#64)
    (hx9 : s.readReg64 .x9 = (byteAt (keyBlock key) 48 ^^^ 0x36#8).zeroExtend 64)
    (hx10 : s.readReg64 .x10 = (byteAt (keyBlock key) 49).zeroExtend 64)
    (hs0 : s.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 0)
    (hs16 : s.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 16)
    (hs32 : s.mem.readBytes (nfsSp s₀ + 320#64) 16 = slice16 ((keyBlock key).map (· ^^^ 0x36#8)) 32)
    (hs48 : s.mem.readBytes (nfsSp s₀ + 336#64) 16 = slice16 (keyBlock key) 48) :
    RunsTo (lsProg_402 H) s (fun s' =>
      s'.pc = (blkPl_402).base + 1260#64 ∧ s'.status = .Running ∧
      NfsRegInv3 nfs3PlacedFakeB s₀ s' ∧ NfsMemInv3 nfs3PlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧ s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 = (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  generalize hPost : (fun s' : State => _) = Post
  obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
  rw [nfs3PlacedFakeB_add_iv] at hx22
  have hRW_stack : s.mem.RW (nfsSp s₀) 544 := hM.rw_stack
  have hread_iv : s.mem.Readable spqrSha256IVAddr 32 := by have h := hM.readable_iv; rwa [nfs3PlacedFakeB_add_iv] at h
  have hdisj_iv : DisjointRegions spqrSha256IVAddr 32 (nfsSp s₀) 544 := by have h := hM.disj_iv_stack; rwa [nfs3PlacedFakeB_add_iv] at h
  have hiv_bytes : s.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV := by have h := hM.iv_bytes; rwa [nfs3PlacedFakeB_add_iv] at h
  have hread_iv_eq0 := read64_write8_stack_iv3_placed_zero hdisj_iv
  have hread_iv_eq := read64_write8_stack_iv3_placed_off hdisj_iv
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hlen
  obtain ⟨-, -, hb50, hb51, hb52, hb53, hb54, hb55, hb56, hb57, hb58, hb59, hb60, hb61, hb62, hb63⟩ :=
    read8_16_of_readBytes_slice16 s.mem (nfsSp s₀) 336#64 (keyBlock key) 48 hs48
  simp only [Nat.add_zero, Nat.reduceAdd, BitVec.reduceAdd] at hb50 hb51 hb52 hb53 hb54 hb55 hb56 hb57 hb58 hb59 hb60 hb61 hb62 hb63
  nfs3_chunk4_mid nfs3PlacedFakeB
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv3_placed _ s.mem (nfsSp s₀) hiv_bytes, write64_quad_0_ivsw3_placed _ s.mem (nfsSp s₀) hiv_bytes,
        writeBytes_ivsw_write8_351_comm, write8_16_stack_336_xor _ _ _ _ hkb_len]; exact hM_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv3_placed _ s.mem (nfsSp s₀) hiv_bytes, write64_quad_0_ivsw3_placed _ s.mem (nfsSp s₀) hiv_bytes,
        writeBytes_ivsw_write8_351_comm, write8_16_stack_336_xor _ _ _ _ hkb_len]; exact hist_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv3_placed _ s.mem (nfsSp s₀) hiv_bytes, write64_quad_0_ivsw3_placed _ s.mem (nfsSp s₀) hiv_bytes,
        writeBytes_ivsw_write8_351_comm, write8_16_stack_336_xor _ _ _ _ hkb_len]; exact hblk_final
  · dsimp only [State.setMem, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_400_iv3_placed _ s.mem (nfsSp s₀) hiv_bytes, write64_quad_0_ivsw3_placed _ s.mem (nfsSp s₀) hiv_bytes,
        writeBytes_ivsw_write8_351_comm, write8_16_stack_336_xor _ _ _ _ hkb_len]; exact hivsw_final

set_option maxHeartbeats 1600000 in
theorem nfs_first_half_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (h_memcpy : H lsMemcpySym = some memcpyHook) {s₀ : State}
    (hpc : s₀.pc = (blkPl_402).base) (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s₀ (fun s' =>
      s'.pc = (blkPl_402).base + 1260#64 ∧ s'.status = .Running ∧
      NfsRegInv3 nfs3PlacedFakeB s₀ s' ∧ NfsMemInv3 nfs3PlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧ s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 = (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  intro key
  have hkey_len : key.length ≤ 64 := by dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  refine (nfs_seg0_placed h_memcpy hpc hstat hlen hiv hread_iv hdisj_iv_stack hrw_out hrw_stack
    hdisj_out_stack hdisj_key_stack hal).trans fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx8_1, hx0_1, hx1_1, hx2_1, hq2_1, hq0_1, hk0_1, hs0_1, hs16_1⟩
  refine (nfs_chunk1_placed hkey_len hpc1 hstat1 hR1 hM1 hx8_1 hx0_1 hx1_1 hx2_1 hs0_1 hs16_1).trans fun s2 h2 => ?_
  rcases h2 with ⟨hpc2, hstat2, hR2, hM2, hx8_2, hx0_2, hx1_2, hx2_2, hx10_2, hx11_2, hq2_2, hq0_2, hs0_2, hs16_2⟩
  refine (nfs_chunk2_placed hkey_len hal hpc2 hstat2 hR2 hM2 hx8_2 hx0_2 hx1_2 hx2_2 hx10_2 hx11_2
    (hq2_2.trans hq2_1) (hq0_2.trans hq0_1) hk0_1 hs0_2 hs16_2).trans fun s3 h3 => ?_
  rcases h3 with ⟨hpc3, hstat3, hR3, hM3, hx8_3, hx0_3, hx1_3, hx2_3, hx11_3, hx9_3, hs0_3, hs16_3, hs32_3, hs48_3⟩
  refine (nfs_chunk3_placed hkey_len hpc3 hstat3 hR3 hM3 hx8_3 hx0_3 hx1_3 hx2_3 hx11_3 hx9_3
    hs0_3 hs16_3 hs32_3 hs48_3).trans fun s4 h4 => ?_
  rcases h4 with ⟨hpc4, hstat4, hR4, hM4, hx8_4, hx0_4, hx1_4, hx2_4, hx9_4, hx10_4, hs0_4, hs16_4, hs32_4, hs48_4⟩
  exact nfs_chunk4_placed hkey_len hal hpc4 hstat4 hR4 hM4 hx8_4 hx0_4 hx1_4 hx2_4 hx9_4 hx10_4
    hs0_4 hs16_4 hs32_4 hs48_4

end CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof
