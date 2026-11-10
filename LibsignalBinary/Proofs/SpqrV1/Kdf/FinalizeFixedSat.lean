/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt

/-!
# `HookSat` Contracts for `Hmac<Sha256>::finalize_fixed` (Block `425`)

Proves the `HookSat`-parameterized sibling contracts for SPQR's
`<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#3]` (Block `425`),
replacing `[HkdfPlacedHooks C.F H]` with `[HkdfPlacedHooksExactSat C.F H]` while proving
the identical `FinalizeFixed3PlacedOk C H` and `withLsCodeLoaded` `subroutine_ok` conclusions,
together with `S2Frame`-framed `RunsTo` contracts (`finalize_fixed3_pfx_placed_runsTo_sat`,
`finalize_fixed3_placed_runsTo_sat`, and `*_of_other_block_sat`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.HMAC (ShaState chunks64 hmacWith toBEBytes)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkPC_425 blkPl_425 lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved FinSaved Frame HmacSt RW RunsTo RunsToFrom
   TraceEq agreesOutside_pad_memset agreesOutside_seg2a agreesOutside_seg3a agreesOutside_seg4a
   digestBytes digestBytes_eq_append finalizeFixedSpec finSaved_seg3a finSaved_seg4a frame_seg2a
   frame_seg3a frame_seg4a fsp_aligned hmacCoreAt hmacInnerInit hmacOuterInit isBlock_hmacCoreAt
   length_hmacWith lsCompress256Sym lsMemsetSym outerBlock outerBlock_digestBytes_length
   read32_words_at_104_of_shaStateBytes read32_words_at_64_of_shaStateBytes read64_seg2a_mid
   read64_seg3a_pad_32 read64_seg3a_pad_40 readBytes_56_eq_append_8 readBytes_56_of_buf_eq
   readBytes_64_after_pad_memset readBytes_fsp_64_seg2 readBytes_fsp_64_seg3
   readBytes_write32_8_digestBytes shaStateBytes_length toLEBytes_4_rev32 toLEBytes_8_read64
   toLEBytes_8_rev32_append toLEBytes_8_rev64 ult_7_of_lt_56 xor_63_of_lt_64 zeroExtend64_ofNat8
   zeroExtend64_truncate32_ofNat64)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (CallingConventionPreserved.x19 CallingConventionPreserved.x20
   CallingConventionPreserved.x21 CallingConventionPreserved.x22
   CallingConventionPreserved.x27 CallingConventionPreserved.x29 S2Frame)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
  (AgreesOn AgreesOn.finSaved_of AgreesOn.read64_eq AgreesOn.readBytes_eq
   S2Frame.trans_agreesOutside S2Frame.trans_agreesOutside_sub S2Frame.update_three_blocks)
open CryptoVerification.SpqrV1.Kdf
  (FinPre3 FinPre3Pfx FinalizeFixed3PlacedOk HmacStN bit_len_innerN_eq
   fin3PlacedFakeB fin3PlacedFakeB_off_0 hmacWith_pfx_short
   innerLastBlockN innerLastBlockN_length)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (CallingConventionPreserved.x23 CallingConventionPreserved.x24 CallingConventionPreserved.x25
   CallingConventionPreserved.x26 CallingConventionPreserved.x28 HkdfPlacedHooksExactSat
   s2_compress256_step_placed_sat_exact s2_memset_step_placed_sat_exact)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat (FinCommonSat FinPostSat)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

private theorem mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

@[local simp, local arm64_norm]
private theorem extractLsb'_0_64_zero128 : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl

@[local simp, local arm64_norm]
private theorem extractLsb'_64_64_zero128 : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl

private theorem finSaved_seg2a {s0 : State} {m1 m2 m3 m4 : Memory} {hm fsp : BitVec 64}
    (hs : FinSaved s0 fsp m1) (hag1 : AgreesOutside m1 m2 fsp 64)
    (hag2 : AgreesOutside m2 m3 hm 64) (hag3 : AgreesOutside m3 m4 fsp 64)
    (hd_fsp : DisjointRegions fsp 64 (fsp + 0x40#64) 0x50)
    (hd_hm : DisjointRegions hm 64 (fsp + 0x40#64) 0x50) :
    FinSaved s0 fsp m4 :=
  FinSaved.of_agreesOutside
    (FinSaved.of_agreesOutside (FinSaved.of_agreesOutside hs hag1 hd_fsp) hag2 hd_hm) hag3 hd_fsp

public theorem frame_seg2a_s2 {m0 m1 m2 m3 m4 : Memory} {out hm fsp : BitVec 64}
    (hf : S2Frame m0 m1 [(out, 32), (hm, 0x90), (fsp, 144)])
    (hag1 : AgreesOutside m1 m2 fsp 64)
    (hag2 : AgreesOutside m2 m3 hm 64)
    (hag3 : AgreesOutside m3 m4 fsp 64) :
    S2Frame m0 m4 [(out, 32), (hm, 0x90), (fsp, 144)] :=
  hf.trans (S2Frame.of_frame (frame_seg2a (Frame.refl m1 _) hag1 hag2 hag3))

public theorem frame_seg3a_s2 {m0 m1 m2 m3 m4 m5 : Memory} {out hm fsp : BitVec 64}
    (hf : S2Frame m0 m1 [(out, 32), (hm, 0x90), (fsp, 144)])
    (hag1 : AgreesOutside m1 m2 hm 64)
    (hag2 : AgreesOutside m2 m3 fsp 64)
    (hag3 : AgreesOutside m3 m4 hm 64)
    (hag4 : AgreesOutside m4 m5 fsp 64) :
    S2Frame m0 m5 [(out, 32), (hm, 0x90), (fsp, 144)] :=
  hf.trans (S2Frame.of_frame (frame_seg3a (Frame.refl m1 _) hag1 hag2 hag3 hag4))

public theorem frame_seg4a_s2 {m0 m1 m2 m3 m4 m5 : Memory} {out hm fsp : BitVec 64}
    (hf : S2Frame m0 m1 [(out, 32), (hm, 0x90), (fsp, 144)])
    (hag1 : AgreesOutside m1 m2 hm 0x90)
    (hag2 : AgreesOutside m2 m3 fsp 64)
    (hag3 : AgreesOutside m3 m4 hm 0x90)
    (hag4 : AgreesOutside m4 m5 out 32) :
    S2Frame m0 m5 [(out, 32), (hm, 0x90), (fsp, 144)] :=
  hf.trans (S2Frame.of_frame (frame_seg4a (Frame.refl m1 _) hag1 hag2 hag3 hag4))

/-! ## 1. Placed Step Wrappers for Block `425` under `[HkdfPlacedHooksExactSat C.F H]` -/

public theorem s2_memset_step_425_sat [LibsignalPlacement] (C : Crypto) (H : LibsignalHooks)
    [HkdfPlacedHooksExactSat C.F H] {s₀ s : State} {Q : State → Prop} {dst lr : BitVec 64} {len : ℕ}
    (hrun : s.status = .Running) (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : (s.readReg64 .x1).truncate 8 = 0#8)
    (hx2 : (s.readReg64 .x2).toNat = len) (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64) (hrw : s.mem.RW dst len)
    (h : ∀ sf : State,
      TraceEq s₀ sf →
      sf.pc = lr →
      sf.status = .Running →
      CallingConventionPreserved s sf →
      sf.readReg64 .x0 = dst →
      s.mem.KeepsFrozen sf.mem →
      sf.mem.readBytes dst len = List.replicate len 0#8 →
      S2Frame s.mem sf.mem [(dst, len)] →
      AgreesOn (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false)
        sf.mem (s.mem.writeBytes dst (List.replicate len 0#8)) →
      RunsToFrom ((blkPC_425).rebase (blkPl_425).base H) s₀ sf Q)
    (htr_s : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide))) :
    RunsToFrom ((blkPC_425).rebase (blkPl_425).base H) s₀ s Q :=
  s2_memset_step_placed_sat_exact C H hrun hpc hx0 hx1 hx2 hlr hsp_al hrw h htr_s

public theorem s2_compress256_step_425_sat [LibsignalPlacement] (C : Crypto) (H : LibsignalHooks)
    [HkdfPlacedHooksExactSat C.F H] {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running) (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr) (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64) (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st) (hblk : s.mem.readBytes blkPtr 64 = blk)
    (hlen : blk.length = 64) (hrw : s.mem.RW stPtr 32)
    (h : RunsToFrom ((blkPC_425).rebase (blkPl_425).base H) s₀
      ((s.setMem (s.mem.writeBytes stPtr (shaStateBytes (C.F st blk)))).setPC lr) Q) :
    RunsToFrom ((blkPC_425).rebase (blkPl_425).base H) s₀ s Q :=
  s2_compress256_step_placed_sat_exact C H hrun hpc hx0 hx1 hx2 hlr hst hblk hlen hrw h

/-! ## 2. `S2Frame`-Framed Cut Predicates for Block `425` -/

public structure StateF0p3Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_425).base + 28#64
  common  : FinCommonSat s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x0
  x1_eq   : s.readReg64 .x1 = s0.readReg64 .x1
  hmac_st : HmacStN s.mem (s0.readReg64 .x1) F key pfx tail

private structure StateF1_3Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_425).base + 76#64
  common  : FinCommonSat s0 s
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

private structure StateF2_3Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_425).base + 176#64
  common  : FinCommonSat s0 s
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

private structure StateF3_3Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_425).base + 180#64
  common  : FinCommonSat s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes (F ((chunks64 pfx).foldl F (hmacInnerInit F key))
      (innerLastBlockN (1 + pfx.length / 64) tail))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateF3b_3Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_425).base + 304#64
  common  : FinCommonSat s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 =
    outerBlock (digestBytes (F ((chunks64 pfx).foldl F (hmacInnerInit F key))
      (innerLastBlockN (1 + pfx.length / 64) tail)))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)

private structure StateF4_3Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_425).base + 308#64
  common  : FinCommonSat s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 =
    shaStateBytes (F (hmacOuterInit F key)
      (outerBlock (digestBytes (F ((chunks64 pfx).foldl F (hmacInnerInit F key))
        (innerLastBlockN (1 + pfx.length / 64) tail)))))

private structure StateF5_3Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_425).base + 420#64
  common : FinCommonSat s0 s
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

private theorem ost_eq_seg3a {m m1 m2 m3 m4 : Memory} {hm fsp : BitVec 64} {bs : List (BitVec 8)}
    (host : m.readBytes (hm + 0x68#64) 32 = bs)
    (hag1 : AgreesOutside m m1 hm 64)
    (hag2 : AgreesOutside m1 m2 fsp 64)
    (hag3 : AgreesOutside m2 m3 hm 64)
    (hag4 : AgreesOutside m3 m4 fsp 64)
    (hd_hm : DisjointRegions hm 64 (hm + 0x68#64) 32)
    (hd_fsp : DisjointRegions fsp 64 (hm + 0x68#64) 32) :
    m4.readBytes (hm + 0x68#64) 32 = bs :=
  (hag4.readBytes_eq hd_fsp (by decide)).trans
    ((hag3.readBytes_eq hd_hm (by decide)).trans
      ((hag2.readBytes_eq hd_fsp (by decide)).trans
        ((hag1.readBytes_eq hd_hm (by decide)).trans host)))

/-! ## 3. Placed Segment Proofs for Block `425` (`tail.length < 56`) -/

section PlacedSat

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksExactSat C.F H]

set_option maxHeartbeats 1600000 in
private theorem seg1a_placed_runsTo_sat {key pfx tail : List (BitVec 8)} {s0 : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s0 (StateF0p3Sat C.F key pfx tail s0) := by
  have hpc : s0.pc = (blkPl_425).base := by simpa only [fin3PlacedFakeB_off_0] using hpre.pc_eq
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
      (s0.sp - 144#64) 144 := by
    agrees_outside_writes
  refine
    { pc_eq := by fin3_reg
      common :=
        { status := by fin3_reg, sp_eq := by fin3_reg, x29_eq := by fin3_reg,
          x26_eq := by fin3_reg, x27_eq := by fin3_reg, x28_eq := by fin3_reg,
          saved := ⟨by solve_fin3_saved, by solve_fin3_saved, by solve_fin3_saved,
                    by solve_fin3_saved, by solve_fin3_saved, by solve_fin3_saved,
                    by solve_fin3_saved, by solve_fin3_saved, by solve_fin3_saved⟩
          frame := by
            rw [mem_setMem]
            exact S2Frame.trans_agreesOutside (S2Frame.refl s0.mem _) (by simp) hag }
      x0_eq := by fin3_reg
      x1_eq := by fin3_reg
      hmac_st := by rw [mem_setMem]; exact HmacStN.of_agreesOutside hpre.hmac_st hag hpre.disj_hm_fsp.symm }

set_option maxHeartbeats 1600000 in
private theorem seg1b_placed_runsTo_sat {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF0p3Sat C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF1_3Sat C.F key pfx tail s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hhmac⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  rcases hhmac with ⟨hpfx_mod, hmsg_lt64, hmsg_eq, hpos_eq, hin_eq, hibl_eq, hout_eq, hobl_eq⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp_s : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp
  have hcw_pos : s.mem.canWrite (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) 1 = true :=
    hrw_hm.canWrite_sub (by bv_omega) (by decide)
  have hze32 := zeroExtend64_truncate32_ofNat64 hmsg_lt64
  have hze64 := zeroExtend64_ofNat8 hmsg_lt64
  have hxor63 := xor_63_of_lt_64 hmsg_lt64
  iterate 12 s2_step
  have htoNat_sub : (BitVec.ofNat 64 (63 - tail.length)).toNat = 63 - tail.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  set dst := s0.readReg64 .x1 + BitVec.ofNat 64 tail.length + 1#64
  set len := 63 - tail.length
  set m_pad := s.mem.write8 (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) 128#8
  have hrw_memset : m_pad.RW dst len := by
    refine Memory.RW.of_perm_eq (by simp [m_pad]) (fun _ => Memory.isLazyFree_write8_of_false _ _)
      (hrw_hm.sub ?_)
    have := hpre.tail_lt; dsimp only [dst, len]; bv_omega
  refine s2_memset_step_425_sat C H
    (dst := dst) (lr := (blkPl_425).base + 76#64) (len := len)
    hstat (by simp only [arm64_norm, lsMemsetSym])
    (by simp only [dst, arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simpa only [len, arm64_norm] using htoNat_sub)
    ((by fin3_reg) : _ = (blkPl_425).base + 76#64)
    (by simp only [arm64_norm, hsp]; exact hpre.sp_aligned)
    hrw_memset
    fun sf htr2 hsf_pc hsf_stat hsf_cc _ _ _ hsf_frame hsf_ag => ?_
  refine RunsTo.refl ?_ htr2
  have hag_full := agreesOutside_pad_memset s.mem (s0.readReg64 .x1) tail hpre.tail_lt
  have hP_pad : ∀ {a : BitVec 64}, s.mem.permNoLazy a = some Perm.rw →
      (m_pad.perm a).r = true ∧ m_pad.isLazyFree a = false := by
    intro a hnl
    obtain ⟨hrw_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl
    exact ⟨by dsimp only [m_pad]; rw [Memory.perm_write8, hrw_a]; rfl,
      Memory.isLazyFree_write8_of_false _ _ hlf_a⟩
  have hP_saved : ∀ a, InRegion (s0.sp - 144#64 + 0x40#64) 0x50 a →
      (m_pad.perm a).r = true ∧ m_pad.isLazyFree a = false :=
    fun a ha => hP_pad (hrw_fsp_s a (by unfold InRegion at ha ⊢; bv_omega))
  have hP_hm64 : ∀ a, InRegion (s0.readReg64 .x1) 64 a →
      (m_pad.perm a).r = true ∧ m_pad.isLazyFree a = false :=
    fun a ha => hP_pad (hrw_hm a (by unfold InRegion at ha ⊢; bv_omega))
  have hP_ist : ∀ a, InRegion (s0.readReg64 .x1 + 0x40#64) 32 a →
      (m_pad.perm a).r = true ∧ m_pad.isLazyFree a = false :=
    fun a ha => hP_pad (hrw_hm a (by unfold InRegion at ha ⊢; bv_omega))
  have hP_ost : ∀ a, InRegion (s0.readReg64 .x1 + 0x68#64) 32 a →
      (m_pad.perm a).r = true ∧ m_pad.isLazyFree a = false :=
    fun a ha => hP_pad (hrw_hm a (by unfold InRegion at ha ⊢; bv_omega))
  have hP_obl : ∀ a, InRegion (s0.readReg64 .x1 + 0x88#64) 8 a →
      (m_pad.perm a).r = true ∧ m_pad.isLazyFree a = false :=
    fun a ha => hP_pad (hrw_hm a (by unfold InRegion at ha ⊢; bv_omega))
  have hd_hm64_fsp : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  have hframe_sf : S2Frame s0.mem sf.mem
      [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)] := by
    have hag_pad : AgreesOutside s.mem m_pad
        (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) 1 := by
      dsimp only [m_pad]; agrees_outside_writes
    have hframe_pad : S2Frame s0.mem m_pad
        [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)] :=
      S2Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
        (by simp) (by have := hpre.tail_lt; bv_omega) hag_pad
    have hsf_frame' : S2Frame m_pad sf.mem [(dst, len)] := by
      simpa only [mem_setMem, arm64_norm] using hsf_frame
    refine hframe_pad.trans (hsf_frame'.mono fun a ha => ?_)
    intro r hr_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
    subst hr_mem
    have ha_hm := ha (s0.readReg64 .x1, 0x90) (by simp)
    have := hpre.tail_lt; dsimp only [dst, len]
    unfold OutsideRegion at ha_hm ⊢; bv_omega
  have hsf_ag' : AgreesOn
      (fun a => (m_pad.perm a).r = true ∧ m_pad.isLazyFree a = false)
      sf.mem (m_pad.writeBytes dst (List.replicate len 0#8)) := by
    simpa only [mem_setMem, arm64_norm] using hsf_ag
  refine
    { pc_eq := hsf_pc
      common :=
        { status := hsf_stat
          sp_eq := (CallingConventionPreserved.sp_eq hsf_cc).trans (by fin3_reg)
          x29_eq := (CallingConventionPreserved.x29 hsf_cc).trans (by fin3_reg)
          x26_eq := (CallingConventionPreserved.x26 hsf_cc).trans (by fin3_reg)
          x27_eq := (CallingConventionPreserved.x27 hsf_cc).trans (by fin3_reg)
          x28_eq := (CallingConventionPreserved.x28 hsf_cc).trans (by fin3_reg)
          saved := AgreesOn.finSaved_of hsf_ag' (FinSaved.of_agreesOutside hsaved hag_full hd_hm64_fsp) hP_saved
          frame := hframe_sf }
      x19_eq := (CallingConventionPreserved.x19 hsf_cc).trans (by fin3_reg)
      x20_eq := (CallingConventionPreserved.x20 hsf_cc).trans (by fin3_reg)
      x21_eq := (CallingConventionPreserved.x21 hsf_cc).trans (by fin3_reg)
      x22_eq := (CallingConventionPreserved.x22 hsf_cc).trans (by fin3_reg)
      x23_eq := (CallingConventionPreserved.x23 hsf_cc).trans (by fin3_reg)
      x24_eq := (CallingConventionPreserved.x24 hsf_cc).trans (by fin3_reg)
      x25_eq := (CallingConventionPreserved.x25 hsf_cc).trans (by dsimp only [len]; fin3_reg)
      buf_eq := (AgreesOn.readBytes_eq hsf_ag' (s0.readReg64 .x1) 64 (by decide) hP_hm64).trans
        (readBytes_64_after_pad_memset s.mem (s0.readReg64 .x1) tail hmsg_eq hpre.tail_lt)
      ist_eq := (AgreesOn.readBytes_eq hsf_ag' (s0.readReg64 .x1 + 0x40#64) 32 (by decide) hP_ist).trans
        ((hag_full.readBytes_eq hd_hm64_ist (by decide)).trans hin_eq)
      ost_eq := (AgreesOn.readBytes_eq hsf_ag' (s0.readReg64 .x1 + 0x68#64) 32 (by decide) hP_ost).trans
        ((hag_full.readBytes_eq hd_hm64_ost (by decide)).trans hout_eq)
      obl_eq := (AgreesOn.read64_eq hsf_ag' (s0.readReg64 .x1 + 0x88#64) hP_obl).trans
        ((hag_full.read64_eq hd_hm64_obl).trans hobl_eq) }

set_option maxHeartbeats 1600000 in
private theorem seg2a_placed_runsTo_sat {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF1_3Sat C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF2_3Sat C.F key pfx tail s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hult_7 := ult_7_of_lt_56 hpre.tail_lt
  obtain ⟨hbit_len1, hbit_len2⟩ := bit_len_innerN_eq (b := 1 + pfx.length / 64) hpre.tail_lt
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
    { pc_eq := by fin3_reg
      common :=
        { status := by fin3_reg, sp_eq := by fin3_reg, x29_eq := by fin3_reg,
          x26_eq := by fin3_reg, x27_eq := by fin3_reg, x28_eq := by fin3_reg,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg2a hsaved hag1 hag2 hag3 hd_fsp64_saved hd_hm64_saved
          frame := by rw [mem_setMem]; exact frame_seg2a_s2 hframe hag1 hag2 hag3 }
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
            ((hag1.read64_eq hd_fsp64_obl).trans hobl)) }

set_option maxHeartbeats 1600000 in
private theorem seg2b_placed_runsTo_sat {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF2_3Sat C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF3_3Sat C.F key pfx tail s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hblk, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_ist : s.mem.RW (s0.readReg64 .x1 + 0x40#64) 32 := hrw_hm.sub (by bv_omega)
  s2_step
  refine s2_compress256_step_425_sat C H
    (stPtr := s0.readReg64 .x1 + 0x40#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_425).base + 180#64)
    (st := (chunks64 pfx).foldl C.F (hmacInnerInit C.F key))
    (blk := innerLastBlockN (1 + pfx.length / 64) tail)
    hstat (by simp only [arm64_norm, lsCompress256Sym])
    (by fin3_reg) (by fin3_reg) (by fin3_reg) (by fin3_reg)
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
          frame := S2Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin3_reg, x20_eq := by fin3_reg, x21_eq := by fin3_reg, x22_eq := by fin3_reg
      ist_eq := by
        have hlen : blk_in.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact readBytes_writeBytes_same s.mem _ blk_in (by rw [hlen]; decide)
      ost_eq := (hag_comp.readBytes_eq hd_ist_ost (by decide)).trans host
      obl_eq := (hag_comp.read64_eq hd_ist_obl).trans hobl }

set_option maxHeartbeats 1600000 in
private theorem seg3a_placed_runsTo_sat {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF3_3Sat C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF3b_3Sat C.F key pfx tail s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp
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
  iterate 31 s2_step
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
          frame := by rw [mem_setMem]; exact frame_seg3a_s2 hframe hag1 hag2 hag3 hag4 }
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
        exact ost_eq_seg3a host hag1 hag2 hag3 hag4 hd_hm64_ost hd_fsp64_ost }

set_option maxHeartbeats 1600000 in
private theorem seg3b_placed_runsTo_sat {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF3b_3Sat C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF4_3Sat C.F key pfx tail s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hblk, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_ost : s.mem.RW (s0.readReg64 .x1 + 0x68#64) 32 := hrw_hm.sub (by bv_omega)
  set h_in := C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key))
    (innerLastBlockN (1 + pfx.length / 64) tail)
  s2_step
  refine s2_compress256_step_425_sat C H
    (stPtr := s0.readReg64 .x1 + 0x68#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_425).base + 308#64)
    (st := hmacOuterInit C.F key) (blk := outerBlock (digestBytes h_in))
    hstat (by simp only [arm64_norm, lsCompress256Sym])
    (by fin3_reg) (by fin3_reg) (by fin3_reg) (by fin3_reg)
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
          frame := S2Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin3_reg, x20_eq := by fin3_reg
      ost_eq := by
        have hlen : blk_out.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact readBytes_writeBytes_same s.mem _ blk_out (by rw [hlen]; decide) }

set_option maxHeartbeats 1600000 in
private theorem seg4a_placed_runsTo_sat {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF4_3Sat C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF5_3Sat C.F key pfx tail s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 32 := hframe.rw_of_rw _ _ hpre.rw_out
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_out := C.F (hmacOuterInit C.F key)
    (outerBlock (digestBytes (C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key))
      (innerLastBlockN (1 + pfx.length / 64) tail))))
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_104_of_shaStateBytes s.mem (s0.readReg64 .x1) h_out host
  have hzero64 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
  iterate 11 s2_step
  have hd_fsp64_hm := (seg4a_disj hpre).1
  have hread128 := read32_seg4a_mid s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 128#64 (h_out.get 6)
    (Or.inl rfl) hd_fsp64_hm hw6
  have hread132 := read32_seg4a_mid s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 132#64 (h_out.get 7)
    (Or.inr rfl) hd_fsp64_hm hw7
  iterate 2 s2_step
  clear hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hread128 hread132 hd_fsp64_hm host
  iterate 15 s2_step
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
          frame := by rw [mem_setMem]; exact frame_seg4a_s2 hframe hag1 hag2 hag3 hag4 }
      out_eq := by
        rw [mem_setMem]
        exact (readBytes_write32_8_digestBytes _ (s0.readReg64 .x0) h_out _ _ _ _ _ _ _ _
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)).trans
          (hmacWith_pfx_short C.F key pfx tail hpre.key_le hpre.hmac_st.1 hpre.tail_lt).symm }

set_option maxHeartbeats 1600000 in
private theorem seg4b_placed_runsTo_sat {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF5_3Sat C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (FinPostSat C.F key (pfx ++ tail) s0) := by
  rcases hs with ⟨hpc, hcom, hout⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  rcases hsaved with ⟨hs29, hslr, hs25, hs24, hs23, hs22, hs21, hs20, hs19⟩
  have hs29' : s.mem.read64 (s0.sp - 144#64 + 64#64) = s0.readReg64 .x29 := hs29
  have hs25' : s.mem.read64 (s0.sp - 144#64 + 80#64) = s0.readReg64 .x25 := hs25
  have hs24' : s.mem.read64 (s0.sp - 144#64 + 96#64) = s0.readReg64 .x24 := hs24
  have hs23' : s.mem.read64 (s0.sp - 144#64 + 104#64) = s0.readReg64 .x23 := hs23
  have hs22' : s.mem.read64 (s0.sp - 144#64 + 112#64) = s0.readReg64 .x22 := hs22
  have hs21' : s.mem.read64 (s0.sp - 144#64 + 120#64) = s0.readReg64 .x21 := hs21
  have hs20' : s.mem.read64 (s0.sp - 144#64 + 128#64) = s0.readReg64 .x20 := hs20
  have hs19' : s.mem.read64 (s0.sp - 144#64 + 136#64) = s0.readReg64 .x19 := hs19
  have hslr' : s.mem.read64 (s0.sp - 144#64 + 72#64) = s0.readReg64 .lr := hslr
  iterate 7 s2_step
  refine RunsTo.refl ⟨by simp (config := { decide := true }) only [arm64_norm], hstat,
    ⟨by simp (config := { decide := true }) only [arm64_norm], fun r hr => ?_⟩, hout, hframe⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [arm64_norm, hx26, hx27, hx28]

public theorem finalize_fixed3_pfx_placed_runsTo_sat {key pfx tail : List (BitVec 8)} {s0 : State}
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s0 (FinPostSat C.F key (pfx ++ tail) s0) :=
  (seg1a_placed_runsTo_sat hpre).trans fun _ hs1 =>
  (seg1b_placed_runsTo_sat hpre hs1).trans fun _ hs2 =>
  (seg2a_placed_runsTo_sat hpre hs2).trans fun _ hs3 =>
  (seg2b_placed_runsTo_sat hpre hs3).trans fun _ hs4 =>
  (seg3a_placed_runsTo_sat hpre hs4).trans fun _ hs5 =>
  (seg3b_placed_runsTo_sat hpre hs5).trans fun _ hs6 =>
  (seg4a_placed_runsTo_sat hpre hs6).trans fun _ hs7 =>
  seg4b_placed_runsTo_sat hpre hs7

public theorem finalize_fixed3_placed_runsTo_sat {key msg : List (BitVec 8)} {s0 : State}
    (hpre : FinPre3 fin3PlacedFakeB C.F key msg s0) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s0 (FinPostSat C.F key msg s0) :=
  @finalize_fixed3_pfx_placed_runsTo_sat _ C H _ key [] msg s0 hpre.to_pfx

public theorem finalize_fixed3_pfx_placed_runsTo_of_other_block_sat {callerProg : Program} {i : Nat}
    [hcaller : IsLsBlockProg callerProg i H]
    {key pfx tail : List (BitVec 8)} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpre : FinPre3Pfx fin3PlacedFakeB C.F key pfx tail s0)
    (hi : i < 619 := by decide) :
    RunsTo callerProg s0 (FinPostSat C.F key (pfx ++ tail) s0) :=
  RunsTo.of_other_block hcl (finalize_fixed3_pfx_placed_runsTo_sat hpre) hi (by decide) (by decide)

public theorem finalize_fixed3_placed_runsTo_of_other_block_sat {callerProg : Program} {i : Nat}
    [hcaller : IsLsBlockProg callerProg i H]
    {key msg : List (BitVec 8)} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpre : FinPre3 fin3PlacedFakeB C.F key msg s0)
    (hi : i < 619 := by decide) :
    RunsTo callerProg s0 (FinPostSat C.F key msg s0) :=
  RunsTo.of_other_block hcl (finalize_fixed3_placed_runsTo_sat hpre) hi (by decide) (by decide)

end PlacedSat

/-! ## 4. Separation-Logic Contract (`finalize_fixed3_placed_ok_sat` : `FinalizeFixed3PlacedOk C H`) -/

/-- Relocatable `FinalizeFixed3PlacedOk C H` contract for `finalize_fixed` (Block `425`) under
`[HkdfPlacedHooksExactSat C.F H]` (sibling of `finalize_fixed3_placed_ok`). -/
public theorem finalize_fixed3_placed_ok_sat [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooksExactSat C.F H] :
    FinalizeFixed3PlacedOk C H := by
  unfold FinalizeFixed3PlacedOk
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  rw [finalizeFixedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hkey_le, hmsg_lt⟩, hsep⟩
  have hmsg_lt64 : x.msg.length < 64 := by omega
  have hb_out := IsBlock.memRegion x.out 32
  have hb_hm := isBlock_hmacCoreAt C.F x.hm x.key x.msg hmsg_lt64
  have hb_stk := IsBlock.memRegion (s0.sp - 144#64) 144
  change (s0.mem ⊨
    (memRegion x.out 32 ∗ hmacCoreAt C.F x.hm x.key x.msg ∗ memRegion (s0.sp - 144#64) 144) ∗ R) at hsep
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
  have hfin_pre : FinPre3 fin3PlacedFakeB C.F x.key x.msg s0 :=
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
  refine (finalize_fixed3_placed_runsTo_sat (C := C) (H := H) hfin_pre).to_reaches_pc
    fun sf hpost _ _ htr => ?_
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
    S2Frame.update_three_blocks hb_out hb_out' hb_hm hb_hm' hb_stk hb_stk hsep_out hframe_sf
      ⟨by rw [length_hmacWith]; decide, by rwa [length_hmacWith]⟩ trivial trivial
  change (sf.mem ⊨
    ((x.out ↦ₛ hmacWith C.F x.key x.msg) ∗ memRegion x.hm 0x90 ∗ memRegion (s0.sp - 144#64) 144) ∗ R)
  ac_nf at hpost_sep ⊢

public theorem finalize_fixed3_placed_ok_withLsCodeLoaded_sat [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooksExactSat C.F H] :
    subroutine_ok ((blkPC_425).rebase (blkPl_425).base H) (blkPl_425).base
      (withLsCodeLoaded lsmpl (finalizeFixedSpec C.F)) :=
  subroutine_ok_withLsCodeLoaded_of_plain (finalize_fixed3_placed_ok_sat C H)

end LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedSat
