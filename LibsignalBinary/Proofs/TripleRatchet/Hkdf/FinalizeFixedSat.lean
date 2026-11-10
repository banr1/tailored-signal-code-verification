/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt

/-!
# `HookSat` Relocatable Verification of `finalize_fixed`

Establishes `S2Frame`-framed `RunsTo` and `FinalizeFixedPlacedOk` contracts for
`Hmac<Sha256>::finalize_fixed` under `[HkdfPlacedHooksSat C.F H]`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   lsmpl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved FinalizeFixedPlacedOk FinSaved Frame HmacSt
   RW RunsTo TraceEq agreesOutside_pad_memset agreesOutside_seg2a agreesOutside_seg3a agreesOutside_seg4a
   bit_len_inner_eq blkPC_123 blkPl_123 digestBytes digestBytes_eq_append finalizeFixedSpec
   finPlacedFakeB finPlacedFakeB_off_0 finSaved_seg3a finSaved_seg4a frame_seg2a frame_seg3a
   frame_seg4a fsp_aligned hmacCoreAt hmacInnerInit hmacOuterInit hmacWith_short innerLastBlock
   innerLastBlock_length isBlock_hmacCoreAt length_hmacWith outerBlock outerBlock_digestBytes_length
   read32_words_at_104_of_shaStateBytes read32_words_at_64_of_shaStateBytes
   read64_seg2a_mid read64_seg3a_pad_32 read64_seg3a_pad_40 readBytes_56_eq_append_8
   readBytes_56_of_buf_eq readBytes_64_after_pad_memset readBytes_fsp_64_seg2
   readBytes_fsp_64_seg3 readBytes_write32_8_digestBytes shaStateBytes_length
   toLEBytes_4_rev32 toLEBytes_8_read64 toLEBytes_8_rev32_append toLEBytes_8_rev64
   ult_7_of_lt_56 xor_63_of_lt_64 zeroExtend64_ofNat8
   zeroExtend64_truncate32_ofNat64)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (CallingConventionPreserved.x19 CallingConventionPreserved.x20
   CallingConventionPreserved.x21 CallingConventionPreserved.x22
   CallingConventionPreserved.x27 CallingConventionPreserved.x29 S2Frame)
open CryptoVerification.LibsignalTripleRatchet.FinalizeFixedProof (FinPre)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
  (AgreesOn.finSaved_of AgreesOn.read64_eq AgreesOn.readBytes_eq S2Frame.trans_agreesOutside
   S2Frame.trans_agreesOutside_sub S2Frame.update_three_blocks)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt.FinX (read32_seg4a_mid_x)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (CallingConventionPreserved.x23 CallingConventionPreserved.x24 CallingConventionPreserved.x25
   CallingConventionPreserved.x26 CallingConventionPreserved.x28 HkdfPlacedHooksExactSat
   s2_compress256_step_placed_sat_exact s2_memset_step_placed_sat_exact)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

private theorem seg4a_disj {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {key msg : List (BitVec 8)} {s0 : State} (hpre : FinPre b F key msg s0) :
    DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1) 0x90 ∧
    DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64 + 0x40#64) 0x50 ∧
    DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 ∧
    DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
  ⟨hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩,
   hpre.disj_hm_fsp.sub_right _ ⟨by decide, by bv_omega⟩,
   by unfold DisjointRegions; bv_omega,
   hpre.disj_out_fsp.sub_right _ ⟨by decide, by bv_omega⟩⟩

private theorem mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

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

local macro "solve_fin_saved_sat" : tactic =>
  `(tactic| (
    try rw [mem_setMem]
    simp (config := { decide := true }) only [arm64_norm]))

local macro "fin_reg_sat" : tactic =>
  `(tactic| (
    try rw [State.readReg64_setMem]
    try rw [State.pc_setMem]
    try rw [State.sp_setMem]
    try rw [State.status_setMem]
    simp (config := { decide := true }) only [arm64_norm, *]))

/-! ## `S2Frame`-Framed Cut Predicates -/

/-- `S2Frame`-framed common state invariant for `finalize_fixed` (`144` B stack). -/
public structure FinCommonSat (s0 s : State) : Prop where
  status : s.status = .Running
  sp_eq  : s.sp = s0.sp - 144#64
  x29_eq : s.readReg64 .x29 = s0.sp - 144#64 + 0x40#64
  x26_eq : s.readReg64 .x26 = s0.readReg64 .x26
  x27_eq : s.readReg64 .x27 = s0.readReg64 .x27
  x28_eq : s.readReg64 .x28 = s0.readReg64 .x28
  saved  : FinSaved s0 (s0.sp - 144#64) s.mem
  frame  : S2Frame s0.mem s.mem
    [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)]

/-- `S2Frame`-framed postcondition of `finalize_fixed` at return (`s'.pc = s0.readReg64 .lr`). -/
@[expose] public def FinPostSat (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s' : State) : Prop :=
  s'.pc = s0.readReg64 .lr ∧
  s'.status = .Running ∧
  CalleeSaved s0 s' ∧
  s'.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key msg ∧
  S2Frame s0.mem s'.mem
    [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)]

private structure StateF0pSat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 28#64
  common  : FinCommonSat s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x0
  x1_eq   : s.readReg64 .x1 = s0.readReg64 .x1
  hmac_st : HmacSt s.mem (s0.readReg64 .x1) F key msg

private structure StateF1Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 76#64
  common  : FinCommonSat s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 msg.length
  x24_eq  : s.readReg64 .x24 = 1#64
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 (63 - msg.length)
  buf_eq  : s.mem.readBytes (s0.readReg64 .x1) 64 =
    msg ++ [0x80#8] ++ List.replicate (63 - msg.length) 0#8
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 = shaStateBytes (hmacInnerInit F key)
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateF2Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 176#64
  common  : FinCommonSat s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 = innerLastBlock msg
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 = shaStateBytes (hmacInnerInit F key)
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateF3Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 180#64
  common  : FinCommonSat s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes (F (hmacInnerInit F key) (innerLastBlock msg))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateF3bSat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 304#64
  common  : FinCommonSat s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 =
    outerBlock (digestBytes (F (hmacInnerInit F key) (innerLastBlock msg)))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)

private structure StateF4Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 308#64
  common  : FinCommonSat s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 =
    shaStateBytes (F (hmacOuterInit F key)
      (outerBlock (digestBytes (F (hmacInnerInit F key) (innerLastBlock msg)))))

private structure StateF5Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 420#64
  common : FinCommonSat s0 s
  out_eq : s.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key msg

/-! ## Placed Segment Proofs (`[HkdfPlacedHooksExactSat C.F H]`) -/

section PlacedSat

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksExactSat C.F H]

private theorem seg1a_placed_runsTo_sat {key msg : List (BitVec 8)} {s0 : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s0 (StateF0pSat C.F key msg s0) := by
  have hpc : s0.pc = (blkPl_123).base := by simpa only [finPlacedFakeB_off_0] using hpre.pc_eq
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
    { pc_eq := by fin_reg_sat
      common :=
        { status := by fin_reg_sat, sp_eq := by fin_reg_sat, x29_eq := by fin_reg_sat,
          x26_eq := by fin_reg_sat, x27_eq := by fin_reg_sat, x28_eq := by fin_reg_sat,
          saved := ⟨by solve_fin_saved_sat, by solve_fin_saved_sat, by solve_fin_saved_sat,
                    by solve_fin_saved_sat, by solve_fin_saved_sat, by solve_fin_saved_sat,
                    by solve_fin_saved_sat, by solve_fin_saved_sat, by solve_fin_saved_sat⟩
          frame := by
            rw [mem_setMem]
            exact S2Frame.trans_agreesOutside (S2Frame.refl s0.mem _) (by simp) hag }
      x0_eq := by fin_reg_sat
      x1_eq := by fin_reg_sat
      hmac_st := by rw [mem_setMem]; exact HmacSt.of_agreesOutside hpre.hmac_st hag hpre.disj_hm_fsp.symm }

private theorem seg1b_placed_runsTo_sat {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hs : StateF0pSat C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateF1Sat C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hhmac⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  rcases hhmac with ⟨hmsg_lt64, hmsg_eq, hpos_eq, hin_eq, hibl_eq, hout_eq, hobl_eq⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp
  have hcw_pos : s.mem.canWrite (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length) 1 = true :=
    hrw_hm.canWrite_sub (by bv_omega) (by decide)
  have hze32 := zeroExtend64_truncate32_ofNat64 hmsg_lt64
  have hze64 := zeroExtend64_ofNat8 hmsg_lt64
  have hxor63 := xor_63_of_lt_64 hmsg_lt64
  have hal_fsp : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  iterate 12 s2_step
  have htoNat_sub : (BitVec.ofNat 64 (63 - msg.length)).toNat = 63 - msg.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  set dst := s0.readReg64 .x1 + BitVec.ofNat 64 msg.length + 1#64
  set len := 63 - msg.length
  set m_pre := s.mem.write8 (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length) 128#8
  have hrw_memset : m_pre.RW dst len := by
    refine Memory.RW.of_perm_eq (by simp [m_pre]) (fun _ => Memory.isLazyFree_write8_of_false _ _)
      (hrw_hm.sub ?_)
    have := hpre.msg_lt; dsimp only [dst, len]; bv_omega
  refine s2_memset_step_placed_sat_exact C H
    (dst := dst) (lr := (blkPl_123).base + 76#64) (len := len)
    hstat rfl
    (by simp only [dst, arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simpa only [len, arm64_norm] using htoNat_sub)
    rfl (by simp only [arm64_norm, hsp]; exact hpre.sp_aligned) hrw_memset
    fun s2 htr2 hpc2 hstat2 hcc2 _ _ _ hs2_frame hag_on => ?_
  refine RunsTo.refl ?_ htr2
  have hag_pad : AgreesOutside s.mem (m_pre.writeBytes dst (List.replicate len 0#8))
      (s0.readReg64 .x1) 64 :=
    agreesOutside_pad_memset s.mem (s0.readReg64 .x1) msg hpre.msg_lt
  have hP_pre : ∀ {a : BitVec 64}, s.mem.permNoLazy a = some Perm.rw →
      (m_pre.perm a).r = true ∧ m_pre.isLazyFree a = false := by
    intro a hnl
    obtain ⟨hrw_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl
    exact ⟨by dsimp only [m_pre]; rw [Memory.perm_write8, hrw_a]; rfl,
      Memory.isLazyFree_write8_of_false _ _ hlf_a⟩
  have hP_saved : ∀ a, InRegion (s0.sp - 144#64 + 0x40#64) 0x50 a →
      (m_pre.perm a).r = true ∧ m_pre.isLazyFree a = false :=
    fun a ha => hP_pre (hrw_fsp a (by unfold InRegion at ha ⊢; bv_omega))
  have hP_hm64 : ∀ a, InRegion (s0.readReg64 .x1) 64 a →
      (m_pre.perm a).r = true ∧ m_pre.isLazyFree a = false :=
    fun a ha => hP_pre (hrw_hm a (by unfold InRegion at ha ⊢; bv_omega))
  have hP_ist : ∀ a, InRegion (s0.readReg64 .x1 + 0x40#64) 32 a →
      (m_pre.perm a).r = true ∧ m_pre.isLazyFree a = false :=
    fun a ha => hP_pre (hrw_hm a (by unfold InRegion at ha ⊢; bv_omega))
  have hP_ost : ∀ a, InRegion (s0.readReg64 .x1 + 0x68#64) 32 a →
      (m_pre.perm a).r = true ∧ m_pre.isLazyFree a = false :=
    fun a ha => hP_pre (hrw_hm a (by unfold InRegion at ha ⊢; bv_omega))
  have hP_obl : ∀ a, InRegion (s0.readReg64 .x1 + 0x88#64) 8 a →
      (m_pre.perm a).r = true ∧ m_pre.isLazyFree a = false :=
    fun a ha => hP_pre (hrw_hm a (by unfold InRegion at ha ⊢; bv_omega))
  have hd_hm64_fsp : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  have hframe_s2 : S2Frame s0.mem s2.mem
      [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)] := by
    have hag_pre : AgreesOutside s.mem m_pre (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length) 1 := by
      dsimp only [m_pre]; agrees_outside_writes
    have hf1 : S2Frame s0.mem m_pre
        [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)] := by
      have := hpre.msg_lt
      exact S2Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
        (by simp) (by bv_omega) hag_pre
    have hs2_frame' : S2Frame m_pre s2.mem [(dst, len)] := by
      simpa only [mem_setMem, arm64_norm] using hs2_frame
    refine hf1.trans (hs2_frame'.mono fun a ha => ?_)
    intro r hr_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
    subst hr_mem
    have ha_hm := ha (s0.readReg64 .x1, 0x90) (by simp)
    have := hpre.msg_lt; dsimp only [dst, len]
    unfold OutsideRegion at ha_hm ⊢; bv_omega
  have hag_on' : CryptoVerification.LibsignalTripleRatchet.HkdfExt.AgreesOn
      (fun a => (m_pre.perm a).r = true ∧ m_pre.isLazyFree a = false)
      s2.mem (m_pre.writeBytes dst (List.replicate len 0#8)) := by
    simpa only [mem_setMem, arm64_norm] using hag_on
  refine
    { pc_eq := hpc2
      common :=
        { status := hstat2
          sp_eq := (CallingConventionPreserved.sp_eq hcc2).trans (by fin_reg_sat)
          x29_eq := (CallingConventionPreserved.x29 hcc2).trans (by fin_reg_sat)
          x26_eq := (CallingConventionPreserved.x26 hcc2).trans (by fin_reg_sat)
          x27_eq := (CallingConventionPreserved.x27 hcc2).trans (by fin_reg_sat)
          x28_eq := (CallingConventionPreserved.x28 hcc2).trans (by fin_reg_sat)
          saved := AgreesOn.finSaved_of hag_on' (FinSaved.of_agreesOutside hsaved hag_pad hd_hm64_fsp) hP_saved
          frame := hframe_s2 }
      x19_eq := (CallingConventionPreserved.x19 hcc2).trans (by fin_reg_sat)
      x20_eq := (CallingConventionPreserved.x20 hcc2).trans (by fin_reg_sat)
      x21_eq := (CallingConventionPreserved.x21 hcc2).trans (by fin_reg_sat)
      x22_eq := (CallingConventionPreserved.x22 hcc2).trans (by fin_reg_sat)
      x23_eq := (CallingConventionPreserved.x23 hcc2).trans (by fin_reg_sat)
      x24_eq := (CallingConventionPreserved.x24 hcc2).trans (by fin_reg_sat)
      x25_eq := (CallingConventionPreserved.x25 hcc2).trans (by dsimp only [len]; fin_reg_sat)
      buf_eq := (AgreesOn.readBytes_eq hag_on' (s0.readReg64 .x1) 64 (by decide) hP_hm64).trans
        (readBytes_64_after_pad_memset s.mem (s0.readReg64 .x1) msg hmsg_eq hpre.msg_lt)
      ist_eq := (AgreesOn.readBytes_eq hag_on' (s0.readReg64 .x1 + 0x40#64) 32 (by decide) hP_ist).trans
        ((hag_pad.readBytes_eq hd_hm64_ist (by decide)).trans hin_eq)
      ost_eq := (AgreesOn.readBytes_eq hag_on' (s0.readReg64 .x1 + 0x68#64) 32 (by decide) hP_ost).trans
        ((hag_pad.readBytes_eq hd_hm64_ost (by decide)).trans hout_eq)
      obl_eq := (AgreesOn.read64_eq hag_on' (s0.readReg64 .x1 + 0x88#64) hP_obl).trans
        ((hag_pad.read64_eq hd_hm64_obl).trans hobl_eq) }

private theorem seg2a_placed_runsTo_sat {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hs : StateF1Sat C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateF2Sat C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hult_7 := ult_7_of_lt_56 hpre.msg_lt
  obtain ⟨hbit_len1, hbit_len2⟩ := bit_len_inner_eq hpre.msg_lt
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
    { pc_eq := by fin_reg_sat
      common :=
        { status := by fin_reg_sat, sp_eq := by fin_reg_sat, x29_eq := by fin_reg_sat,
          x26_eq := by fin_reg_sat, x27_eq := by fin_reg_sat, x28_eq := by fin_reg_sat,
          saved := by
            rw [mem_setMem]
            exact FinSaved.of_agreesOutside
              (FinSaved.of_agreesOutside (FinSaved.of_agreesOutside hsaved hag1 hd_fsp64_saved)
                hag2 hd_hm64_saved) hag3 hd_fsp64_saved
          frame := by
            rw [mem_setMem]
            exact hframe.trans (S2Frame.of_frame (frame_seg2a (Frame.refl s.mem _) hag1 hag2 hag3)) }
      x0_eq := by fin_reg_sat, x1_eq := by fin_reg_sat, x2_eq := by fin_reg_sat,
      x19_eq := by fin_reg_sat, x20_eq := by fin_reg_sat, x21_eq := by fin_reg_sat, x22_eq := by fin_reg_sat
      blk_eq := by
        rw [mem_setMem]
        refine (readBytes_fsp_64_seg2 _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
        rw [toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
            toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_rev64,
            readBytes_56_eq_append_8 s.mem (s0.readReg64 .x1),
            readBytes_56_of_buf_eq s.mem (s0.readReg64 .x1) msg hbuf hpre.msg_lt]
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

private theorem seg2b_placed_runsTo_sat {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hs : StateF2Sat C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateF3Sat C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hblk, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_ist : s.mem.RW (s0.readReg64 .x1 + 0x40#64) 32 := hrw_hm.sub (by bv_omega)
  s2_step
  refine s2_compress256_step_placed_sat_exact C H
    (stPtr := s0.readReg64 .x1 + 0x40#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_123).base + 180#64) (st := hmacInnerInit C.F key) (blk := innerLastBlock msg)
    hstat rfl
    (by fin_reg_sat) (by fin_reg_sat) (by fin_reg_sat) rfl
    hist hblk (innerLastBlock_length hpre.msg_lt) hrw_ist ?_
  refine RunsTo.refl ?_
  set blk_in := shaStateBytes (C.F (hmacInnerInit C.F key) (innerLastBlock msg))
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
    { pc_eq := by fin_reg_sat
      common :=
        { status := by fin_reg_sat, sp_eq := by fin_reg_sat, x29_eq := by fin_reg_sat,
          x26_eq := by fin_reg_sat, x27_eq := by fin_reg_sat, x28_eq := by fin_reg_sat,
          saved := FinSaved.of_agreesOutside hsaved hag_comp hd_ist_saved
          frame := S2Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin_reg_sat, x20_eq := by fin_reg_sat, x21_eq := by fin_reg_sat, x22_eq := by fin_reg_sat
      ist_eq := by
        have hlen : blk_in.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact readBytes_writeBytes_same s.mem _ blk_in (by rw [hlen]; decide)
      ost_eq := (hag_comp.readBytes_eq hd_ist_ost (by decide)).trans host
      obl_eq := (hag_comp.read64_eq hd_ist_obl).trans hobl }

private theorem seg3a_placed_runsTo_sat {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hs : StateF3Sat C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateF3bSat C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_in := C.F (hmacInnerInit C.F key) (innerLastBlock msg)
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
    { pc_eq := by fin_reg_sat
      common :=
        { status := by fin_reg_sat, sp_eq := by fin_reg_sat, x29_eq := by fin_reg_sat,
          x26_eq := by fin_reg_sat, x27_eq := by fin_reg_sat, x28_eq := by fin_reg_sat,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg3a hsaved hag1 hag2 hag3 hag4 hd_hm64_saved hd_fsp64_saved
          frame := by
            rw [mem_setMem]
            exact hframe.trans (S2Frame.of_frame (frame_seg3a (Frame.refl s.mem _) hag1 hag2 hag3 hag4)) }
      x0_eq := by fin_reg_sat, x1_eq := by fin_reg_sat, x2_eq := by fin_reg_sat,
      x19_eq := by fin_reg_sat, x20_eq := by fin_reg_sat
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

private theorem seg3b_placed_runsTo_sat {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hs : StateF3bSat C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateF4Sat C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hblk, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_ost : s.mem.RW (s0.readReg64 .x1 + 0x68#64) 32 := hrw_hm.sub (by bv_omega)
  set h_in := C.F (hmacInnerInit C.F key) (innerLastBlock msg)
  s2_step
  refine s2_compress256_step_placed_sat_exact C H
    (stPtr := s0.readReg64 .x1 + 0x68#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_123).base + 308#64) (st := hmacOuterInit C.F key) (blk := outerBlock (digestBytes h_in))
    hstat rfl
    (by fin_reg_sat) (by fin_reg_sat) (by fin_reg_sat) rfl
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
    { pc_eq := by fin_reg_sat
      common :=
        { status := by fin_reg_sat, sp_eq := by fin_reg_sat, x29_eq := by fin_reg_sat,
          x26_eq := by fin_reg_sat, x27_eq := by fin_reg_sat, x28_eq := by fin_reg_sat,
          saved := FinSaved.of_agreesOutside hsaved hag_comp hd_ost_saved
          frame := S2Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin_reg_sat, x20_eq := by fin_reg_sat
      ost_eq := by
        have hlen : blk_out.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact readBytes_writeBytes_same s.mem _ blk_out (by rw [hlen]; decide) }

private theorem seg4a_placed_runsTo_sat {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hs : StateF4Sat C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateF5Sat C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 32 := hframe.rw_of_rw _ _ hpre.rw_out
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_out := C.F (hmacOuterInit C.F key)
    (outerBlock (digestBytes (C.F (hmacInnerInit C.F key) (innerLastBlock msg))))
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_104_of_shaStateBytes s.mem (s0.readReg64 .x1) h_out host
  have hzero64 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
  iterate 11 s2_step
  have hd_fsp64_hm := (seg4a_disj hpre).1
  have hread128 := read32_seg4a_mid_x s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 128#64 (h_out.get 6)
    (Or.inl rfl) hd_fsp64_hm hw6
  have hread132 := read32_seg4a_mid_x s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 132#64 (h_out.get 7)
    (Or.inr rfl) hd_fsp64_hm hw7
  iterate 2 s2_step
  clear hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hread128 hread132 hd_fsp64_hm host
  iterate 15 s2_step
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg4a s.mem
    (s0.readReg64 .x0) (s0.readReg64 .x1) (s0.sp - 144#64) _ _ _ _ _ _ _ _
  obtain ⟨_, hd_hm_saved, hd_fsp64_saved, hd_out_saved⟩ := seg4a_disj hpre
  refine
    { pc_eq := by fin_reg_sat
      common :=
        { status := by fin_reg_sat, sp_eq := by fin_reg_sat, x29_eq := by fin_reg_sat,
          x26_eq := by fin_reg_sat, x27_eq := by fin_reg_sat, x28_eq := by fin_reg_sat,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg4a hsaved hag1 hag2 hag3 hag4 hd_hm_saved hd_fsp64_saved hd_out_saved
          frame := by
            rw [mem_setMem]
            exact hframe.trans (S2Frame.of_frame (frame_seg4a (Frame.refl s.mem _) hag1 hag2 hag3 hag4)) }
      out_eq := by
        rw [mem_setMem]
        exact (readBytes_write32_8_digestBytes _ (s0.readReg64 .x0) h_out _ _ _ _ _ _ _ _
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)).trans
          (hmacWith_short C.F key msg hpre.key_le hpre.msg_lt).symm }

private theorem seg4b_placed_runsTo_sat {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hs : StateF5Sat C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (FinPostSat C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hout⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp
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
  all_goals simp only [arm64_norm, hx26, hx27, hx28, hs19', hs20', hs21', hs22', hs23', hs24', hs25', hs29', hslr']

public theorem finalize_fixed_placed_runsTo_sat {key msg : List (BitVec 8)} {s0 : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s0 (FinPostSat C.F key msg s0) :=
  (seg1a_placed_runsTo_sat hpre).trans fun _ hs1 =>
  (seg1b_placed_runsTo_sat hpre hs1).trans fun _ hs2 =>
  (seg2a_placed_runsTo_sat hpre hs2).trans fun _ hs3 =>
  (seg2b_placed_runsTo_sat hpre hs3).trans fun _ hs4 =>
  (seg3a_placed_runsTo_sat hpre hs4).trans fun _ hs5 =>
  (seg3b_placed_runsTo_sat hpre hs5).trans fun _ hs6 =>
  (seg4a_placed_runsTo_sat hpre hs6).trans fun _ hs7 =>
  seg4b_placed_runsTo_sat hpre hs7

public theorem finalize_fixed_placed_runsTo_of_other_block_sat {callerProg : Program} {i : Nat}
    [hcaller : IsLsBlockProg callerProg i H]
    {key msg : List (BitVec 8)} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hi : i < 619 := by decide) :
    RunsTo callerProg s0 (FinPostSat C.F key msg s0) :=
  RunsTo.of_other_block hcl (finalize_fixed_placed_runsTo_sat hpre) hi (by decide) (by decide)

end PlacedSat

/-! ## Separation-Logic Contract -/

public theorem finalize_fixed_placed_ok_sat [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooksExactSat C.F H] :
    FinalizeFixedPlacedOk C H := by
  unfold FinalizeFixedPlacedOk
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
  have hfin_pre : FinPre finPlacedFakeB C.F x.key x.msg s0 :=
    { pc_eq := by rw [finPlacedFakeB_off_0]; exact hpc
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
  refine (finalize_fixed_placed_runsTo_sat (C := C) (H := H) hfin_pre).to_reaches_pc
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
  change sf.mem ⊨
    ((x.out ↦ₛ hmacWith C.F x.key x.msg) ∗ memRegion x.hm 0x90 ∗ memRegion (s0.sp - 144#64) 144) ∗ R
  ac_nf at hpost_sep ⊢

public theorem finalize_fixed_placed_ok_withLsCodeLoaded_sat [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooksExactSat C.F H] :
    subroutine_ok ((blkPC_123).rebase (blkPl_123).base H) (blkPl_123).base
      (withLsCodeLoaded lsmpl (finalizeFixedSpec C.F)) :=
  subroutine_ok_withLsCodeLoaded_of_plain (finalize_fixed_placed_ok_sat C H)

end LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat
