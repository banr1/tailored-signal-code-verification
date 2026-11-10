/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFin -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlacedA -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegs
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt
import LibsignalBinary.Specifications.LibsignalE2E.State -- shake: keep

/-!
# Relocatable Multi-Block `finalize_fixed` and Long-IKM `Hkdf::extract` under `HkdfPlacedHooksSat`

Proves relocatable `[LibsignalPlacement]` contracts for multi-block `finalize_fixed` (Block `123`)
and long-IKM `Hkdf::extract` (Block `54`, `x.salt = none`, `x.ikm.length ∈ {160, 192, 224}`) under
`[HkdfPlacedHooksExactSat C.F H]` with `S2Frame` memory framing.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlacedSat

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState chunks64 hmacWith toBEBytes)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl
   lsρ)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (EC88Long ECompLongPlaced EFinLongPlaced EMemcpyLongPlaced FinGenPre HmacStGen
   agreesOutside_writeBytes_sub_sp0 bit_len_inner_gen_eq compress256Hook_multi_eq
   fin_long_placed_runsTo hmacWith_gen innerLastBlockGen innerLastBlockGen_length
   nfs1_long_placed_runsTo seg0_long_placed_runsTo seg1a_long_placed_runsTo seg1c_long_placed_runsTo)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved ExtractGhost FinSaved Frame RW RunsTo RunsToFrom TraceEq agreesOutside_pad_memset
   agreesOutside_seg2a agreesOutside_seg3a agreesOutside_seg4a blkPC_123 blkPC_54 blkPl_123 blkPl_54
   digestBytes digestBytes_eq_append effectiveSalt extPlacedFakeB extPlacedFakeB_off_328
   extPlacedFakeB_off_380 finPlacedFakeB finPlacedFakeB_off_0 finSaved_seg3a finSaved_seg4a
   frame_seg2a frame_seg3a frame_seg4a fsp_aligned hmacInnerInit hmacOuterInit lsCompress256Sym
   lsMemcpySym ls_externAt?_of_mem newFromSliceSpec outerBlock outerBlock_digestBytes_length
   read32_words_at_104_of_shaStateBytes read32_words_at_64_of_shaStateBytes read64_seg2a_mid
   read64_seg3a_pad_32 read64_seg3a_pad_40 readBytes_56_eq_append_8 readBytes_56_of_buf_eq
   readBytes_64_after_pad_memset readBytes_fsp_64_seg2 readBytes_fsp_64_seg3
   readBytes_write32_8_digestBytes rw_of_perm_eq shaStateBytes_length toLEBytes_4_rev32
   toLEBytes_8_read64 toLEBytes_8_rev32_append toLEBytes_8_rev64 ult_7_of_lt_56 xor_63_of_lt_64
   zeroExtend64_ofNat8 zeroExtend64_truncate32_ofNat64)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (CallingConventionPreserved.x19 CallingConventionPreserved.x20
   CallingConventionPreserved.x21 CallingConventionPreserved.x22
   CallingConventionPreserved.x27 CallingConventionPreserved.x29 EPost ERetFin ExtCommon ExtFrame
   ExtSaved ExtSaved_and_Frame_of_agreesOutside_328 RunsTo.toE RunsToE S2Frame
   agreesOutside_sp0_write8 disj_sp0_off disj_sp0_sub_off effectiveSalt_length nfs2_placed_runsTo
   rw_stk_sub saltPtrOf seg2_placed_runsTo seg3_placed_runsTo sp0_aligned_0b1111)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
  (AgreesOn AgreesOn.finSaved_of AgreesOn.read64_eq AgreesOn.readBytes_eq
   S2Frame.trans_agreesOutside S2Frame.trans_agreesOutside_sub)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt.FinX (read32_seg4a_mid_x)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (applyMemcpyClobber)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (s2_memcpy_step_placed_of_exact)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (CallingConventionPreserved.x23 CallingConventionPreserved.x24 CallingConventionPreserved.x25
   CallingConventionPreserved.x26 CallingConventionPreserved.x28 HkdfPlacedHooksExactSat
   s2_compress256_step_placed_sat_exact s2_memset_step_placed_sat_exact)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat (FinCommonSat FinPostSat)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

private theorem mem_setMem_p (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

private theorem ost_eq_seg3a_p {m m1 m2 m3 m4 : Memory} {hm fsp : BitVec 64} {bs : List (BitVec 8)}
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

local macro "solve_fin_saved_p" : tactic =>
  `(tactic| (
    try rw [mem_setMem_p]
    simp (config := { decide := true }) only [arm64_norm]))

local macro "fin_reg_p" : tactic =>
  `(tactic| (
    try rw [State.readReg64_setMem]
    try rw [State.pc_setMem]
    try rw [State.sp_setMem]
    try rw [State.status_setMem]
    simp (config := { decide := true }) only [arm64_norm, *]))

/-! ## Multi-Block `compress256Hook` Step -/

public theorem s2_compress256_multi_step_placed_sat [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H] [hH : HkdfPlacedHooksExactSat C.F H]
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {nblk : ℕ} {st : ShaState} {blocks : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : (s.readReg64 .x2).toNat = nblk)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr (64 * nblk) = blocks)
    (hrw : s.mem.RW stPtr 32)
    (h : RunsToFrom prog s₀
      ((s.setMem (s.mem.writeBytes stPtr
        (shaStateBytes ((chunks64 blocks).foldl C.F st)))).setPC lr) Q)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q := by
  have hcan :
      s.mem.canWrite stPtr (shaStateBytes ((chunks64 blocks).foldl C.F st)).length = true := by
    rw [shaStateBytes_length]
    exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : prog.externAt? s.pc = some (compress256Hook C.F) := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hH.compress256]
  have hstate := compress256Hook_multi_eq C.F hx0 hx1 hx2 hlr hst hblk
  have hkeep : s.mem.KeepsFrozen (compress256Hook C.F s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (compress256Hook C.F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

/-! ## Relocatable `finalize_fixed` (Block `123`) for `HmacStGen` -/

section PlacedGenFinSat

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksExactSat C.F H]

private structure StateGF0pPlacedSat (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 28#64
  common  : FinCommonSat s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x0
  x1_eq   : s.readReg64 .x1 = s0.readReg64 .x1
  hmac_st : HmacStGen s.mem (s0.readReg64 .x1) F key blocks rem

private structure StateGF1PlacedSat (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 76#64
  common  : FinCommonSat s0 s
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

private structure StateGF2PlacedSat (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 176#64
  common  : FinCommonSat s0 s
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

private structure StateGF3PlacedSat (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 180#64
  common  : FinCommonSat s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes
      (F ((chunks64 blocks).foldl F (hmacInnerInit F key)) (innerLastBlockGen blocks rem))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateGF3bPlacedSat (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 304#64
  common  : FinCommonSat s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 =
    outerBlock (digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
      (innerLastBlockGen blocks rem)))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)

private structure StateGF4PlacedSat (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 308#64
  common  : FinCommonSat s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 =
    shaStateBytes (F (hmacOuterInit F key)
      (outerBlock (digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
        (innerLastBlockGen blocks rem)))))

private structure StateGF5PlacedSat (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 420#64
  common : FinCommonSat s0 s
  out_eq : s.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key (blocks ++ rem)

private theorem gseg1a_placed_runsTo_sat {key blocks rem : List (BitVec 8)} {s0 : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s0 (StateGF0pPlacedSat C.F key blocks rem s0) := by
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
      (s0.sp - 144#64) 144 := by agrees_outside_writes
  refine
    { pc_eq := by fin_reg_p
      common :=
        { status := by fin_reg_p, sp_eq := by fin_reg_p, x29_eq := by fin_reg_p,
          x26_eq := by fin_reg_p, x27_eq := by fin_reg_p, x28_eq := by fin_reg_p,
          saved := ⟨by solve_fin_saved_p, by solve_fin_saved_p, by solve_fin_saved_p,
                    by solve_fin_saved_p, by solve_fin_saved_p, by solve_fin_saved_p,
                    by solve_fin_saved_p, by solve_fin_saved_p, by solve_fin_saved_p⟩
          frame := by
            rw [mem_setMem_p]
            exact S2Frame.trans_agreesOutside (S2Frame.refl s0.mem _) (by simp) hag }
      x0_eq := by fin_reg_p, x1_eq := by fin_reg_p
      hmac_st := by rw [mem_setMem_p]; exact HmacStGen.of_agreesOutside hpre.hmac_st hag hpre.disj_hm_fsp.symm }

private theorem gseg1b_placed_runsTo_sat {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF0pPlacedSat C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateGF1PlacedSat C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hhmac⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  rcases hhmac with ⟨hmod, hblk_le, hmsg_lt64, hmsg_eq, hpos_eq, hin_eq, hibl_eq, hout_eq, hobl_eq⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp
  have hcw_pos : s.mem.canWrite (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 1 = true :=
    hrw_hm.canWrite_sub (by bv_omega) (by decide)
  have hze32 := zeroExtend64_truncate32_ofNat64 hmsg_lt64
  have hze64 := zeroExtend64_ofNat8 hmsg_lt64
  have hxor63 := xor_63_of_lt_64 hmsg_lt64
  iterate 12 s2_step
  have htoNat_sub : (BitVec.ofNat 64 (63 - rem.length)).toNat = 63 - rem.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  set dst := s0.readReg64 .x1 + BitVec.ofNat 64 rem.length + 1#64
  set len := 63 - rem.length
  set m_pre := s.mem.write8 (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 128#8
  have hrw_memset : m_pre.RW dst len := by
    refine Memory.RW.of_perm_eq (by simp [m_pre]) (fun _ => Memory.isLazyFree_write8_of_false _ _)
      (hrw_hm.sub ?_)
    have := hpre.rem_lt; dsimp only [dst, len]; bv_omega
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
    agreesOutside_pad_memset s.mem (s0.readReg64 .x1) rem hpre.rem_lt
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
    have hag_pre : AgreesOutside s.mem m_pre (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 1 := by
      dsimp only [m_pre]; agrees_outside_writes
    have hf1 : S2Frame s0.mem m_pre
        [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)] := by
      have := hpre.rem_lt
      exact S2Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
        (by simp) (by bv_omega) hag_pre
    have hs2_frame' : S2Frame m_pre s2.mem [(dst, len)] := by
      simpa only [mem_setMem_p, arm64_norm] using hs2_frame
    refine hf1.trans (hs2_frame'.mono fun a ha => ?_)
    intro r hr_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
    subst hr_mem
    have ha_hm := ha (s0.readReg64 .x1, 0x90) (by simp)
    have := hpre.rem_lt; dsimp only [dst, len]
    unfold OutsideRegion at ha_hm ⊢; bv_omega
  have hag_on' : AgreesOn
      (fun a => (m_pre.perm a).r = true ∧ m_pre.isLazyFree a = false)
      s2.mem (m_pre.writeBytes dst (List.replicate len 0#8)) := by
    simpa only [mem_setMem_p, arm64_norm] using hag_on
  refine
    { pc_eq := hpc2
      common :=
        { status := hstat2
          sp_eq := (CallingConventionPreserved.sp_eq hcc2).trans (by fin_reg_p)
          x29_eq := (CallingConventionPreserved.x29 hcc2).trans (by fin_reg_p)
          x26_eq := (CallingConventionPreserved.x26 hcc2).trans (by fin_reg_p)
          x27_eq := (CallingConventionPreserved.x27 hcc2).trans (by fin_reg_p)
          x28_eq := (CallingConventionPreserved.x28 hcc2).trans (by fin_reg_p)
          saved := AgreesOn.finSaved_of hag_on' (FinSaved.of_agreesOutside hsaved hag_pad hd_hm64_fsp) hP_saved
          frame := hframe_s2 }
      x19_eq := (CallingConventionPreserved.x19 hcc2).trans (by fin_reg_p)
      x20_eq := (CallingConventionPreserved.x20 hcc2).trans (by fin_reg_p)
      x21_eq := (CallingConventionPreserved.x21 hcc2).trans (by fin_reg_p)
      x22_eq := (CallingConventionPreserved.x22 hcc2).trans (by fin_reg_p)
      x23_eq := (CallingConventionPreserved.x23 hcc2).trans (by fin_reg_p)
      x24_eq := (CallingConventionPreserved.x24 hcc2).trans (by fin_reg_p)
      x25_eq := (CallingConventionPreserved.x25 hcc2).trans (by dsimp only [len]; fin_reg_p)
      buf_eq := (AgreesOn.readBytes_eq hag_on' (s0.readReg64 .x1) 64 (by decide) hP_hm64).trans
        (readBytes_64_after_pad_memset s.mem (s0.readReg64 .x1) rem hmsg_eq hpre.rem_lt)
      ist_eq := (AgreesOn.readBytes_eq hag_on' (s0.readReg64 .x1 + 0x40#64) 32 (by decide) hP_ist).trans
        ((hag_pad.readBytes_eq hd_hm64_ist (by decide)).trans hin_eq)
      ost_eq := (AgreesOn.readBytes_eq hag_on' (s0.readReg64 .x1 + 0x68#64) 32 (by decide) hP_ost).trans
        ((hag_pad.readBytes_eq hd_hm64_ost (by decide)).trans hout_eq)
      obl_eq := (AgreesOn.read64_eq hag_on' (s0.readReg64 .x1 + 0x88#64) hP_obl).trans
        ((hag_pad.read64_eq hd_hm64_obl).trans hobl_eq) }

set_option maxHeartbeats 800000 in
private theorem gseg2a_placed_runsTo_sat {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF1PlacedSat C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateGF2PlacedSat C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp
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
    { pc_eq := by fin_reg_p
      common :=
        { status := by fin_reg_p, sp_eq := by fin_reg_p, x29_eq := by fin_reg_p,
          x26_eq := by fin_reg_p, x27_eq := by fin_reg_p, x28_eq := by fin_reg_p,
          saved := by
            rw [mem_setMem_p]
            exact FinSaved.of_agreesOutside
              (FinSaved.of_agreesOutside (FinSaved.of_agreesOutside hsaved hag1 hd_fsp64_saved)
                hag2 hd_hm64_saved) hag3 hd_fsp64_saved
          frame := by
            rw [mem_setMem_p]
            exact hframe.trans (S2Frame.of_frame (frame_seg2a (Frame.refl s.mem _) hag1 hag2 hag3)) }
      x0_eq := by fin_reg_p, x1_eq := by fin_reg_p, x2_eq := by fin_reg_p,
      x19_eq := by fin_reg_p, x20_eq := by fin_reg_p, x21_eq := by fin_reg_p, x22_eq := by fin_reg_p
      blk_eq := by
        rw [mem_setMem_p]
        refine (readBytes_fsp_64_seg2 _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
        rw [toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
            toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_rev64,
            readBytes_56_eq_append_8 s.mem (s0.readReg64 .x1),
            readBytes_56_of_buf_eq s.mem (s0.readReg64 .x1) rem hbuf hpre.rem_lt,
            bit_len_inner_gen_eq hpre.hmac_st.1 hpre.hmac_st.2.1 hpre.rem_lt]
        rfl
      ist_eq := by
        rw [mem_setMem_p]
        exact (hag3.readBytes_eq hd_fsp64_ist (by decide)).trans
          ((hag2.readBytes_eq hd_hm64_ist (by decide)).trans
            ((hag1.readBytes_eq hd_fsp64_ist (by decide)).trans hist))
      ost_eq := by
        rw [mem_setMem_p]
        exact (hag3.readBytes_eq hd_fsp64_ost (by decide)).trans
          ((hag2.readBytes_eq hd_hm64_ost (by decide)).trans
            ((hag1.readBytes_eq hd_fsp64_ost (by decide)).trans host))
      obl_eq := by
        rw [mem_setMem_p]
        exact (hag3.read64_eq hd_fsp64_obl).trans
          ((hag2.read64_eq hd_hm64_obl).trans
            ((hag1.read64_eq hd_fsp64_obl).trans hobl)) }

private theorem gseg2b_placed_runsTo_sat {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF2PlacedSat C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateGF3PlacedSat C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hblk, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_ist : s.mem.RW (s0.readReg64 .x1 + 0x40#64) 32 := hrw_hm.sub (by bv_omega)
  s2_step
  refine s2_compress256_step_placed_sat_exact C H
    (stPtr := s0.readReg64 .x1 + 0x40#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_123).base + 180#64) (st := (chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
    (blk := innerLastBlockGen blocks rem)
    hstat rfl
    (by fin_reg_p) (by fin_reg_p) (by fin_reg_p) rfl
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
    { pc_eq := by fin_reg_p
      common :=
        { status := by fin_reg_p, sp_eq := by fin_reg_p, x29_eq := by fin_reg_p,
          x26_eq := by fin_reg_p, x27_eq := by fin_reg_p, x28_eq := by fin_reg_p,
          saved := FinSaved.of_agreesOutside hsaved hag_comp hd_ist_saved
          frame := S2Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin_reg_p, x20_eq := by fin_reg_p, x21_eq := by fin_reg_p, x22_eq := by fin_reg_p
      ist_eq := by
        have hlen : blk_in.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact readBytes_writeBytes_same s.mem _ blk_in (by rw [hlen]; decide)
      ost_eq := (hag_comp.readBytes_eq hd_ist_ost (by decide)).trans host
      obl_eq := (hag_comp.read64_eq hd_ist_obl).trans hobl }

set_option maxHeartbeats 800000 in
private theorem gseg3a_placed_runsTo_sat {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF3PlacedSat C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateGF3bPlacedSat C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_in := C.F ((chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
    (innerLastBlockGen blocks rem)
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_64_of_shaStateBytes s.mem (s0.readReg64 .x1) h_in hist
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hrev768 : rev64 (256#64 ||| 512#64) = (3#64 <<< 48) := by decide
  have hread32 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
    read64_seg3a_pad_32 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
  have hread40 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
    read64_seg3a_pad_40 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
  iterate 31 s2_step
  clear hread32 hread40 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hist
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg3a s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
    _ _ _ _ _ _ _ _ _ _ _ _ 0#64 (3#64 <<< 48) 0x80#64 0#64 0#64 (3#64 <<< 48)
  have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  refine
    { pc_eq := by fin_reg_p
      common :=
        { status := by fin_reg_p, sp_eq := by fin_reg_p, x29_eq := by fin_reg_p,
          x26_eq := by fin_reg_p, x27_eq := by fin_reg_p, x28_eq := by fin_reg_p,
          saved := by
            rw [mem_setMem_p]
            exact finSaved_seg3a hsaved hag1 hag2 hag3 hag4 hd_hm64_saved hd_fsp64_saved
          frame := by
            rw [mem_setMem_p]
            exact hframe.trans (S2Frame.of_frame (frame_seg3a (Frame.refl s.mem _) hag1 hag2 hag3 hag4)) }
      x0_eq := by fin_reg_p, x1_eq := by fin_reg_p, x2_eq := by fin_reg_p,
      x19_eq := by fin_reg_p, x20_eq := by fin_reg_p
      blk_eq := by
        rw [mem_setMem_p]
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
        rw [mem_setMem_p]
        exact ost_eq_seg3a_p host hag1 hag2 hag3 hag4 hd_hm64_ost hd_fsp64_ost }

private theorem gseg3b_placed_runsTo_sat {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF3bPlacedSat C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateGF4PlacedSat C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hblk, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_ost : s.mem.RW (s0.readReg64 .x1 + 0x68#64) 32 := hrw_hm.sub (by bv_omega)
  set h_in := C.F ((chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
    (innerLastBlockGen blocks rem)
  s2_step
  refine s2_compress256_step_placed_sat_exact C H
    (stPtr := s0.readReg64 .x1 + 0x68#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_123).base + 308#64) (st := hmacOuterInit C.F key) (blk := outerBlock (digestBytes h_in))
    hstat rfl
    (by fin_reg_p) (by fin_reg_p) (by fin_reg_p) rfl
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
    { pc_eq := by fin_reg_p
      common :=
        { status := by fin_reg_p, sp_eq := by fin_reg_p, x29_eq := by fin_reg_p,
          x26_eq := by fin_reg_p, x27_eq := by fin_reg_p, x28_eq := by fin_reg_p,
          saved := FinSaved.of_agreesOutside hsaved hag_comp hd_ost_saved
          frame := S2Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin_reg_p, x20_eq := by fin_reg_p
      ost_eq := by
        have hlen : blk_out.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact readBytes_writeBytes_same s.mem _ blk_out (by rw [hlen]; decide) }

private theorem gseg4a_disj_p {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
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
private theorem extractLsb'_0_64_zero128_p : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl

@[local simp, local arm64_norm]
private theorem extractLsb'_64_64_zero128_p : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl

set_option maxHeartbeats 800000 in
private theorem gseg4a_placed_runsTo_sat {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF4PlacedSat C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateGF5PlacedSat C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 32 := hframe.rw_of_rw _ _ hpre.rw_out
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_out := C.F (hmacOuterInit C.F key)
    (outerBlock (digestBytes (C.F ((chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
      (innerLastBlockGen blocks rem))))
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_104_of_shaStateBytes s.mem (s0.readReg64 .x1) h_out host
  have hzero64 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
  iterate 11 s2_step
  have hd_fsp64_hm := (gseg4a_disj_p hpre).1
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
  obtain ⟨_, hd_hm_saved, hd_fsp64_saved, hd_out_saved⟩ := gseg4a_disj_p hpre
  refine
    { pc_eq := by fin_reg_p
      common :=
        { status := by fin_reg_p, sp_eq := by fin_reg_p, x29_eq := by fin_reg_p,
          x26_eq := by fin_reg_p, x27_eq := by fin_reg_p, x28_eq := by fin_reg_p,
          saved := by
            rw [mem_setMem_p]
            exact finSaved_seg4a hsaved hag1 hag2 hag3 hag4 hd_hm_saved hd_fsp64_saved hd_out_saved
          frame := by
            rw [mem_setMem_p]
            exact hframe.trans (S2Frame.of_frame (frame_seg4a (Frame.refl s.mem _) hag1 hag2 hag3 hag4)) }
      out_eq := by
        rw [mem_setMem_p]
        exact (readBytes_write32_8_digestBytes _ (s0.readReg64 .x0) h_out _ _ _ _ _ _ _ _
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
          (toLEBytes_4_rev32 _)).trans
          (hmacWith_gen C.F key blocks rem hpre.key_le hpre.hmac_st.1 hpre.rem_lt).symm }

private theorem gseg4b_placed_runsTo_sat {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF5PlacedSat C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s
      (FinPostSat C.F key (blocks ++ rem) s0) := by
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

public theorem finalize_fixed_gen_placed_runsTo_sat {key blocks rem : List (BitVec 8)} {s0 : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s0
      (FinPostSat C.F key (blocks ++ rem) s0) :=
  (gseg1a_placed_runsTo_sat (H := H) hpre).trans fun _ hs0 =>
    (gseg1b_placed_runsTo_sat (H := H) hpre hs0).trans fun _ hs1 =>
      (gseg2a_placed_runsTo_sat (H := H) hpre hs1).trans fun _ hs2 =>
        (gseg2b_placed_runsTo_sat (H := H) hpre hs2).trans fun _ hs3 =>
          (gseg3a_placed_runsTo_sat (H := H) hpre hs3).trans fun _ hs3b =>
            (gseg3b_placed_runsTo_sat (H := H) hpre hs3b).trans fun _ hs4 =>
              (gseg4a_placed_runsTo_sat (H := H) hpre hs4).trans fun _ hs5 =>
                gseg4b_placed_runsTo_sat (H := H) hpre hs5

public theorem finalize_fixed_gen_placed_runsTo_of_other_block_sat {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i H]
    {key blocks rem : List (BitVec 8)} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hi : i < 619 := by decide) :
    RunsTo callerProg s0 (FinPostSat C.F key (blocks ++ rem) s0) :=
  RunsTo.of_other_block hcl (finalize_fixed_gen_placed_runsTo_sat (H := H) hpre) hi (by decide) (by decide)

end PlacedGenFinSat

/-! ## Long-IKM `Hkdf::extract` (Block `54`) -/

section LongExtractPlacedSat

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}

/-- Compose `ExtFrame` with a 3-region `S2Frame` contained in `(sp0 - 544#64, 976)`. -/
public theorem extFrame_trans_triple_s2 {s0 : State} {sp0 : BitVec 64} {m m' : Memory}
    {a₁ : BitVec 64} {n₁ : ℕ} {a₂ : BitVec 64} {n₂ : ℕ} {a₃ : BitVec 64} {n₃ : ℕ}
    (hf₁ : ExtFrame s0 sp0 m) (hf₂ : S2Frame m m' [(a₁, n₁), (a₂, n₂), (a₃, n₃)])
    (hsub₁ : (a₁ - (sp0 - 544#64)).toNat + n₁ ≤ 976)
    (hsub₂ : (a₂ - (sp0 - 544#64)).toNat + n₂ ≤ 976)
    (hsub₃ : (a₃ - (sp0 - 544#64)).toNat + n₃ ≤ 976) :
    ExtFrame s0 sp0 m' := by
  refine hf₁.trans (hf₂.mono fun a ha => ?_)
  have hstk : OutsideRegion (sp0 - 544#64) 976 a :=
    ha (sp0 - 544#64, 976) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  simp only [OutsideRegion] at hstk ⊢
  exact ⟨by bv_omega, by bv_omega, by bv_omega⟩

public theorem seg1b1_long_placed_runsTo_sat [HkdfPlacedHooksExactSat C.F H]
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ECompLongPlaced C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (EMemcpyLongPlaced C.F x s0 sp0) := by
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
    have h := readBytes_slice_of_readBytes_eq s.mem x.ikmA x.ikm hikm_s 0
      (64 * (x.ikm.length / 64)) (by omega)
    simpa using h
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_40 : s.mem.RW (sp0 + 0x40#64) 32 :=
    hrw_sp0_s.sub (by bv_omega)
  have hx2_nat : (s.readReg64 .x2).toNat = x.ikm.length / 64 := by
    rcases hikm_len with h | h | h <;> (rw [hx2, h]; rfl)
  refine s2_compress256_multi_step_placed_sat C H
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
  have hag_w8 : AgreesOutside s.mem
      ((s.mem.writeBytes (sp0 + 0x40#64) ist').write8 (sp0 + 63#64)
        (BitVec.ofNat 8 (x.ikm.length % 64))) sp0 328 :=
    agreesOutside_sp0_write8 hag_comp (by decide)
  have hcnt1' : s.mem.read64 (sp0 + 0x60#64) =
      BitVec.ofNat 64 (1 + (x.ikm.take (64 * (x.ikm.length / 64))).length / 64) := by
    rw [hblk_len, Nat.mul_div_cancel_left _ (by decide)]
    exact hcnt1
  have hm := HmacStGen.of_comp_write8 (nrem := x.ikm.length % 64) hcnt1' hout hcnt2
  rw [hblk_len, Nat.mul_div_cancel_left _ (by decide), hist_def] at hm
  unfold EMemcpyLongPlaced ExtCommon
  simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
    State.readReg64_advancePC, State.readReg64_writeReg64,
    Reg.lr, Reg.x0, Reg.x1, Reg.x2, Reg.x19, Reg.x27, Reg.x29, Reg.x22, ite_true, ite_false]
  dsimp only [State.setMem, State.setPC, State.advancePC, State.writeReg64]
  exact ⟨⟨hstat, hsp, hx19, hx27, hx29,
    ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe hag_w8⟩,
    by simp [lsρ, lsMemcpySym], trivial, trivial, trivial, trivial, hx22, hm.1,
    hm.2.1.trans hist_def.symm, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2⟩

private theorem readable_of_rw {m : Memory} {a : BitVec 64} {n : Nat} (h : m.RW a n) :
    m.Readable a n := by
  intro x hx
  obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (h x hx)
  exact ⟨by rw [hp]; rfl, hlf⟩

public theorem seg1b2_long_placed_runsTo_sat [hH : HkdfPlacedHooksExactSat C.F H]
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EMemcpyLongPlaced C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (EC88Long extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx22, hpos, hist, hcnt1, hout, hcnt2⟩
  have hsp_s : s.spAligned = true := by
    simpa [State.spAligned, hsp] using hsp_al
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
    have h := readBytes_slice_of_readBytes_eq s.mem x.ikmA x.ikm hikm_s
      (64 * (x.ikm.length / 64)) (x.ikm.length % 64) (by omega)
    have htake : (x.ikm.drop (64 * (x.ikm.length / 64))).take (x.ikm.length % 64) =
        x.ikm.drop (64 * (x.ikm.length / 64)) :=
      List.take_of_length_le (by simp; omega)
    exact h.trans htake
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_nrem : s.mem.RW sp0 (x.ikm.length % 64) :=
    hrw_sp0_s.sub (by bv_omega)
  have hrw_ikm_s : s.mem.RW x.ikmA x.ikm.length :=
    hframe.rw_of_rw x.ikmA x.ikm.length hRW_ikm
  have hread_rem_s : s.mem.Readable
      (x.ikmA + BitVec.ofNat 64 (64 * (x.ikm.length / 64))) (x.ikm.length % 64) :=
    readable_of_rw (hrw_ikm_s.sub (by rcases hikm_len with h | h | h <;> (rw [h]; bv_omega)))
  have hdisj_rem : x.ikm.length % 64 = 0 ∨
      DisjointRegions sp0 (x.ikm.length % 64)
        (x.ikmA + BitVec.ofNat 64 (64 * (x.ikm.length / 64))) (x.ikm.length % 64) := by
    by_cases h0 : x.ikm.length % 64 = 0
    · exact Or.inl h0
    · refine Or.inr ((hd_ikm_stk.sub_left (x.ikmA + BitVec.ofNat 64 (64 * (x.ikm.length / 64)))
        ⟨by omega, by rcases hikm_len with h | h | h <;> (rw [h]; bv_omega)⟩).sub_right sp0
        ⟨by omega, by rcases hikm_len with h | h | h <;> (rw [h]; bv_omega)⟩).symm
  have hx2_nat : (s.readReg64 .x2).toNat = x.ikm.length % 64 := by
    rcases hikm_len with h | h | h <;> (rw [hx2, h]; rfl)
  refine s2_memcpy_step_placed_of_exact H hH.memcpy
    hstat hsp_s hpc hx0 hx1 hx2_nat hlr hrem_s hrw_sp0_nrem hread_rem_s hdisj_rem fun c => ?_
  dsimp only [applyMemcpyClobber]
  refine RunsTo.refl ?_
  have hag_mc : AgreesOutside s.mem
      (s.mem.writeBytes sp0 (x.ikm.drop (64 * (x.ikm.length / 64)))) sp0 328 :=
    agreesOutside_writeBytes_sub_sp0 (by rw [BitVec.sub_self, hrem_len]; bv_omega)
  unfold EC88Long ExtCommon
  simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
    State.readReg64_setPState, State.readReg64_writeReg64,
    Reg.x19, Reg.x27, Reg.x29, Reg.x22,
    Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x7, Reg.x8, Reg.x9, Reg.x10,
    Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16, Reg.x17,
    ite_false, extPlacedFakeB_off_328]
  dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64]
  refine ⟨⟨hstat, hsp, hx19, hx27, hx29,
    ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe hag_mc⟩,
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

public theorem fin_long_placed_runsTo_sat [HkdfPlacedHooksExactSat C.F H]
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EFinLongPlaced C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s
      (ERetFin extPlacedFakeB C.F x s0 sp0) := by
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
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 544#64)).toNat + 96 ≤ 976 := by
    have heq : (sp0 + 336#64) - (sp0 - 544#64) = 880#64 := by bv_lin
    rw [heq]; decide
  have hrw_336 : RW s.mem (sp0 + 336#64) 96 :=
    hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_336)
  have hpre : FinGenPre finPlacedFakeB C.F (effectiveSalt x.salt)
      (x.ikm.take (64 * (x.ikm.length / 64))) (x.ikm.drop (64 * (x.ikm.length / 64))) s :=
    { pc_eq := by rw [finPlacedFakeB_off_0]; exact hpc
      status := hstat
      key_le := by rw [effectiveSalt_length]; decide
      rem_lt := by simp; omega
      hmac_st := by rw [hx1]; exact hhm
      rw_out := by rw [hx0]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_144.2)
      rw_hm := by rw [hx1]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_176.2)
      rw_fsp := by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_m144.2)
      disj_out_hm := by
        rw [hx0, hx1]; exact disj_sp0_off sp0 144#64 32 176#64 0x90 (by decide)
      disj_out_fsp := by
        rw [hx0, hsp]; exact (disj_sp0_sub_off sp0 144#64 144 144#64 32 (by decide)).symm
      disj_hm_fsp := by
        rw [hx1, hsp]; exact (disj_sp0_sub_off sp0 144#64 144 176#64 0x90 (by decide)).symm
      sp_aligned := by rw [hsp]; exact sp0_aligned_0b1111 hsp_al }
  refine (finalize_fixed_gen_placed_runsTo_of_other_block_sat (C := C) (H := H) hcl hpre).mono
    fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hout, hfr'⟩
  rw [hx0, hx1, hsp] at hfr'
  rw [hx0, List.take_append_drop] at hout
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' hrw_336 ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact disj_sp0_off sp0 144#64 32 336#64 96 (by decide)
    · exact disj_sp0_off sp0 176#64 0x90 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 144#64 144 336#64 96 (by decide)
  have hframe' : ExtFrame s0 sp0 s'.mem :=
    extFrame_trans_triple_s2 hframe hfr' hsub_144.2 hsub_176.2 hsub_m144.2
  have hlr' : s.readReg64 .lr =
      extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 380) := by
    rw [hlr, extPlacedFakeB_off_380]
  exact ⟨⟨hstat', hcs.sp_eq.trans hsp, (CalleeSaved.x19 hcs).trans hx19,
    (CalleeSaved.x27 hcs).trans hx27,
    (CalleeSaved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr', (CalleeSaved.x22 hcs).trans hx22, hout⟩

/-- Relocatable `RunsToE` contract for `Hkdf::extract` (Block `54`) when `x.salt = none` and
`x.ikm.length ∈ {160, 192, 224}` under `[HkdfPlacedHooksSat C.F H]`. -/
public theorem extract_none_long_placed_runsToE_of_inv_sat [HkdfPlacedHooksExactSat C.F H]
    {Inv : Memory → Prop}
    (hInv_kf : ∀ {m1 m2 : Memory}, Inv m1 → m1.KeepsFrozen m2 → Inv m2)
    (hInv_cl : ∀ {m : Memory}, Inv m → LibsignalCodeLoaded lsmpl m)
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpec C.F with pre := fun x s0 => (newFromSliceSpec C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ })
    {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hInv0 : Inv s0.mem)
    (hpc : s0.pc = (blkPl_54).base)
    (hrun : s0.status = .Running)
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
    RunsToE ((blkPC_54).rebase (blkPl_54).base H) s0 (EPost C.F x s0 sp0) := by
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s0.mem.RW sp0 432 := rw_stk_sub hRW_stk sp0 432 hsub_432
  have hRW_salt : RW s0.mem (saltPtrOf sp0 x) 32 := by
    rw [saltPtrOf, hsalt]
    exact rw_stk_sub hRW_stk _ _ hsub_144.2
  have hd_salt_544 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 544#64) 544 := by
    rw [saltPtrOf, hsalt]
    exact (disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)).symm
  have hd_salt_176 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98 := by
    rw [saltPtrOf, hsalt]
    exact disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)
  have h0 := RunsTo.toE (seg0_long_placed_runsTo (H := H)
    hpc hrun hsp0 hx1 hx3 hx4 hsp_al hrw_sp0 hsalt hsaltA)
  have h1 := RunsToE.trans_full h0 fun s hs hkf _ =>
    nfs1_long_placed_runsTo hNfs (hInv_kf hInv0 hkf) hRW_stk hRW_salt hd_salt_544 hd_salt_176 hsp_al hs
  have h2 := h1.trans fun s hs =>
    RunsTo.toE (seg1a_long_placed_runsTo hRW_stk hikm_len hsp_al hs)
  have h3a := h2.trans fun s hs =>
    RunsTo.toE
      (seg1b1_long_placed_runsTo_sat hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs)
  have h3 := h3a.trans fun s hs =>
    RunsTo.toE
      (seg1b2_long_placed_runsTo_sat hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs)
  have h4 := h3.trans fun s hs =>
    RunsTo.toE (seg1c_long_placed_runsTo hRW_stk hsp_al hs)
  have h5 := RunsToE.trans_full h4 fun s hs hkf _ =>
    RunsTo.toE (fin_long_placed_runsTo_sat (hInv_cl (hInv_kf hInv0 hkf)) hRW_stk hikm_len hsp_al hs)
  have h6 := h5.trans fun s hs =>
    RunsTo.toE (seg2_placed_runsTo hsp_al hs)
  have h7 := RunsToE.trans_full h6 fun s hs hkf _ =>
    nfs2_placed_runsTo hNfs (hInv_kf hInv0 hkf) hRW_stk hsp_al hs
  exact h7.trans fun s hs =>
    RunsTo.toE (seg3_placed_runsTo hsp0 hRW_out hRW_stk hd_out_stk hsp_al hs)

end LongExtractPlacedSat

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlacedSat
