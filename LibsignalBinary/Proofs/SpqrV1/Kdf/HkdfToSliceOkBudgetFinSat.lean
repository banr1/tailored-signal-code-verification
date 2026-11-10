/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGen -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetVmSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixed
import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt
import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import VerifiedLibraries.RustStd.Proofs.ExecSegSym

/-!
# Block `425` (`finalize_fixed [local#3]`) `RunsToVm` Bridge (`HkdfToSliceOkBudgetFinSat`)

Proves `finalize_fixed3_pfx_lt64_kdf_vm_sat` on Block `425` lifted onto Block `379`'s program
under `[HkdfPlacedHooksExactSat C.F H]`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetFinSat

open Arm64 ProofLib
open Arm64.Obj (PlacedLib)
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.HMAC (ShaState chunks64 hmacWith sha256IV toBEBytes)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkLib_379 blkLib_402 blkLib_425 blkLib_eq_379 blkLib_eq_402 blkLib_eq_425
   blkPC_378 blkPC_379 blkPC_402 blkPC_425 blkPl_378 blkPl_379 blkPl_402 blkPl_425
   libsignalMutatedBlocks libsignalSessionLib
   lsProg_402 ls_externAt?_blockProgram_eq_of_externs_eq ls_externAt?_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
  (disjointRegions_of_ro_rw length_hmacWith)
open CryptoVerification.LibsignalSpqrV1 (hkdfExtractBytes spqrHkdfWith)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved FinSaved Frame
   HkdfPlacedHooks HmacSt LibsignalCodeRoLoaded RW RunsTo RunsToFrom TraceEq
   agreesOutside_seg2a agreesOutside_seg3a agreesOutside_seg4a
   digestBytes digestBytes_eq_append extHookStack extract_withLsCodeRoLoaded
   finSaved_seg3a finSaved_seg4a frame_seg2a frame_seg3a frame_seg4a fsp_aligned
   hmacInnerInit hmacOuterInit keys_ls_subroutine_ok_of_block_cro
   compress256Hook_eq lsCompress256Sym lsMemcpySym lsMemsetSym noAllocShimSpec
   outerBlock outerBlock_digestBytes_length
   read32_words_at_104_of_shaStateBytes read32_words_at_64_of_shaStateBytes
   read64_seg2a_mid read64_seg3a_pad_32 read64_seg3a_pad_40
   readBytes_56_eq_append_8 readBytes_56_of_buf_eq readBytes_fsp_64_seg2 readBytes_fsp_64_seg3
   readBytes_write32_8_digestBytes ro_outside_rw_shared_lb rw_of_perm_eq shaStateBytes_length
   toLEBytes_4_rev32 toLEBytes_8_read64 toLEBytes_8_rev32_append toLEBytes_8_rev64
   ult_7_of_lt_56 withLsCodeRoLoaded xor_63_of_lt_64
   zeroExtend64_ofNat8 zeroExtend64_truncate32_ofNat64)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (hkdfExpand_64_eq t1_length t2_length t3_length)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (CallingConventionPreserved.x19 CallingConventionPreserved.x20
   CallingConventionPreserved.x21 CallingConventionPreserved.x22
   CallingConventionPreserved.x27 CallingConventionPreserved.x29 S2Frame)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
  (AgreesOn AgreesOn.finSaved_of AgreesOn.read64_eq AgreesOn.readBytes_eq)
open CryptoVerification.SpqrV1.Alloc (spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt hkdfToSliceSpec hkdfToSliceSpqrSpec)
open CryptoVerification.SpqrV1.Kdf
  (FinPre3 FinPre3Pfx FinPre3PfxGen HmacStN
   bit_len_innerN_eq bit_len_innerN_eq_lt64 effectiveHmacKey effectiveHmacKey_length_le
   effectiveHmacKey_of_le fin3PlacedFakeB fin3PlacedFakeB_off_0
   hmacWith_effectiveHmacKey hmacWith_pfx_short hmacWith_pfx_two_blocks
   innerLastBlockN innerLastBlockN_length innerPadBlock1 innerPadBlock1_length
   innerPadBlock2 innerPadBlock2_length read64_fsp32_hm readBytes_64_eq_append_8
   readBytes_fsp_64_copy spqrRustAllocZeroedSym toLEBytes_8_zero_7 ult_7_of_ge_56)
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt (disjointRegions_of_outside)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
  (stripExecOutside_readBytes stripExecOutside_readable stripExecOutside_rw unstrip_frame)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (CallingConventionPreserved.x23 CallingConventionPreserved.x24
   CallingConventionPreserved.x25 CallingConventionPreserved.x26
   CallingConventionPreserved.x28 HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat (FinPostSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

open CryptoVerification.LibsignalTripleRatchet.FinalizeFixedProof (FinCommon FinPost)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetVmSat
  (RunsToVm blk425_noMsr blk425_noSvc0 extractLsb'_0_64_zero128 extractLsb'_64_64_zero128
   hmacNoMemsetExcHooks hmacNoMemsetExcHooks_compress
   lift_block_to_379_vm mem_setMem placed_memset_budget_optAlloc_steps_sat
   stripS_finSaved stripS_hmacSt stripS_hmacStN
   stripS_mem stripS_read64 stripS_read8 stripS_readBytes unstrip_finCommon)

attribute [local simp, local arm64_norm] extractLsb'_0_64_zero128 extractLsb'_64_64_zero128

/-! ## 3. Block `425` (`finalize_fixed [local#3]`) `RunsToVm` under `HkdfPlacedHooksExactSat` -/

local macro "fin_reg" : tactic =>
  `(tactic| (
    try rw [State.readReg64_setMem]
    try rw [State.pc_setMem]
    try rw [State.sp_setMem]
    try rw [State.status_setMem]
    simp (config := { decide := true }) only [arm64_norm, *]))

local macro "fin_saved_slot" : tactic =>
  `(tactic| (
    try rw [mem_setMem]
    simp (config := { decide := true }) only [arm64_norm]))

private theorem s2_compress256_step_425_hc [LibsignalPlacement] (C : Crypto) (H : LibsignalHooks)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running) (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr) (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64) (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr 64 = blk)
    (hlen : blk.length = 64) (hrw : s.mem.RW stPtr 32)
    (h : RunsToFrom ((blkPC_425).rebase (blkPl_425).base H) s₀
      ((s.setMem (s.mem.writeBytes stPtr (shaStateBytes (C.F st blk)))).setPC lr) Q) :
    RunsToFrom ((blkPC_425).rebase (blkPl_425).base H) s₀ s Q := by
  have hcan : s.mem.canWrite stPtr (shaStateBytes (C.F st blk)).length = true := by
    rw [shaStateBytes_length]; exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : ((blkPC_425).rebase (blkPl_425).base H).externAt? s.pc =
      some (compress256Hook C.F) := by
    rw [hpc, ls_externAt?_of_mem (i := 425) (by decide) (by decide) (by decide), h_compress]
  have hstate := compress256Hook_eq C.F hx0 hx1 hx2 hlr hst hblk hlen
  have hkeep : s.mem.KeepsFrozen (compress256Hook C.F s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (compress256Hook C.F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

private structure StateF0p425 [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_425).base + 28#64
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x0
  x1_eq   : s.readReg64 .x1 = s0.readReg64 .x1
  hmac_st : HmacStN s.mem (s0.readReg64 .x1) F key pfx tail

private structure StateFPreMemset425 [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = lsρ lsMemsetSym
  common  : FinCommon s0 s
  lr_eq   : s.readReg64 .lr = (blkPl_425).base + 76#64
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + BitVec.ofNat 64 tail.length + 1#64
  x1_eq   : (s.readReg64 .x1).truncate 8 = 0#8
  x2_eq   : (s.readReg64 .x2).toNat = 63 - tail.length
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 tail.length
  x24_eq  : s.readReg64 .x24 = BitVec.ofNat 64 (1 + pfx.length / 64)
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 (63 - tail.length)
  pad_eq  : s.mem.readBytes (s0.readReg64 .x1) (tail.length + 1) = tail ++ [0x80#8]
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes ((chunks64 pfx).foldl F (hmacInnerInit F key))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure FinMidPre (key pfx tail : List (BitVec 8)) (s0 : State) : Prop where
  key_le       : key.length ≤ 64
  pfx_mod      : pfx.length % 64 = 0
  tail_lt      : tail.length < 64
  rw_out       : s0.mem.RW (s0.readReg64 .x0) 32
  rw_hm        : s0.mem.RW (s0.readReg64 .x1) 0x90
  rw_fsp       : s0.mem.RW (s0.sp - 144#64) 144
  disj_out_fsp : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64) 144
  disj_hm_fsp  : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64) 144
  sp_aligned   : (s0.sp &&& 15#64) = 0#64

private theorem FinMidPre.stripS (kp : BitVec 64 → Bool) {key pfx tail : List (BitVec 8)}
    {s0 : State} (hp : FinMidPre key pfx tail s0) :
    FinMidPre key pfx tail (ProofLib.stripS kp s0) := by
  have hr : ∀ r, (ProofLib.stripS kp s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  have hsp0 : (ProofLib.stripS kp s0).sp = s0.sp := by cases s0; rfl
  exact
    { key_le := hp.key_le, pfx_mod := hp.pfx_mod, tail_lt := hp.tail_lt,
      rw_out := by rw [stripS_mem, hr]; exact stripExecOutside_rw kp s0.mem _ _ hp.rw_out,
      rw_hm := by rw [stripS_mem, hr]; exact stripExecOutside_rw kp s0.mem _ _ hp.rw_hm,
      rw_fsp := by rw [stripS_mem, hsp0]; exact stripExecOutside_rw kp s0.mem _ _ hp.rw_fsp,
      disj_out_fsp := by rw [hr, hsp0]; exact hp.disj_out_fsp,
      disj_hm_fsp := by rw [hr, hsp0]; exact hp.disj_hm_fsp,
      sp_aligned := by rw [hsp0]; exact hp.sp_aligned }

private structure StateF1_425 [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_425).base + 76#64
  common  : FinCommon s0 s
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

private structure StateF3Gen425 [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (ist : ShaState) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_425).base + 180#64
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 = shaStateBytes ist
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private theorem finSaved_seg2a_local {s0 : State} {m1 m2 m3 m4 : Memory} {hm fsp : BitVec 64}
    (hs : FinSaved s0 fsp m1) (hag1 : AgreesOutside m1 m2 fsp 64)
    (hag2 : AgreesOutside m2 m3 hm 64) (hag3 : AgreesOutside m3 m4 fsp 64)
    (hd_fsp : DisjointRegions fsp 64 (fsp + 0x40#64) 0x50)
    (hd_hm : DisjointRegions hm 64 (fsp + 0x40#64) 0x50) :
    FinSaved s0 fsp m4 :=
  FinSaved.of_agreesOutside
    (FinSaved.of_agreesOutside (FinSaved.of_agreesOutside hs hag1 hd_fsp) hag2 hd_hm) hag3 hd_fsp

private theorem read32_seg4a_mid_local (m : Memory) (hm fsp off : BitVec 64) (w : BitVec 32)
    (hoff : off = 128#64 ∨ off = 132#64) (hd : DisjointRegions fsp 64 hm 0x90)
    (hw : m.read32 (hm + off) = w) :
    (((((((((m.write8 (hm + 63#64) 0#8).write64
      fsp 0#64).write64 (fsp + 8#64) 0#64).write64
      (fsp + 16#64) 0#64).write64 (fsp + 24#64) 0#64).write64
      (fsp + 32#64) 0#64).write64 (fsp + 40#64) 0#64).write64
      (fsp + 48#64) 0#64).write64 (fsp + 56#64) 0#64).read32 (hm + off) = w := by
  have hag_fsp : AgreesOutside (m.write8 (hm + 63#64) 0#8)
      (((((((((m.write8 (hm + 63#64) 0#8).write64
        fsp 0#64).write64 (fsp + 8#64) 0#64).write64
        (fsp + 16#64) 0#64).write64 (fsp + 24#64) 0#64).write64
        (fsp + 32#64) 0#64).write64 (fsp + 40#64) 0#64).write64
        (fsp + 48#64) 0#64).write64 (fsp + 56#64) 0#64) fsp 64 := by agrees_outside_writes
  have hag_63 : AgreesOutside m (m.write8 (hm + 63#64) 0#8) (hm + 63#64) 1 := by
    agrees_outside_writes
  rcases hoff with rfl | rfl <;>
    rw [hag_fsp.read32_eq (hd.sub_right _ ⟨by decide, by bv_omega⟩),
        hag_63.read32_eq (by unfold DisjointRegions; bv_omega), hw]

private theorem ost_eq_seg3a_local {m1 m2 m3 m4 m5 : Memory} {hm fsp : BitVec 64}
    {bs : List (BitVec 8)} (host : m1.readBytes (hm + 0x68#64) 32 = bs)
    (hag1 : AgreesOutside m1 m2 hm 64) (hag2 : AgreesOutside m2 m3 fsp 64)
    (hag3 : AgreesOutside m3 m4 hm 64) (hag4 : AgreesOutside m4 m5 fsp 64)
    (hd_hm : DisjointRegions hm 64 (hm + 0x68#64) 32)
    (hd_fsp : DisjointRegions fsp 64 (hm + 0x68#64) 32) :
    m5.readBytes (hm + 0x68#64) 32 = bs :=
  (hag4.readBytes_eq hd_fsp (by decide)).trans
    ((hag3.readBytes_eq hd_hm (by decide)).trans
      ((hag2.readBytes_eq hd_fsp (by decide)).trans
        ((hag1.readBytes_eq hd_hm (by decide)).trans host)))

set_option maxHeartbeats 1600000 in
private theorem seg1a_425 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key pfx tail : List (BitVec 8)} {s0 : State}
    (hpre : FinPre3PfxGen fin3PlacedFakeB C.F key pfx tail s0) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s0 (StateF0p425 C.F key pfx tail s0) := by
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
      (s0.sp - 144#64) 144 := by agrees_outside_writes
  refine ⟨by fin_reg,
    ⟨by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
      ⟨by fin_saved_slot, by fin_saved_slot, by fin_saved_slot,
       by fin_saved_slot, by fin_saved_slot, by fin_saved_slot,
       by fin_saved_slot, by fin_saved_slot, by fin_saved_slot⟩,
      by rw [mem_setMem]; exact Frame.trans_agreesOutside (Frame.refl s0.mem _) (by simp) hag⟩,
    by fin_reg, by fin_reg,
    by rw [mem_setMem]; exact HmacStN.of_agreesOutside hpre.hmac_st hag hpre.disj_hm_fsp.symm⟩

set_option maxHeartbeats 1600000 in
private theorem seg1b_pre_425 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGen fin3PlacedFakeB C.F key pfx tail s0)
    (hs : StateF0p425 C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateFPreMemset425 C.F key pfx tail s0) := by
  rcases hs with ⟨hpc, ⟨hstat, hsp_s, hx29, hx26, hx27, hx28, hsaved, hframe⟩, hx0, hx1,
    ⟨hpfx_mod, hmsg_lt64, hmsg_eq, hpos_eq, hin_eq, hibl_eq, hout_eq, hobl_eq⟩⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hcw_pos : s.mem.canWrite (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) 1 = true :=
    hrw_hm.canWrite_sub (by bv_omega) (by decide)
  have hze32 := zeroExtend64_truncate32_ofNat64 hmsg_lt64
  have hze64 := zeroExtend64_ofNat8 hmsg_lt64
  have hxor63 := xor_63_of_lt_64 hmsg_lt64
  iterate 12 s2_step
  refine RunsTo.refl ?_
  have htoNat_sub : (BitVec.ofNat 64 (63 - tail.length)).toNat = 63 - tail.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  set m_pad := s.mem.write8 (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) 0x80#8
  have hag_pad : AgreesOutside s.mem m_pad
      (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) 1 := by
    dsimp only [m_pad]; agrees_outside_writes
  have hd_pad_fsp : DisjointRegions (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) 1
      (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_pad_ist : DisjointRegions (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) 1
      (s0.readReg64 .x1 + 0x40#64) 32 := by unfold DisjointRegions; bv_omega
  have hd_pad_ost : DisjointRegions (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) 1
      (s0.readReg64 .x1 + 0x68#64) 32 := by unfold DisjointRegions; bv_omega
  have hd_pad_obl : DisjointRegions (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) 1
      (s0.readReg64 .x1 + 0x88#64) 8 := by unfold DisjointRegions; bv_omega
  have hpad_bytes : m_pad.readBytes (s0.readReg64 .x1) (tail.length + 1) = tail ++ [0x80#8] := by
    have hw : m_pad = s.mem.writeBytes (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) [0x80#8] := rfl
    rw [hw, readBytes_add _ (s0.readReg64 .x1) tail.length 1]
    have hl : (s.mem.writeBytes (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) [0x80#8]).readBytes
        (s0.readReg64 .x1) tail.length = tail := by
      by_cases h0 : tail.length = 0
      · simp [h0] at hmsg_eq ⊢; exact hmsg_eq
      · rw [readBytes_writeBytes_disjoint s.mem (s0.readReg64 .x1) tail.length
          (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) [0x80#8]]
        · exact hmsg_eq
        · dsimp only [List.length]; unfold DisjointRegions; bv_omega
    have hr : (s.mem.writeBytes (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) [0x80#8]).readBytes
        (s0.readReg64 .x1 + BitVec.ofNat 64 tail.length) 1 = [0x80#8] :=
      readBytes_writeBytes_same s.mem _ [0x80#8] (by decide)
    rw [hl, hr]
  refine ⟨by simp only [arm64_norm, lsMemsetSym],
    ⟨by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
      by rw [mem_setMem]; exact FinSaved.of_agreesOutside hsaved hag_pad hd_pad_fsp,
      by rw [mem_setMem]
         exact Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
           (by simp) (by bv_omega) hag_pad⟩,
    by fin_reg, by fin_reg,
    by simp (config := { decide := true }) only [arm64_norm],
    by simpa only [arm64_norm] using htoNat_sub,
    by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
    by rw [mem_setMem]; exact hpad_bytes,
    by rw [mem_setMem]; exact (hag_pad.readBytes_eq hd_pad_ist (by decide)).trans hin_eq,
    by rw [mem_setMem]; exact (hag_pad.readBytes_eq hd_pad_ost (by decide)).trans hout_eq,
    by rw [mem_setMem]; exact (hag_pad.read64_eq hd_pad_obl).trans hobl_eq⟩

private structure StateF2Lt56_425 [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_425).base + 176#64
  common  : FinCommon s0 s
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

set_option maxHeartbeats 1600000 in
private theorem seg2_lt56_a_425 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinMidPre key pfx tail s0) (hlt56 : tail.length < 56)
    (hs : StateF1_425 C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s
      (StateF2Lt56_425 C.F key pfx tail s0) := by
  rcases hs with ⟨hpc, ⟨hstat, hsp_s, hx29, hx26, hx27, hx28, hsaved, hframe⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hult_7 := ult_7_of_lt_56 hlt56
  obtain ⟨hbit_len1, hbit_len2⟩ := bit_len_innerN_eq (b := 1 + pfx.length / 64) hlt56
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
  refine ⟨by fin_reg,
    ⟨by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
      by rw [mem_setMem]
         exact finSaved_seg2a_local hsaved hag1 hag2 hag3 hd_fsp64_saved hd_hm64_saved,
      by rw [mem_setMem]; exact frame_seg2a hframe hag1 hag2 hag3⟩,
    by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
    by rw [mem_setMem]
       refine (readBytes_fsp_64_seg2 _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
       rw [toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
           toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_rev64,
           readBytes_56_eq_append_8 s.mem (s0.readReg64 .x1),
           readBytes_56_of_buf_eq s.mem (s0.readReg64 .x1) tail hbuf hlt56]; rfl,
    by rw [mem_setMem]
       exact (hag3.readBytes_eq hd_fsp64_ist (by decide)).trans
         ((hag2.readBytes_eq hd_hm64_ist (by decide)).trans
           ((hag1.readBytes_eq hd_fsp64_ist (by decide)).trans hist)),
    by rw [mem_setMem]
       exact (hag3.readBytes_eq hd_fsp64_ost (by decide)).trans
         ((hag2.readBytes_eq hd_hm64_ost (by decide)).trans
           ((hag1.readBytes_eq hd_fsp64_ost (by decide)).trans host)),
    by rw [mem_setMem]
       exact (hag3.read64_eq hd_fsp64_obl).trans
         ((hag2.read64_eq hd_hm64_obl).trans
           ((hag1.read64_eq hd_fsp64_obl).trans hobl))⟩

set_option maxHeartbeats 1600000 in
private theorem seg2_lt56_b_425 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinMidPre key pfx tail s0) (hlt56 : tail.length < 56)
    (hs : StateF2Lt56_425 C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s
      (StateF3Gen425 C.F key
        (C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key))
          (innerLastBlockN (1 + pfx.length / 64) tail)) s0) := by
  rcases hs with ⟨hpc, ⟨hstat, hsp_s, hx29, hx26, hx27, hx28, hsaved, hframe⟩,
    hx0, hx1, hx2, hx19, hx20, hx21, hx22, hblk, hist, host, hobl⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_ist : s.mem.RW (s0.readReg64 .x1 + 0x40#64) 32 := hrw_hm.sub (by bv_omega)
  s2_step
  refine s2_compress256_step_425_hc C H h_compress
    (stPtr := s0.readReg64 .x1 + 0x40#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_425).base + 180#64)
    (st := (chunks64 pfx).foldl C.F (hmacInnerInit C.F key))
    (blk := innerLastBlockN (1 + pfx.length / 64) tail)
    hstat (by simp only [arm64_norm, lsCompress256Sym])
    (by fin_reg) (by fin_reg) (by fin_reg) (by fin_reg)
    hist hblk (innerLastBlockN_length hlt56) hrw_ist ?_
  refine RunsTo.refl ?_
  set blk_in := shaStateBytes (C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key))
    (innerLastBlockN (1 + pfx.length / 64) tail))
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x40#64) blk_in)
      (s0.readReg64 .x1 + 0x40#64) 32 := by
    have hlen : blk_in.length = 32 := shaStateBytes_length _
    rw [← hlen]; exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_in
  have hd_ist_saved : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_ist_ost : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_ist_obl : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine ⟨by fin_reg,
    ⟨by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
      FinSaved.of_agreesOutside hsaved hag_comp hd_ist_saved,
      Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
        (by simp) (by bv_omega) hag_comp⟩,
    by fin_reg, by fin_reg, by fin_reg, by fin_reg,
    by have hlen : blk_in.length = 32 := shaStateBytes_length _
       rw [← hlen]; exact readBytes_writeBytes_same s.mem _ blk_in (by rw [hlen]; decide),
    (hag_comp.readBytes_eq hd_ist_ost (by decide)).trans host,
    (hag_comp.read64_eq hd_ist_obl).trans hobl⟩

private structure StateF2b425 [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_425).base + 116#64
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 tail.length
  x24_eq  : s.readReg64 .x24 = BitVec.ofNat 64 (1 + pfx.length / 64)
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes (F ((chunks64 pfx).foldl F (hmacInnerInit F key)) (innerPadBlock1 tail))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

set_option maxHeartbeats 1600000 in
private theorem seg2_ge56_ab_425 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinMidPre key pfx tail s0) (hge : 56 ≤ tail.length)
    (hs : StateF1_425 C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF2b425 C.F key pfx tail s0) := by
  rcases hs with ⟨hpc, ⟨hstat, hsp_s, hx29, hx26, hx27, hx28, hsaved, hframe⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hult_7 := ult_7_of_ge_56 hge hpre.tail_lt
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  iterate 7 s2_step
  have hread32 := fun u0 u1 u2 u3 => read64_fsp32_hm s.mem _ _ u0 u1 u2 u3 32#64 (by decide) hd_hm64_fsp64
  have hread40 := fun u0 u1 u2 u3 => read64_fsp32_hm s.mem _ _ u0 u1 u2 u3 40#64 (by decide) hd_hm64_fsp64
  have hread48 := fun u0 u1 u2 u3 => read64_fsp32_hm s.mem _ _ u0 u1 u2 u3 48#64 (by decide) hd_hm64_fsp64
  have hread56 := fun u0 u1 u2 u3 => read64_fsp32_hm s.mem _ _ u0 u1 u2 u3 56#64 (by decide) hd_hm64_fsp64
  iterate 3 s2_step
  clear hread32 hread40 hread48 hread56
  set m_cp := (((((((s.mem.write64 (s0.sp - 144#64) (s.mem.read64 (s0.readReg64 .x1))).write64
    (s0.sp - 144#64 + 8#64) (s.mem.read64 (s0.readReg64 .x1 + 8#64))).write64
    (s0.sp - 144#64 + 16#64) (s.mem.read64 (s0.readReg64 .x1 + 16#64))).write64
    (s0.sp - 144#64 + 24#64) (s.mem.read64 (s0.readReg64 .x1 + 24#64))).write64
    (s0.sp - 144#64 + 32#64) (s.mem.read64 (s0.readReg64 .x1 + 32#64))).write64
    (s0.sp - 144#64 + 40#64) (s.mem.read64 (s0.readReg64 .x1 + 40#64))).write64
    (s0.sp - 144#64 + 48#64) (s.mem.read64 (s0.readReg64 .x1 + 48#64))).write64
    (s0.sp - 144#64 + 56#64) (s.mem.read64 (s0.readReg64 .x1 + 56#64))
  have hag : AgreesOutside s.mem m_cp (s0.sp - 144#64) 64 := by dsimp only [m_cp]; agrees_outside_writes
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_ist : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x40#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_obl : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x88#64) 8 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hfr_cp := Frame.trans_agreesOutside_sub hframe (rbase := s0.sp - 144#64) (rlen := 144)
    (by simp) (by bv_omega) hag
  have hrw_ist_cp : m_cp.RW (s0.readReg64 .x1 + 0x40#64) 32 :=
    (rw_of_perm_eq hfr_cp.2 hpre.rw_hm).sub (by bv_omega)
  have hbuf1 : s.mem.readBytes (s0.readReg64 .x1) 64 = innerPadBlock1 tail := hbuf
  refine s2_compress256_step_425_hc C H h_compress
    (stPtr := s0.readReg64 .x1 + 0x40#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_425).base + 116#64)
    (st := (chunks64 pfx).foldl C.F (hmacInnerInit C.F key))
    (blk := innerPadBlock1 tail)
    hstat (by simp only [arm64_norm, lsCompress256Sym])
    (by fin_reg) (by fin_reg) (by fin_reg) (by fin_reg)
    (by rw [mem_setMem]; exact (hag.readBytes_eq hd_fsp64_ist (by decide)).trans hist)
    (by rw [mem_setMem]; refine (readBytes_fsp_64_copy _ _ _ _ _ _ _ _ _ _).trans ?_
        rw [toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
            toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
            readBytes_64_eq_append_8 s.mem (s0.readReg64 .x1), hbuf1])
    (innerPadBlock1_length hpre.tail_lt)
    (by rw [mem_setMem]; exact hrw_ist_cp) ?_
  refine RunsTo.refl ?_
  set blk_in := shaStateBytes (C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key)) (innerPadBlock1 tail))
  have hag_comp : AgreesOutside m_cp (m_cp.writeBytes (s0.readReg64 .x1 + 0x40#64) blk_in)
      (s0.readReg64 .x1 + 0x40#64) 32 := by
    have hlen : blk_in.length = 32 := shaStateBytes_length _
    rw [← hlen]; exact ProofLib.AgreesOutside.writeBytes_self m_cp _ blk_in
  have hd_ist_saved : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_ist_ost : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_ist_obl : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine ⟨by fin_reg,
    ⟨by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
      FinSaved.of_agreesOutside (FinSaved.of_agreesOutside hsaved hag hd_fsp64_saved)
        hag_comp hd_ist_saved,
      Frame.trans_agreesOutside_sub hfr_cp (rbase := s0.readReg64 .x1) (rlen := 0x90)
        (by simp) (by bv_omega) hag_comp⟩,
    by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
    by have hlen : blk_in.length = 32 := shaStateBytes_length _
       rw [mem_setMem, ← hlen]; exact readBytes_writeBytes_same m_cp _ blk_in (by rw [hlen]; decide),
    by rw [mem_setMem]
       exact (hag_comp.readBytes_eq hd_ist_ost (by decide)).trans
         ((hag.readBytes_eq hd_fsp64_ost (by decide)).trans host),
    by rw [mem_setMem]
       exact (hag_comp.read64_eq hd_ist_obl).trans ((hag.read64_eq hd_fsp64_obl).trans hobl)⟩

private structure StateF2c425 [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key pfx tail : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_425).base + 176#64
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 = innerPadBlock2 (1 + pfx.length / 64) tail
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes (F ((chunks64 pfx).foldl F (hmacInnerInit F key)) (innerPadBlock1 tail))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

set_option maxHeartbeats 1600000 in
private theorem seg2_ge56_c_425 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinMidPre key pfx tail s0)
    (hs : StateF2b425 C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF2c425 C.F key pfx tail s0) := by
  rcases hs with ⟨hpc, ⟨hstat, hsp_s, hx29, hx26, hx27, hx28, hsaved, hframe⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hist, host, hobl⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  obtain ⟨hbit_len1, hbit_len2⟩ := bit_len_innerN_eq_lt64 (b := 1 + pfx.length / 64) hpre.tail_lt
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  iterate 8 s2_step
  let mz := ((((((s.mem.write64 (s0.readReg64 .x1 + 48#64) 0#64).write64
    (s0.readReg64 .x1 + 16#64) 0#64).write64
    (s0.readReg64 .x1 + 24#64) 0#64).write64
    (s0.readReg64 .x1 + 32#64) 0#64).write64
    (s0.readReg64 .x1 + 40#64) 0#64).write64
    (s0.readReg64 .x1) 0#64).write64
    (s0.readReg64 .x1 + 8#64) 0#64
  have hread32 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid mz _ _ u0 u1 u2 u3 w56 32#64 (by decide) hd_hm64_fsp64
  have hread40 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid mz _ _ u0 u1 u2 u3 w56 40#64 (by decide) hd_hm64_fsp64
  have hread48 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid mz _ _ u0 u1 u2 u3 w56 48#64 (by decide) hd_hm64_fsp64
  iterate 7 s2_step
  clear hread32 hread40 hread48
  refine RunsTo.refl ?_
  have hag0 : AgreesOutside s.mem mz (s0.readReg64 .x1) 64 := by dsimp only [mz]; agrees_outside_writes
  obtain ⟨hag1, hag2, hag3⟩ := agreesOutside_seg2a mz (s0.readReg64 .x1) (s0.sp - 144#64)
    0#64 0#64 0#64 0#64 _ 0#64 0#64 0#64 _
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
  have hsaved0 : FinSaved s0 (s0.sp - 144#64) mz := FinSaved.of_agreesOutside hsaved hag0 hd_hm64_saved
  have hfr0 := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
    (by simp) (by bv_omega) hag0
  refine ⟨by fin_reg,
    ⟨by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
      by rw [mem_setMem]
         exact finSaved_seg2a_local hsaved0 hag1 hag2 hag3 hd_fsp64_saved hd_hm64_saved,
      by rw [mem_setMem]; exact frame_seg2a hfr0 hag1 hag2 hag3⟩,
    by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
    by rw [mem_setMem]; refine (readBytes_fsp_64_seg2 mz _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
       rw [toLEBytes_8_zero_7, toLEBytes_8_rev64]; rfl,
    by rw [mem_setMem]
       exact (hag3.readBytes_eq hd_fsp64_ist (by decide)).trans
         ((hag2.readBytes_eq hd_hm64_ist (by decide)).trans
           ((hag1.readBytes_eq hd_fsp64_ist (by decide)).trans
             ((hag0.readBytes_eq hd_hm64_ist (by decide)).trans hist))),
    by rw [mem_setMem]
       exact (hag3.readBytes_eq hd_fsp64_ost (by decide)).trans
         ((hag2.readBytes_eq hd_hm64_ost (by decide)).trans
           ((hag1.readBytes_eq hd_fsp64_ost (by decide)).trans
             ((hag0.readBytes_eq hd_hm64_ost (by decide)).trans host))),
    by rw [mem_setMem]
       exact (hag3.read64_eq hd_fsp64_obl).trans
         ((hag2.read64_eq hd_hm64_obl).trans
           ((hag1.read64_eq hd_fsp64_obl).trans
             ((hag0.read64_eq hd_hm64_obl).trans hobl)))⟩

set_option maxHeartbeats 1600000 in
private theorem seg2_ge56_d_425 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinMidPre key pfx tail s0)
    (hs : StateF2c425 C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s
      (StateF3Gen425 C.F key
        (C.F (C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key)) (innerPadBlock1 tail))
          (innerPadBlock2 (1 + pfx.length / 64) tail)) s0) := by
  rcases hs with ⟨hpc, ⟨hstat, hsp_s, hx29, hx26, hx27, hx28, hsaved, hframe⟩,
    hx0, hx1, hx2, hx19, hx20, hx21, hx22, hblk, hist, host, hobl⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_ist : s.mem.RW (s0.readReg64 .x1 + 0x40#64) 32 := hrw_hm.sub (by bv_omega)
  s2_step
  refine s2_compress256_step_425_hc C H h_compress
    (stPtr := s0.readReg64 .x1 + 0x40#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_425).base + 180#64)
    (st := C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key)) (innerPadBlock1 tail))
    (blk := innerPadBlock2 (1 + pfx.length / 64) tail)
    hstat (by simp only [arm64_norm, lsCompress256Sym])
    (by fin_reg) (by fin_reg) (by fin_reg) (by fin_reg)
    hist hblk (innerPadBlock2_length (1 + pfx.length / 64) tail) hrw_ist ?_
  refine RunsTo.refl ?_
  set blk_in := shaStateBytes (C.F (C.F ((chunks64 pfx).foldl C.F (hmacInnerInit C.F key))
    (innerPadBlock1 tail)) (innerPadBlock2 (1 + pfx.length / 64) tail))
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x40#64) blk_in)
      (s0.readReg64 .x1 + 0x40#64) 32 := by
    have hlen : blk_in.length = 32 := shaStateBytes_length _
    rw [← hlen]; exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_in
  have hd_ist_saved : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_ist_ost : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_ist_obl : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine ⟨by fin_reg,
    ⟨by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
      FinSaved.of_agreesOutside hsaved hag_comp hd_ist_saved,
      Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
        (by simp) (by bv_omega) hag_comp⟩,
    by fin_reg, by fin_reg, by fin_reg, by fin_reg,
    by have hlen : blk_in.length = 32 := shaStateBytes_length _
       rw [← hlen]; exact readBytes_writeBytes_same s.mem _ blk_in (by rw [hlen]; decide),
    (hag_comp.readBytes_eq hd_ist_ost (by decide)).trans host,
    (hag_comp.read64_eq hd_ist_obl).trans hobl⟩

private structure StateF3bGen425 [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (ist : ShaState) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_425).base + 304#64
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 = outerBlock (digestBytes ist)
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)

private structure StateF4Gen425 [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (ist : ShaState) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_425).base + 308#64
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 =
    shaStateBytes (F (hmacOuterInit F key) (outerBlock (digestBytes ist)))

set_option maxHeartbeats 1600000 in
private theorem seg3a_425 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key pfx tail : List (BitVec 8)} {ist : ShaState} {s0 s : State}
    (hpre : FinMidPre key pfx tail s0)
    (hs : StateF3Gen425 C.F key ist s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF3bGen425 C.F key ist s0) := by
  rcases hs with ⟨hpc, ⟨hstat, hsp_s, hx29, hx26, hx27, hx28, hsaved, hframe⟩,
    hx19, hx20, hx21, hx22, hist, host, hobl⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_64_of_shaStateBytes s.mem (s0.readReg64 .x1) ist hist
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
  refine ⟨by fin_reg,
    ⟨by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
      by rw [mem_setMem]; exact finSaved_seg3a hsaved hag1 hag2 hag3 hag4 hd_hm64_saved hd_fsp64_saved,
      by rw [mem_setMem]; exact frame_seg3a hframe hag1 hag2 hag3 hag4⟩,
    by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
    by rw [mem_setMem]; refine (readBytes_fsp_64_seg3 _ _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
       rw [toLEBytes_8_rev32_append, toLEBytes_8_rev32_append,
           toLEBytes_8_rev32_append, toLEBytes_8_rev32_append]
       have htail : toLEBytes 8 0x80#64 ++ toLEBytes 8 0#64 ++ toLEBytes 8 0#64 ++
           toLEBytes 8 (rev64 768#64) =
           [0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 768#64 := by decide
       unfold outerBlock; rw [digestBytes_eq_append ist]
       simp only [List.append_assoc] at htail ⊢; rw [htail]; rfl,
    by rw [mem_setMem]; exact ost_eq_seg3a_local host hag1 hag2 hag3 hag4 hd_hm64_ost hd_fsp64_ost⟩

set_option maxHeartbeats 1600000 in
private theorem seg3b_425 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {key pfx tail : List (BitVec 8)} {ist : ShaState} {s0 s : State}
    (hpre : FinMidPre key pfx tail s0)
    (hs : StateF3bGen425 C.F key ist s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (StateF4Gen425 C.F key ist s0) := by
  rcases hs with ⟨hpc, ⟨hstat, hsp_s, hx29, hx26, hx27, hx28, hsaved, hframe⟩,
    hx0, hx1, hx2, hx19, hx20, hblk, host⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_ost : s.mem.RW (s0.readReg64 .x1 + 0x68#64) 32 := hrw_hm.sub (by bv_omega)
  s2_step
  refine s2_compress256_step_425_hc C H h_compress
    (stPtr := s0.readReg64 .x1 + 0x68#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_425).base + 308#64)
    (st := hmacOuterInit C.F key) (blk := outerBlock (digestBytes ist))
    hstat (by simp only [arm64_norm, lsCompress256Sym])
    (by fin_reg) (by fin_reg) (by fin_reg) (by fin_reg)
    host hblk (outerBlock_digestBytes_length ist) hrw_ost ?_
  refine RunsTo.refl ?_
  set blk_out := shaStateBytes (C.F (hmacOuterInit C.F key) (outerBlock (digestBytes ist)))
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x68#64) blk_out)
      (s0.readReg64 .x1 + 0x68#64) 32 := by
    have hlen : blk_out.length = 32 := shaStateBytes_length _
    rw [← hlen]; exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_out
  have hd_ost_saved : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  refine ⟨by fin_reg,
    ⟨by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
      FinSaved.of_agreesOutside hsaved hag_comp hd_ost_saved,
      Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
        (by simp) (by bv_omega) hag_comp⟩,
    by fin_reg, by fin_reg,
    by have hlen : blk_out.length = 32 := shaStateBytes_length _
       rw [← hlen]; exact readBytes_writeBytes_same s.mem _ blk_out (by rw [hlen]; decide)⟩

private structure StateF5Gen425 [LibsignalPlacement] (outBytes : List (BitVec 8))
    (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_425).base + 420#64
  common : FinCommon s0 s
  out_eq : s.mem.readBytes (s0.readReg64 .x0) 32 = outBytes

set_option maxHeartbeats 1600000 in
private theorem seg4a_425 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key pfx tail : List (BitVec 8)} {ist : ShaState} {s0 s : State}
    (hpre : FinMidPre key pfx tail s0)
    (hhmac : digestBytes (C.F (hmacOuterInit C.F key) (outerBlock (digestBytes ist))) =
      hmacWith C.F key (pfx ++ tail))
    (hs : StateF4Gen425 C.F key ist s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s
      (StateF5Gen425 (hmacWith C.F key (pfx ++ tail)) s0) := by
  rcases hs with ⟨hpc, ⟨hstat, hsp_s, hx29, hx26, hx27, hx28, hsaved, hframe⟩, hx19, hx20, host⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 32 := rw_of_perm_eq hframe.2 hpre.rw_out
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_out := C.F (hmacOuterInit C.F key) (outerBlock (digestBytes ist))
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_104_of_shaStateBytes s.mem (s0.readReg64 .x1) h_out host
  have hzero64 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
  iterate 11 s2_step
  have hd_fsp64_hm : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1) 0x90 :=
    hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩
  have hread128 := read32_seg4a_mid_local s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
    128#64 (h_out.get 6) (Or.inl rfl) hd_fsp64_hm hw6
  have hread132 := read32_seg4a_mid_local s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
    132#64 (h_out.get 7) (Or.inr rfl) hd_fsp64_hm hw7
  iterate 2 s2_step
  clear hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hread128 hread132 hd_fsp64_hm host
  iterate 15 s2_step
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg4a s.mem
    (s0.readReg64 .x0) (s0.readReg64 .x1) (s0.sp - 144#64) _ _ _ _ _ _ _ _
  have hd_hm_saved : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    hpre.disj_hm_fsp.sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_out_saved : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    hpre.disj_out_fsp.sub_right _ ⟨by decide, by bv_omega⟩
  refine ⟨by fin_reg,
    ⟨by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
      by rw [mem_setMem]; exact finSaved_seg4a hsaved hag1 hag2 hag3 hag4 hd_hm_saved hd_fsp64_saved hd_out_saved,
      by rw [mem_setMem]; exact frame_seg4a hframe hag1 hag2 hag3 hag4⟩,
    by rw [mem_setMem]
       exact (readBytes_write32_8_digestBytes _ (s0.readReg64 .x0) h_out _ _ _ _ _ _ _ _
         (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
         (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)).trans
         hhmac⟩

set_option maxHeartbeats 1600000 in
private theorem seg4_425 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key pfx tail : List (BitVec 8)} {ist : ShaState} {s0 s : State}
    (hpre : FinMidPre key pfx tail s0)
    (hhmac : digestBytes (C.F (hmacOuterInit C.F key) (outerBlock (digestBytes ist))) =
      hmacWith C.F key (pfx ++ tail))
    (hs : StateF4Gen425 C.F key ist s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (FinPost C.F key (pfx ++ tail) s0) := by
  refine (seg4a_425 hpre hhmac hs).trans fun s5 ⟨hpc5, ⟨hstat5, hsp5, hx29_5, hx26_5, hx27_5, hx28_5, hsaved5, hfr5⟩, hout5⟩ => ?_
  have hrw_fsp5 : s5.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hfr5.2 hpre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  rcases hsaved5 with ⟨hs29, hslr, hs25, hs24, hs23, hs22, hs21, hs20, hs19⟩
  have hs29' : s5.mem.read64 (s0.sp - 144#64 + 64#64) = s0.readReg64 .x29 := hs29
  have hslr' : s5.mem.read64 (s0.sp - 144#64 + 72#64) = s0.readReg64 .lr := hslr
  have hs25' : s5.mem.read64 (s0.sp - 144#64 + 80#64) = s0.readReg64 .x25 := hs25
  have hs24' : s5.mem.read64 (s0.sp - 144#64 + 96#64) = s0.readReg64 .x24 := hs24
  have hs23' : s5.mem.read64 (s0.sp - 144#64 + 104#64) = s0.readReg64 .x23 := hs23
  have hs22' : s5.mem.read64 (s0.sp - 144#64 + 112#64) = s0.readReg64 .x22 := hs22
  have hs21' : s5.mem.read64 (s0.sp - 144#64 + 120#64) = s0.readReg64 .x21 := hs21
  have hs20' : s5.mem.read64 (s0.sp - 144#64 + 128#64) = s0.readReg64 .x20 := hs20
  have hs19' : s5.mem.read64 (s0.sp - 144#64 + 136#64) = s0.readReg64 .x19 := hs19
  iterate 7 s2_step
  refine RunsTo.refl ⟨by simp (config := { decide := true }) only [arm64_norm], hstat5,
    ⟨by simp (config := { decide := true }) only [arm64_norm], fun r hr => ?_⟩, hout5, hfr5⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [arm64_norm, hx26_5, hx27_5, hx28_5]

private theorem seg2_to_end_425 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {key pfx tail : List (BitVec 8)} {s0 s : State}
    (hpre : FinMidPre key pfx tail s0)
    (hs : StateF1_425 C.F key pfx tail s0 s) :
    RunsTo ((blkPC_425).rebase (blkPl_425).base H) s (FinPost C.F key (pfx ++ tail) s0) := by
  by_cases hlt56 : tail.length < 56
  · exact (seg2_lt56_a_425 hpre hlt56 hs).trans fun _ hs2a =>
      (seg2_lt56_b_425 h_compress hpre hlt56 hs2a).trans fun _ hs3 =>
      (seg3a_425 hpre hs3).trans fun _ hs3b =>
      (seg3b_425 h_compress hpre hs3b).trans fun _ hs4 =>
        seg4_425 hpre (hmacWith_pfx_short C.F key pfx tail hpre.key_le hpre.pfx_mod hlt56).symm hs4
  · have hge56 : 56 ≤ tail.length := Nat.le_of_not_lt hlt56
    exact (seg2_ge56_ab_425 h_compress hpre hge56 hs).trans fun _ hs2b =>
      (seg2_ge56_c_425 hpre hs2b).trans fun _ hs2c =>
      (seg2_ge56_d_425 h_compress hpre hs2c).trans fun _ hs3 =>
      (seg3a_425 hpre hs3).trans fun _ hs3b =>
      (seg3b_425 h_compress hpre hs3b).trans fun _ hs4 =>
        seg4_425 hpre
          (hmacWith_pfx_two_blocks C.F key pfx tail hpre.key_le hpre.pfx_mod hge56 hpre.tail_lt).symm hs4

theorem finalize_fixed3_pfx_lt64_kdf_vm_sat [LibsignalPlacement] {C : Crypto}
    {H : LibsignalHooks} [hH : HkdfPlacedHooksExactSat C.F H]
    (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    {key pfx tail : List (BitVec 8)} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpre : FinPre3PfxGen fin3PlacedFakeB C.F key pfx tail s0) :
    RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s0 (FinPostSat C.F key (pfx ++ tail) s0) := by
  have heq425 : ∀ X, (blkPC_425).rebase (blkPl_425).base X =
      libsignalSessionLib.blockProgram lsmpl 425 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := (blkPC_425).rebase (blkPl_425).base X)
  let kp425 := ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl 425 H)
  have hpre_strip : FinPre3PfxGen fin3PlacedFakeB C.F key pfx tail (ProofLib.stripS kp425 s0) := by
    have hr : ∀ r, (ProofLib.stripS kp425 s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
    have hsp0 : (ProofLib.stripS kp425 s0).sp = s0.sp := by cases s0; rfl
    exact
      { pc_eq := (by cases s0; rfl : (ProofLib.stripS kp425 s0).pc = s0.pc).trans hpre.pc_eq,
        status := (by cases s0; rfl : (ProofLib.stripS kp425 s0).status = s0.status).trans hpre.status,
        key_le := hpre.key_le, tail_lt := hpre.tail_lt,
        hmac_st := by rw [hr, stripS_hmacStN]; exact hpre.hmac_st,
        rw_out := by rw [stripS_mem, hr]; exact stripExecOutside_rw kp425 s0.mem _ _ hpre.rw_out,
        rw_hm := by rw [stripS_mem, hr]; exact stripExecOutside_rw kp425 s0.mem _ _ hpre.rw_hm,
        rw_fsp := by rw [stripS_mem, hsp0]; exact stripExecOutside_rw kp425 s0.mem _ _ hpre.rw_fsp,
        disj_out_hm := by rw [hr, hr]; exact hpre.disj_out_hm,
        disj_out_fsp := by rw [hr, hsp0]; exact hpre.disj_out_fsp,
        disj_hm_fsp := by rw [hr, hsp0]; exact hpre.disj_hm_fsp,
        sp_aligned := by rw [hsp0]; exact hpre.sp_aligned }
  -- Piece 1: `+0 -> bl memset` (`s0 -> s1`, 0 `memset` calls)
  have hp1 : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s0
      (StateFPreMemset425 C.F key pfx tail s0) := by
    refine lift_block_to_379_vm (Pj := (blkPC_425).rebase (blkPl_425).base H)
      blkLib_eq_425 blk425_noSvc0 blk425_noMsr (by decide) (by decide) hcl
      (heq425 H ▸ (seg1a_425 hpre).trans fun _ hs0 => seg1b_pre_425 hpre hs0)
      (heq425 (hmacNoMemsetExcHooks C.F H s0.mem kp425) ▸
        (seg1a_425 hpre_strip).trans fun _ hs0 => seg1b_pre_425 hpre_strip hs0)
      (fun _ hs => hs.common.status) (fun _ hs => hs.common.status)
      fun s1 hvm1 hs1 => ?_
    rcases hs1 with ⟨hpc, hc, hlr, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hx23, hx24, hx25,
      hpad, hist, host, hobl⟩
    have hr0 : ∀ r, (ProofLib.stripS kp425 s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
    rw [hr0, stripS_readBytes] at hpad hist host
    rw [hr0, stripS_read64] at hobl
    exact ⟨(by cases s1; exact hpc), unstrip_finCommon hc hvm1.perm_eq,
      (by cases s1; exact hlr), (by cases s0; cases s1; exact hx0),
      (by cases s1; exact hx1), (by cases s1; exact hx2),
      (by cases s0; cases s1; exact hx19), (by cases s0; cases s1; exact hx20),
      (by cases s0; cases s1; exact hx21), (by cases s1; exact hx22),
      (by cases s1; exact hx23), (by cases s1; exact hx24), (by cases s1; exact hx25),
      hpad, hist, host, hobl⟩
  refine hp1.trans_full fun s1 hs1 hkf1 => ?_
  -- Piece 2: `bl memset` (`s1 -> s2`)
  have hp2 : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s1 fun s2 =>
      S2Frame s0.mem s2.mem
        [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)] ∧
      StateF1_425 C.F key pfx tail (s0.setMem s2.mem) s2 := by
    intro hL1
    rcases hs1 with ⟨hpc1, ⟨hstat1, hsp1, hx29_1, hx26_1, hx27_1, hx28_1, hsaved1, hfr1⟩,
      hlr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
      hpad1, hist1, host1, hobl1⟩
    set dst := s0.readReg64 .x1 + BitVec.ofNat 64 tail.length + 1#64
    set len := 63 - tail.length
    have hrw_hm1 : s1.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hfr1.2 hpre.rw_hm
    have hrw_fsp1 : s1.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hfr1.2 hpre.rw_fsp
    have hrw_dst : s1.mem.RW dst len :=
      hrw_hm1.sub (by have := hpre.tail_lt; dsimp only [dst, len]; bv_omega)
    have hsp1_al : (s1.sp &&& 15#64) = 0#64 := by
      rw [hsp1]; exact fsp_aligned hpre.sp_aligned
    obtain ⟨s2, hst2, hvm2, hacp2, htr2, hv2, hpc2, hstat2, hcc2, _, _, _, hs2_fr, hs2_ag⟩ :=
      placed_memset_budget_optAlloc_steps_sat (prog := (blkPC_379).rebase (blkPl_379).base H) (i := 379)
        hMemsetVm hstat1 hpc1 hx0_1 hx1_1 hx2_1 hlr1 hsp1_al hrw_dst
    have hfr_0_2 : S2Frame s0.mem s2.mem
        [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)] := by
      refine (S2Frame.of_frame hfr1).trans (hs2_fr.mono fun a ha r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      have ha_hm := ha (s0.readReg64 .x1, 0x90) (by simp)
      have := hpre.tail_lt; dsimp only [dst, len]; unfold OutsideRegion at ha_hm ⊢; bv_omega
    have hP1 : ∀ {a : BitVec 64}, s1.mem.permNoLazy a = some Perm.rw →
        (s1.mem.perm a).r = true ∧ s1.mem.isLazyFree a = false := fun {a} hnl => by
      obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl
      exact ⟨by rw [hp]; rfl, hlf⟩
    have hag_wb64 : AgreesOutside s1.mem (s1.mem.writeBytes dst (List.replicate len 0#8))
        (s0.readReg64 .x1) 64 :=
      (AgreesOutside.refl s1.mem (s0.readReg64 .x1) 64).writeBytes (List.replicate len 0#8)
        (by rw [List.length_replicate]; have := hpre.tail_lt; dsimp only [dst, len]; bv_omega)
    have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
      (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
    have hsaved2_0 : FinSaved s0 (s0.sp - 144#64) s2.mem :=
      AgreesOn.finSaved_of hs2_ag (FinSaved.of_agreesOutside hsaved1 hag_wb64 hd_hm64_saved)
        (fun a ha => hP1 (hrw_fsp1 a (by unfold InRegion at ha ⊢; bv_omega)))
    have hsaved2 : FinSaved (s0.setMem s2.mem) ((s0.setMem s2.mem).sp - 144#64) s2.mem := by
      cases s0; exact hsaved2_0
    have hbuf2 : s2.mem.readBytes (s0.readReg64 .x1) 64 =
        tail ++ [0x80#8] ++ List.replicate len 0#8 := by
      rw [AgreesOn.readBytes_eq hs2_ag (s0.readReg64 .x1) 64 (by decide)
        (fun a ha => hP1 (hrw_hm1 a (by unfold InRegion at ha ⊢; bv_omega)))]
      have hsplit : (s1.mem.writeBytes dst (List.replicate len 0#8)).readBytes (s0.readReg64 .x1) 64 =
          (s1.mem.writeBytes dst (List.replicate len 0#8)).readBytes (s0.readReg64 .x1) (tail.length + 1) ++
          (s1.mem.writeBytes dst (List.replicate len 0#8)).readBytes
            (s0.readReg64 .x1 + BitVec.ofNat 64 (tail.length + 1)) len := by
        rw [← readBytes_add]; congr 1; have := hpre.tail_lt; dsimp only [len]; omega
      have hdst_eq : s0.readReg64 .x1 + BitVec.ofNat 64 (tail.length + 1) = dst := by
        dsimp only [dst]; rw [BitVec.ofNat_add]; simp [BitVec.add_assoc]
      rw [hsplit, hdst_eq]
      have hl : (s1.mem.writeBytes dst (List.replicate len 0#8)).readBytes
          (s0.readReg64 .x1) (tail.length + 1) = tail ++ [0x80#8] := by
        by_cases h0 : len = 0
        · simp [h0, Memory.writeBytes]; exact hpad1
        · rw [readBytes_writeBytes_disjoint s1.mem (s0.readReg64 .x1) (tail.length + 1)
            dst (List.replicate len 0#8)]
          · exact hpad1
          · rw [List.length_replicate]; have := hpre.tail_lt; dsimp only [dst, len] at h0 ⊢
            unfold DisjointRegions; bv_omega
      have hr : (s1.mem.writeBytes dst (List.replicate len 0#8)).readBytes dst len =
          List.replicate len 0#8 := by
        simpa only [List.length_replicate] using
          readBytes_writeBytes_same s1.mem dst (List.replicate len 0#8)
            (by rw [List.length_replicate]; dsimp only [len]; omega)
      rw [hl, hr]
    have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
      unfold DisjointRegions; bv_omega
    have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
      unfold DisjointRegions; bv_omega
    have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
      unfold DisjointRegions; bv_omega
    have hx1_sm : (s0.setMem s2.mem).readReg64 .x1 = s0.readReg64 .x1 := by cases s0; rfl
    refine ⟨s2, hst2, hvm2, hacp2, htr2, hv2, ⟨hfr_0_2,
      ⟨hpc2,
        ⟨hstat2, (CallingConventionPreserved.sp_eq hcc2).trans hsp1,
          (CallingConventionPreserved.x29 hcc2).trans hx29_1,
          (CallingConventionPreserved.x26 hcc2).trans hx26_1,
          (CallingConventionPreserved.x27 hcc2).trans hx27_1,
          (CallingConventionPreserved.x28 hcc2).trans hx28_1,
          hsaved2, Frame.refl s2.mem _⟩,
        (CallingConventionPreserved.x19 hcc2).trans hx19_1,
        (CallingConventionPreserved.x20 hcc2).trans hx20_1,
        (CallingConventionPreserved.x21 hcc2).trans hx21_1,
        (CallingConventionPreserved.x22 hcc2).trans hx22_1,
        (CallingConventionPreserved.x23 hcc2).trans hx23_1,
        (CallingConventionPreserved.x24 hcc2).trans hx24_1,
        (CallingConventionPreserved.x25 hcc2).trans hx25_1,
        by rw [hx1_sm]; exact hbuf2,
        by rw [hx1_sm]
           exact (AgreesOn.readBytes_eq hs2_ag (s0.readReg64 .x1 + 0x40#64) 32 (by decide)
             (fun a ha => hP1 (hrw_hm1 a (by unfold InRegion at ha ⊢; bv_omega)))).trans
             ((hag_wb64.readBytes_eq hd_hm64_ist (by decide)).trans hist1),
        by rw [hx1_sm]
           exact (AgreesOn.readBytes_eq hs2_ag (s0.readReg64 .x1 + 0x68#64) 32 (by decide)
             (fun a ha => hP1 (hrw_hm1 a (by unfold InRegion at ha ⊢; bv_omega)))).trans
             ((hag_wb64.readBytes_eq hd_hm64_ost (by decide)).trans host1),
        by rw [hx1_sm]
           exact (AgreesOn.read64_eq hs2_ag (s0.readReg64 .x1 + 0x88#64)
             (fun a ha => hP1 (hrw_hm1 a (by unfold InRegion at ha ⊢; bv_omega)))).trans
             ((hag_wb64.read64_eq hd_hm64_obl).trans hobl1)⟩⟩,
      hst2.codeLoaded hL1⟩
  refine hp2.trans_full fun s2 ⟨hfr_0_2, hs2⟩ hkf2 => ?_
  -- Piece 3: `+76 -> ret` (`s2 -> sf`, 0 `memset` calls, anchored at `s0' := s0.setMem s2.mem`)
  have hcl2 : LibsignalCodeLoaded lsmpl s2.mem :=
    (hcl.of_keepsFrozen hkf1).of_keepsFrozen hkf2
  let s0' := s0.setMem s2.mem
  have hmid : FinMidPre key pfx tail s0' :=
    { key_le := hpre.key_le, pfx_mod := hpre.hmac_st.1, tail_lt := hpre.tail_lt,
      rw_out := hfr_0_2.rw_of_rw _ _ hpre.rw_out,
      rw_hm := hfr_0_2.rw_of_rw _ _ hpre.rw_hm,
      rw_fsp := hfr_0_2.rw_of_rw _ _ hpre.rw_fsp,
      disj_out_fsp := hpre.disj_out_fsp, disj_hm_fsp := hpre.disj_hm_fsp,
      sp_aligned := hpre.sp_aligned }
  have hs2_strip : StateF1_425 C.F key pfx tail (ProofLib.stripS kp425 s0')
      (ProofLib.stripS kp425 s2) := by
    rcases hs2 with ⟨hpc, ⟨hst, hsp_c, hx29, hx26, hx27, hx28, hsav, _⟩,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
    have hm_eq : (ProofLib.stripS kp425 s0').mem = (ProofLib.stripS kp425 s2).mem := by
      cases s0; cases s2; rfl
    have hr0 : ∀ r, (ProofLib.stripS kp425 s0').readReg64 r = s0'.readReg64 r := fun _ => by
      cases s0; rfl
    exact ⟨(by cases s2; exact hpc),
      ⟨(by cases s2; exact hst), (by cases s0; cases s2; exact hsp_c),
        (by cases s0; cases s2; exact hx29), (by cases s0; cases s2; exact hx26),
        (by cases s0; cases s2; exact hx27), (by cases s0; cases s2; exact hx28),
        (stripS_finSaved kp425 s0' s2).mpr hsav, hm_eq ▸ Frame.refl _ _⟩,
      (by cases s0; cases s2; exact hx19), (by cases s0; cases s2; exact hx20),
      (by cases s0; cases s2; exact hx21), (by cases s2; exact hx22),
      (by cases s2; exact hx23), (by cases s2; exact hx24), (by cases s2; exact hx25),
      by rw [hr0, stripS_readBytes]; exact hbuf,
      by rw [hr0, stripS_readBytes]; exact hist,
      by rw [hr0, stripS_readBytes]; exact host,
      by rw [hr0, stripS_read64]; exact hobl⟩
  have hp3 : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s2
      (FinPost C.F key (pfx ++ tail) s0') := by
    refine lift_block_to_379_vm (Pj := (blkPC_425).rebase (blkPl_425).base H)
      blkLib_eq_425 blk425_noSvc0 blk425_noMsr (by decide) (by decide) hcl2
      (heq425 H ▸ seg2_to_end_425 hH.compress256 hmid hs2)
      (heq425 (hmacNoMemsetExcHooks C.F H s2.mem kp425) ▸
        seg2_to_end_425 (hmacNoMemsetExcHooks_compress C.F H s2.mem kp425) (hmid.stripS kp425) hs2_strip)
      (fun _ hp => hp.2.1) (fun _ hp => hp.2.1)
      fun sf hvm3 ⟨hpc_f, hstat_f, hcs_f, hout_f, hfr_f⟩ => ?_
    have hr0 : ∀ r, (ProofLib.stripS kp425 s0').readReg64 r = s0'.readReg64 r := fun _ => by
      cases s0; rfl
    have hsp0 : (ProofLib.stripS kp425 s0').sp = s0'.sp := by cases s0; rfl
    have hm0 : (ProofLib.stripS kp425 s0').mem = ProofLib.stripExecOutside kp425 s2.mem := by
      cases s0; rfl
    rw [hr0, stripS_readBytes] at hout_f
    rw [hm0, stripS_mem, hr0, hr0, hsp0] at hfr_f
    refine ⟨(by cases s0; cases sf; exact hpc_f), (by cases sf; exact hstat_f),
      ⟨(by cases s0; cases sf; exact hcs_f.1), fun r hr => ?_⟩,
      hout_f, unstrip_frame hfr_f hvm3.perm_eq⟩
    have := hcs_f.2 r hr
    cases s0; cases sf; exact this
  exact hp3.mono fun sf ⟨hpc_f, hstat_f, hcs_f, hout_f, hfr_f⟩ =>
    ⟨hpc_f, hstat_f, hcs_f, hout_f, hfr_0_2.trans (S2Frame.of_frame hfr_f)⟩

end LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetFinSat
