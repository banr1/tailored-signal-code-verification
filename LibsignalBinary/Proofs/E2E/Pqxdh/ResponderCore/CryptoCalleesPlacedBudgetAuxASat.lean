/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFin -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlacedA -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegs
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt
import LibsignalBinary.Specifications.LibsignalE2E.State -- shake: keep

/-!
# `HookSat` Sibling of `CryptoCalleesPlacedBudgetAux`, Part A (`CryptoCalleesPlacedBudgetAuxASat`)

Provides `s2_compress256_multi_step_of_eq`, `finalize_fixed_gen_placed_runsToVm_sat` (Block `123`
`finalize_fixed` on `HmacStGen` under `[HkdfPlacedHooksExactBudgetSat C.F H]`), and Block `54`
(`GenericHkdf::extract`) segments `seg1b_hmc`, `seg1b1_long_hc256`, and `seg1b2_long_hmc`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxASat

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (ShaState chunks64 hmacWith toBEBytes)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   libsignalMutatedBlocks libsignalSessionLib lsmpl lsρ)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (EC88Long ECompLongPlaced EMemcpyLongPlaced FinGenPre HmacStGen
   agreesOutside_writeBytes_sub_sp0 bit_len_inner_gen_eq compress256Hook_multi_eq
   hmacWith_gen innerLastBlockGen innerLastBlockGen_length)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved ExtractGhost FinSaved Frame
   RW RunsTo RunsToFrom TraceEq agreesOutside_seg2a agreesOutside_seg3a agreesOutside_seg4a
   blkLib_123 blkLib_eq_123 blkPC_123 blkPC_54 blkPl_123 blkPl_54
   digestBytes digestBytes_eq_append effectiveSalt extPlacedFakeB extPlacedFakeB_off_328
   finPlacedFakeB finPlacedFakeB_off_0 finSaved_seg3a finSaved_seg4a
   frame_seg2a frame_seg3a frame_seg4a fsp_aligned
   hmacInnerInit hmacOuterInit lsCompress256Sym lsMemcpySym lsMemsetSym ls_externAt?_of_mem
   outerBlock outerBlock_digestBytes_length
   read32_words_at_104_of_shaStateBytes read32_words_at_64_of_shaStateBytes
   read64_seg2a_mid read64_seg3a_pad_32 read64_seg3a_pad_40
   readBytes_56_eq_append_8 readBytes_56_of_buf_eq
   readBytes_fsp_64_seg2 readBytes_fsp_64_seg3 readBytes_write32_8_digestBytes
   shaStateBytes_length
   toLEBytes_4_rev32 toLEBytes_8_read64 toLEBytes_8_rev32_append toLEBytes_8_rev64
   ult_7_of_lt_56 xor_63_of_lt_64 zeroExtend64_ofNat8 zeroExtend64_truncate32_ofNat64)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (CallingConventionPreserved.x19 CallingConventionPreserved.x20
   CallingConventionPreserved.x21 CallingConventionPreserved.x22
   CallingConventionPreserved.x27 CallingConventionPreserved.x29
   EC88 EMemcpyPlaced ExtCommon ExtSaved_and_Frame_of_agreesOutside_328
   HmacSt.of_writeBytes_32_write8_pos S2Frame
   agreesOutside_sp0_write8 disj_stk_sub_right rw_stk_sub)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
  (AgreesOn.finSaved_of AgreesOn.read64_eq AgreesOn.readBytes_eq)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt.FinX (read32_seg4a_mid_x)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (MemcpyClobber applyMemcpyClobber)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux (stripExecOutside_rw unstrip_frame)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
  (hmacCompressOnlyExcHooks hmacCompressOnlyExcHooks_compress
   placed_memcpy_budget_steps_sat_exact placed_memset_budget_steps_sat)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat
  (FinCommon FinPost RunsToVm blk123_noMsr blk123_noSvc0 finSaved_of_seg1a
   lift_block_vm_compress_only mem_setMem rw_of_perm_eq s2_compress256_step_of_eq
   stripS_finSaved stripS_mem stripS_read64 stripS_read8 stripS_readBytes unstrip_finCommon)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (CallingConventionPreserved.x23 CallingConventionPreserved.x24 CallingConventionPreserved.x25
   CallingConventionPreserved.x26 CallingConventionPreserved.x28)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat (FinPostSat)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

@[local simp, local arm64_norm]
private theorem extractLsb'_0_64_zero128 : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl

@[local simp, local arm64_norm]
private theorem extractLsb'_64_64_zero128 : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl

private theorem ost_eq_seg3a_local {m m₄ : Memory} {hm fsp : BitVec 64} {bs : List (BitVec 8)}
    {m₁ m₂ m₃ : Memory}
    (host : m.readBytes (hm + 0x68#64) 32 = bs)
    (hag1 : AgreesOutside m m₁ hm 64)
    (hag2 : AgreesOutside m₁ m₂ fsp 64)
    (hag3 : AgreesOutside m₂ m₃ hm 64)
    (hag4 : AgreesOutside m₃ m₄ fsp 64)
    (hd_hm64_ost : DisjointRegions hm 64 (hm + 0x68#64) 32)
    (hd_fsp64_ost : DisjointRegions fsp 64 (hm + 0x68#64) 32) :
    m₄.readBytes (hm + 0x68#64) 32 = bs :=
  (hag4.readBytes_eq hd_fsp64_ost (by decide)).trans
    ((hag3.readBytes_eq hd_hm64_ost (by decide)).trans
      ((hag2.readBytes_eq hd_fsp64_ost (by decide)).trans
        ((hag1.readBytes_eq hd_hm64_ost (by decide)).trans host)))

local macro "fin_reg_local" : tactic =>
  `(tactic| (
    try rw [State.readReg64_setMem]
    try rw [State.pc_setMem]
    try rw [State.sp_setMem]
    try rw [State.status_setMem]
    simp (config := { decide := true }) only [arm64_norm, *]))

/-! ## 1. Multi-Block `compress256Hook` Step & `stripS_hmacStGen` -/

/-- Step through multi-block `compress256` from `H lsCompress256Sym = some (compress256Hook C.F)` alone. -/
public theorem s2_compress256_multi_step_of_eq [LibsignalPlacement] {prog : Program} {i : Nat}
    {C : Crypto} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_c256 : H lsCompress256Sym = some (compress256Hook C.F))
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
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, h_c256]
  have hstate := compress256Hook_multi_eq C.F hx0 hx1 hx2 hlr hst hblk
  have hkeep : s.mem.KeepsFrozen (compress256Hook C.F s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (compress256Hook C.F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

public theorem stripS_hmacStGen (kp : BitVec 64 → Bool)
    {F : ShaState → List (BitVec 8) → ShaState} {s : State} {a : BitVec 64}
    {key blocks rem : List (BitVec 8)} :
    HmacStGen (ProofLib.stripS kp s).mem a F key blocks rem ↔
      HmacStGen s.mem a F key blocks rem := by
  unfold HmacStGen
  simp only [stripS_read8, stripS_read64, stripS_readBytes]

/-! ## 2. Block `123` (`finalize_fixed` on `HmacStGen`) `RunsToVm` under `HkdfPlacedHooksBudgetSat` -/

private structure StateGF0p [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 28#64
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x0
  x1_eq   : s.readReg64 .x1 = s0.readReg64 .x1
  hmac_st : HmacStGen s.mem (s0.readReg64 .x1) F key blocks rem

private structure StateGFPreMemset123 [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = lsρ lsMemsetSym
  common : FinCommon s0 s
  lr_eq  : s.readReg64 .lr = (blkPl_123).base + 76#64
  x0_eq  : s.readReg64 .x0 = s0.readReg64 .x1 + BitVec.ofNat 64 rem.length + 1#64
  x1_eq  : (s.readReg64 .x1).truncate 8 = 0#8
  x2_eq  : (s.readReg64 .x2).toNat = 63 - rem.length
  x19_eq : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq : s.readReg64 .x22 = 0x80#64
  x23_eq : s.readReg64 .x23 = BitVec.ofNat 64 rem.length
  x24_eq : s.readReg64 .x24 = BitVec.ofNat 64 (1 + blocks.length / 64)
  x25_eq : s.readReg64 .x25 = BitVec.ofNat 64 (63 - rem.length)
  pad_eq : s.mem.readBytes (s0.readReg64 .x1) (rem.length + 1) = rem ++ [0x80#8]
  ist_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes ((chunks64 blocks).foldl F (hmacInnerInit F key))
  ost_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateGF1 [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 76#64
  common : FinCommon s0 s
  x19_eq : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq : s.readReg64 .x22 = 0x80#64
  x23_eq : s.readReg64 .x23 = BitVec.ofNat 64 rem.length
  x24_eq : s.readReg64 .x24 = BitVec.ofNat 64 (1 + blocks.length / 64)
  x25_eq : s.readReg64 .x25 = BitVec.ofNat 64 (63 - rem.length)
  buf_eq : s.mem.readBytes (s0.readReg64 .x1) 64 =
    rem ++ [0x80#8] ++ List.replicate (63 - rem.length) 0#8
  ist_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes ((chunks64 blocks).foldl F (hmacInnerInit F key))
  ost_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateGF2 [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 176#64
  common : FinCommon s0 s
  x0_eq  : s.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64
  x1_eq  : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq  : s.readReg64 .x2 = 1#64
  x19_eq : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq : s.readReg64 .x22 = 0x80#64
  blk_eq : s.mem.readBytes (s0.sp - 144#64) 64 = innerLastBlockGen blocks rem
  ist_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes ((chunks64 blocks).foldl F (hmacInnerInit F key))
  ost_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateGF3 [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 180#64
  common : FinCommon s0 s
  x19_eq : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq : s.readReg64 .x22 = 0x80#64
  ist_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes
      (F ((chunks64 blocks).foldl F (hmacInnerInit F key)) (innerLastBlockGen blocks rem))
  ost_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateGF3b [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 304#64
  common : FinCommon s0 s
  x0_eq  : s.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64
  x1_eq  : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq  : s.readReg64 .x2 = 1#64
  x19_eq : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq : s.readReg64 .x20 = s0.readReg64 .x1
  blk_eq : s.mem.readBytes (s0.sp - 144#64) 64 =
    outerBlock (digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
      (innerLastBlockGen blocks rem)))
  ost_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)

private structure StateGF4 [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 308#64
  common : FinCommon s0 s
  x19_eq : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq : s.readReg64 .x20 = s0.readReg64 .x1
  ost_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 =
    shaStateBytes (F (hmacOuterInit F key)
      (outerBlock (digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
        (innerLastBlockGen blocks rem)))))

private structure StateGF5 [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 420#64
  common : FinCommon s0 s
  out_eq : s.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key (blocks ++ rem)

private structure FinGenMidPre123 (key blocks rem : List (BitVec 8)) (s0 : State) : Prop where
  key_le       : key.length ≤ 64
  blk_mod      : blocks.length % 64 = 0
  blk_le       : blocks.length ≤ 192
  rem_lt       : rem.length < 56
  rw_out       : RW s0.mem (s0.readReg64 .x0) 32
  rw_hm        : RW s0.mem (s0.readReg64 .x1) 0x90
  rw_fsp       : RW s0.mem (s0.sp - 144#64) 144
  disj_out_fsp : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64) 144
  disj_hm_fsp  : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64) 144
  sp_aligned   : (s0.sp &&& 0b1111#64) = 0#64

private theorem FinGenMidPre123.stripS {key blocks rem : List (BitVec 8)} {s0 : State}
    (h : FinGenMidPre123 key blocks rem s0) (kp : BitVec 64 → Bool) :
    FinGenMidPre123 key blocks rem (ProofLib.stripS kp s0) := by
  have hr : ∀ r, (ProofLib.stripS kp s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  have hsp0 : (ProofLib.stripS kp s0).sp = s0.sp := by cases s0; rfl
  exact
    { key_le := h.key_le, blk_mod := h.blk_mod, blk_le := h.blk_le, rem_lt := h.rem_lt,
      rw_out := by rw [stripS_mem, hr]; exact stripExecOutside_rw kp s0.mem _ _ h.rw_out,
      rw_hm := by rw [stripS_mem, hr]; exact stripExecOutside_rw kp s0.mem _ _ h.rw_hm,
      rw_fsp := by rw [stripS_mem, hsp0]; exact stripExecOutside_rw kp s0.mem _ _ h.rw_fsp,
      disj_out_fsp := by rw [hr, hsp0]; exact h.disj_out_fsp,
      disj_hm_fsp := by rw [hr, hsp0]; exact h.disj_hm_fsp,
      sp_aligned := by rw [hsp0]; exact h.sp_aligned }

private theorem gseg1a_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    {key blocks rem : List (BitVec 8)} {s0 : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s0 (StateGF0p C.F key blocks rem s0) := by
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
    { pc_eq := by fin_reg_local
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := by
            rw [mem_setMem]
            exact finSaved_of_seg1a s0 s0.mem
          frame := by
            rw [mem_setMem]
            exact Frame.trans_agreesOutside (Frame.refl s0.mem _) (by simp) hag }
      x0_eq := by fin_reg_local, x1_eq := by fin_reg_local
      hmac_st := by
        rw [mem_setMem]
        exact HmacStGen.of_agreesOutside hpre.hmac_st hag hpre.disj_hm_fsp.symm }

private theorem gseg1b_pre_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF0p C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s
      (StateGFPreMemset123 C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hhmac⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  rcases hhmac with ⟨hmod, hblk_le, hmsg_lt64, hmsg_eq, hpos_eq, hin_eq, hibl_eq, hout_eq, hobl_eq⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe hpre.rw_hm
  have hcw_pos : s.mem.canWrite (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 1 = true :=
    hrw_hm.canWrite_sub (by bv_omega) (by decide)
  have hze32 := zeroExtend64_truncate32_ofNat64 hmsg_lt64
  have hze64 := zeroExtend64_ofNat8 hmsg_lt64
  have hxor63 := xor_63_of_lt_64 hmsg_lt64
  iterate 12 s2_step
  have htoNat_sub : (BitVec.ofNat 64 (63 - rem.length)).toNat = 63 - rem.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine RunsTo.refl ?_
  set m_pre := s.mem.write8 (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 128#8
  have hag_pre : AgreesOutside s.mem m_pre (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 1 := by
    dsimp only [m_pre]; agrees_outside_writes
  have hd_pre_saved : DisjointRegions (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 1
      (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by have := hpre.rem_lt; bv_omega⟩).sub_right _
      ⟨by decide, by bv_omega⟩
  have hd_pre_ist : DisjointRegions (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 1
      (s0.readReg64 .x1 + 0x40#64) 32 := by
    have := hpre.rem_lt; unfold DisjointRegions; bv_omega
  have hd_pre_ost : DisjointRegions (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 1
      (s0.readReg64 .x1 + 0x68#64) 32 := by
    have := hpre.rem_lt; unfold DisjointRegions; bv_omega
  have hd_pre_obl : DisjointRegions (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 1
      (s0.readReg64 .x1 + 0x88#64) 8 := by
    have := hpre.rem_lt; unfold DisjointRegions; bv_omega
  have hpad : m_pre.readBytes (s0.readReg64 .x1) (rem.length + 1) = rem ++ [0x80#8] := by
    rw [readBytes_add m_pre (s0.readReg64 .x1) rem.length 1]
    have hl : m_pre.readBytes (s0.readReg64 .x1) rem.length = rem := by
      by_cases h0 : rem.length = 0
      · cases rem with | nil => rfl | cons _ _ => cases h0
      · refine (hag_pre.readBytes_eq ?_ (by have := hpre.rem_lt; omega)).trans hmsg_eq
        have := hpre.rem_lt; unfold DisjointRegions; bv_omega
    have hr : m_pre.readBytes (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 1 = [0x80#8] := by
      dsimp only [m_pre]
      simp [Memory.readBytes, Memory.read8_write8_same]
    rw [hl, hr]
  refine
    { pc_eq := rfl
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := by rw [mem_setMem]; exact FinSaved.of_agreesOutside hsaved hag_pre hd_pre_saved
          frame := by
            rw [mem_setMem]
            have := hpre.rem_lt
            exact Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
              (by simp) (by bv_omega) hag_pre }
      lr_eq := by fin_reg_local
      x0_eq := by simp only [arm64_norm]
      x1_eq := by simp (config := { decide := true }) only [arm64_norm]
      x2_eq := by simpa only [arm64_norm] using htoNat_sub
      x19_eq := by fin_reg_local, x20_eq := by fin_reg_local, x21_eq := by fin_reg_local,
      x22_eq := by fin_reg_local, x23_eq := by fin_reg_local, x24_eq := by fin_reg_local,
      x25_eq := by fin_reg_local
      pad_eq := by rw [mem_setMem]; exact hpad
      ist_eq := by rw [mem_setMem]; exact (hag_pre.readBytes_eq hd_pre_ist (by decide)).trans hin_eq
      ost_eq := by rw [mem_setMem]; exact (hag_pre.readBytes_eq hd_pre_ost (by decide)).trans hout_eq
      obl_eq := by rw [mem_setMem]; exact (hag_pre.read64_eq hd_pre_obl).trans hobl_eq }

set_option maxHeartbeats 800000 in
private theorem gseg2a_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hmid : FinGenMidPre123 key blocks rem s0)
    (hs : StateGF1 C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s (StateGF2 C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe hmid.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe hmid.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hmid.sp_aligned
  have hult_7 := ult_7_of_lt_56 hmid.rem_lt
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hmid.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
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
    (hmid.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_ist : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x40#64) 32 :=
    (hmid.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hmid.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_obl : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x88#64) 8 :=
    (hmid.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := by fin_reg_local
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := by
            rw [mem_setMem]
            exact FinSaved.of_agreesOutside
              (FinSaved.of_agreesOutside (FinSaved.of_agreesOutside hsaved hag1 hd_fsp64_saved)
                hag2 hd_hm64_saved) hag3 hd_fsp64_saved
          frame := by
            rw [mem_setMem]
            exact frame_seg2a hframe hag1 hag2 hag3 }
      x0_eq := by fin_reg_local, x1_eq := by fin_reg_local, x2_eq := by fin_reg_local,
      x19_eq := by fin_reg_local, x20_eq := by fin_reg_local, x21_eq := by fin_reg_local,
      x22_eq := by fin_reg_local
      blk_eq := by
        rw [mem_setMem]
        refine (readBytes_fsp_64_seg2 _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
        rw [toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
            toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_rev64,
            readBytes_56_eq_append_8 s.mem (s0.readReg64 .x1),
            readBytes_56_of_buf_eq s.mem (s0.readReg64 .x1) rem hbuf hmid.rem_lt,
            bit_len_inner_gen_eq hmid.blk_mod hmid.blk_le hmid.rem_lt]
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

private theorem gseg2b_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    (hc256 : Hk lsCompress256Sym = some (compress256Hook C.F))
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hmid : FinGenMidPre123 key blocks rem s0)
    (hs : StateGF2 C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s (StateGF3 C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hblk, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe hmid.rw_hm
  have hrw_ist : s.mem.RW (s0.readReg64 .x1 + 0x40#64) 32 := hrw_hm.sub (by bv_omega)
  s2_step
  refine s2_compress256_step_of_eq hc256
    (stPtr := s0.readReg64 .x1 + 0x40#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_123).base + 180#64)
    (st := (chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
    (blk := innerLastBlockGen blocks rem)
    hstat rfl
    (by fin_reg_local) (by fin_reg_local) (by fin_reg_local) rfl
    hist hblk (innerLastBlockGen_length hmid.rem_lt) hrw_ist ?_
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
    (hmid.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_ist_ost :
      DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_ist_obl :
      DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := by fin_reg_local
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := FinSaved.of_agreesOutside hsaved hag_comp hd_ist_saved
          frame := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin_reg_local, x20_eq := by fin_reg_local,
      x21_eq := by fin_reg_local, x22_eq := by fin_reg_local
      ist_eq := by
        have hlen : blk_in.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact readBytes_writeBytes_same s.mem _ blk_in (by rw [hlen]; decide)
      ost_eq := (hag_comp.readBytes_eq hd_ist_ost (by decide)).trans host
      obl_eq := (hag_comp.read64_eq hd_ist_obl).trans hobl }

set_option maxHeartbeats 800000 in
private theorem gseg3a_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hmid : FinGenMidPre123 key blocks rem s0)
    (hs : StateGF3 C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s (StateGF3b C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe hmid.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe hmid.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hmid.sp_aligned
  set h_in := C.F ((chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
    (innerLastBlockGen blocks rem)
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_64_of_shaStateBytes s.mem (s0.readReg64 .x1) h_in hist
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hmid.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
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
    (hmid.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hmid.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  refine
    { pc_eq := by fin_reg_local
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg3a hsaved hag1 hag2 hag3 hag4 hd_hm64_saved hd_fsp64_saved
          frame := by
            rw [mem_setMem]
            exact frame_seg3a hframe hag1 hag2 hag3 hag4 }
      x0_eq := by fin_reg_local, x1_eq := by fin_reg_local, x2_eq := by fin_reg_local,
      x19_eq := by fin_reg_local, x20_eq := by fin_reg_local
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
        exact ost_eq_seg3a_local host hag1 hag2 hag3 hag4 hd_hm64_ost hd_fsp64_ost }

private theorem gseg3b_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    (hc256 : Hk lsCompress256Sym = some (compress256Hook C.F))
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hmid : FinGenMidPre123 key blocks rem s0)
    (hs : StateGF3b C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s (StateGF4 C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hblk, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe hmid.rw_hm
  have hrw_ost : s.mem.RW (s0.readReg64 .x1 + 0x68#64) 32 := hrw_hm.sub (by bv_omega)
  set h_in := C.F ((chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
    (innerLastBlockGen blocks rem)
  s2_step
  refine s2_compress256_step_of_eq hc256
    (stPtr := s0.readReg64 .x1 + 0x68#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_123).base + 308#64)
    (st := hmacOuterInit C.F key) (blk := outerBlock (digestBytes h_in))
    hstat rfl
    (by fin_reg_local) (by fin_reg_local) (by fin_reg_local) rfl
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
    (hmid.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  refine
    { pc_eq := by fin_reg_local
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := FinSaved.of_agreesOutside hsaved hag_comp hd_ost_saved
          frame := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin_reg_local, x20_eq := by fin_reg_local
      ost_eq := by
        have hlen : blk_out.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact readBytes_writeBytes_same s.mem _ blk_out (by rw [hlen]; decide) }

private theorem gseg4a_disj_mid {key blocks rem : List (BitVec 8)} {s0 : State}
    (hmid : FinGenMidPre123 key blocks rem s0) :
    DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1) 0x90 ∧
    DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64 + 0x40#64) 0x50 ∧
    DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 ∧
    DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
  ⟨hmid.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩,
   hmid.disj_hm_fsp.sub_right _ ⟨by decide, by bv_omega⟩,
   by unfold DisjointRegions; bv_omega,
   hmid.disj_out_fsp.sub_right _ ⟨by decide, by bv_omega⟩⟩

set_option maxHeartbeats 800000 in
private theorem gseg4a_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hmid : FinGenMidPre123 key blocks rem s0)
    (hs : StateGF4 C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s (StateGF5 C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe hmid.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe hmid.rw_fsp
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 32 := rw_of_perm_eq hframe hmid.rw_out
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hmid.sp_aligned
  set h_out := C.F (hmacOuterInit C.F key)
    (outerBlock (digestBytes (C.F ((chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
      (innerLastBlockGen blocks rem))))
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_104_of_shaStateBytes s.mem (s0.readReg64 .x1) h_out host
  have hzero64 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
  iterate 11 s2_step
  have hd_fsp64_hm := (gseg4a_disj_mid hmid).1
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
  obtain ⟨_, hd_hm_saved, hd_fsp64_saved, hd_out_saved⟩ := gseg4a_disj_mid hmid
  refine
    { pc_eq := by fin_reg_local
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg4a hsaved hag1 hag2 hag3 hag4 hd_hm_saved hd_fsp64_saved hd_out_saved
          frame := by
            rw [mem_setMem]
            exact frame_seg4a hframe hag1 hag2 hag3 hag4 }
      out_eq := by
        rw [mem_setMem]
        exact (readBytes_write32_8_digestBytes _ (s0.readReg64 .x0) h_out _ _ _ _ _ _ _ _
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
          (toLEBytes_4_rev32 _)).trans
          (hmacWith_gen C.F key blocks rem hmid.key_le hmid.blk_mod hmid.rem_lt).symm }

private theorem gseg4b_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hmid : FinGenMidPre123 key blocks rem s0)
    (hs : StateGF5 C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s
      (FinPost C.F key (blocks ++ rem) s0) := by
  rcases hs with ⟨hpc, hcom, hout⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe hmid.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hmid.sp_aligned
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

private theorem gseg2_to_end_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    (hc256 : Hk lsCompress256Sym = some (compress256Hook C.F))
    {key blocks rem : List (BitVec 8)} {s0 s1 : State}
    (hmid : FinGenMidPre123 key blocks rem s0) (hs1 : StateGF1 C.F key blocks rem s0 s1) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s1 (FinPost C.F key (blocks ++ rem) s0) :=
  (gseg2a_123 hmid hs1).trans fun _ hs2 => (gseg2b_123 hc256 hmid hs2).trans fun _ hs3 =>
  (gseg3a_123 hmid hs3).trans fun _ hs3b => (gseg3b_123 hc256 hmid hs3b).trans fun _ hs4 =>
  (gseg4a_123 hmid hs4).trans fun _ hs5 => gseg4b_123 hmid hs5

/-- Full relocatable `RunsToVm` contract of Block `123` (`finalize_fixed` on `HmacStGen`)
under `[HkdfPlacedHooksExactBudgetSat C.F H]` with `FinPostSat` (`S2Frame`). -/
public theorem finalize_fixed_gen_placed_runsToVm_sat [LibsignalPlacement] {C : Crypto}
    {H : LibsignalHooks} [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {key blocks rem : List (BitVec 8)} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s0
      (FinPostSat C.F key (blocks ++ rem) s0) := by
  have heq123 : ∀ X, (blkPC_123).rebase (blkPl_123).base X =
      libsignalSessionLib.blockProgram lsmpl 123 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := (blkPC_123).rebase (blkPl_123).base X)
  let Q123 := libsignalSessionLib.blockProgram lsmpl 123 (hmacCompressOnlyExcHooks C.F H)
  let kp123 := ProofLib.progKeep Q123
  have hpre_strip : FinGenPre finPlacedFakeB C.F key blocks rem (ProofLib.stripS kp123 s0) := by
    have hr : ∀ r, (ProofLib.stripS kp123 s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
    have hsp0 : (ProofLib.stripS kp123 s0).sp = s0.sp := by cases s0; rfl
    exact
      { pc_eq := (by cases s0; rfl : (ProofLib.stripS kp123 s0).pc = s0.pc).trans hpre.pc_eq,
        status := (by cases s0; rfl : (ProofLib.stripS kp123 s0).status = s0.status).trans hpre.status,
        key_le := hpre.key_le, rem_lt := hpre.rem_lt,
        hmac_st := by rw [hr, stripS_hmacStGen]; exact hpre.hmac_st,
        rw_out := by rw [stripS_mem, hr]; exact stripExecOutside_rw kp123 s0.mem _ _ hpre.rw_out,
        rw_hm := by rw [stripS_mem, hr]; exact stripExecOutside_rw kp123 s0.mem _ _ hpre.rw_hm,
        rw_fsp := by rw [stripS_mem, hsp0]; exact stripExecOutside_rw kp123 s0.mem _ _ hpre.rw_fsp,
        disj_out_hm := by rw [hr, hr]; exact hpre.disj_out_hm,
        disj_out_fsp := by rw [hr, hsp0]; exact hpre.disj_out_fsp,
        disj_hm_fsp := by rw [hr, hsp0]; exact hpre.disj_hm_fsp,
        sp_aligned := by rw [hsp0]; exact hpre.sp_aligned }
  have hp1 : RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s0
      (StateGFPreMemset123 C.F key blocks rem s0) := by
    refine lift_block_vm_compress_only (Pj := (blkPC_123).rebase (blkPl_123).base H)
      blkLib_eq_123 blk123_noSvc0 blk123_noMsr (by decide) (by decide) hcl
      (heq123 H ▸ (gseg1a_123 hpre).trans fun _ hs0 => gseg1b_pre_123 hpre hs0)
      (heq123 _ ▸ (gseg1a_123 hpre_strip).trans fun _ hs0 => gseg1b_pre_123 hpre_strip hs0)
      (fun _ hs => hs.common.status) (fun _ hs => hs.common.status) fun s1 hvm1 hs1 => ?_
    rcases hs1 with ⟨hpc, hc, hlr, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hx23, hx24, hx25,
      hpad, hist, host, hobl⟩
    have hr0 : ∀ r, (ProofLib.stripS kp123 s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
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
  have hp2 : RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s1 fun s2 =>
      S2Frame s0.mem s2.mem
        [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)] ∧
      StateGF1 C.F key blocks rem (s0.setMem s2.mem) s2 := by
    intro hL1
    rcases hs1 with ⟨hpc1, ⟨hstat1, hsp1, hx29_1, hx26_1, hx27_1, hx28_1, hsaved1, hfr1⟩,
      hlr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
      hpad1, hist1, host1, hobl1⟩
    set dst := s0.readReg64 .x1 + BitVec.ofNat 64 rem.length + 1#64
    set len := 63 - rem.length
    have hrw_hm1 : s1.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hfr1 hpre.rw_hm
    have hrw_fsp1 : s1.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hfr1 hpre.rw_fsp
    have hrw_dst : s1.mem.RW dst len :=
      hrw_hm1.sub (by have := hpre.rem_lt; dsimp only [dst, len]; bv_omega)
    have hsp1_al : (s1.sp &&& 15#64) = 0#64 := by rw [hsp1]; exact fsp_aligned hpre.sp_aligned
    obtain ⟨s2, hst2, hvm2, htr2, hv2, hpc2, hstat2, hcc2, _, _, _, hs2_fr, hs2_ag⟩ :=
      placed_memset_budget_steps_sat (prog := (blkPC_123).rebase (blkPl_123).base H) (i := 123)
        hH.memset hstat1 hpc1 hx0_1 hx1_1 hx2_1 hlr1 hsp1_al hrw_dst
    have hfr_0_2 : S2Frame s0.mem s2.mem
        [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)] := by
      refine (S2Frame.of_frame hfr1).trans (hs2_fr.mono fun a ha r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      have ha_hm := ha (s0.readReg64 .x1, 0x90) (by simp)
      have := hpre.rem_lt; dsimp only [dst, len]; unfold OutsideRegion at ha_hm ⊢; bv_omega
    have hP1 : ∀ {a : BitVec 64}, s1.mem.permNoLazy a = some Perm.rw →
        (s1.mem.perm a).r = true ∧ s1.mem.isLazyFree a = false := fun {a} hnl => by
      obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl
      exact ⟨by rw [hp]; rfl, hlf⟩
    have hag_wb : AgreesOutside s1.mem (s1.mem.writeBytes dst (List.replicate len 0#8)) dst len := by
      have hlen_r : (List.replicate len 0#8).length = len := List.length_replicate
      conv_rhs => rw [← hlen_r]
      exact ProofLib.AgreesOutside.writeBytes_self s1.mem dst (List.replicate len 0#8)
    have hd_dst_saved : DisjointRegions dst len (s0.sp - 144#64 + 0x40#64) 0x50 :=
      (hpre.disj_hm_fsp.sub_left dst ⟨by have := hpre.rem_lt; dsimp only [dst, len]; bv_omega,
        by have := hpre.rem_lt; dsimp only [dst, len]; bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
    have hsaved2 : FinSaved (s0.setMem s2.mem) ((s0.setMem s2.mem).sp - 144#64) s2.mem :=
      AgreesOn.finSaved_of hs2_ag (FinSaved.of_agreesOutside hsaved1 hag_wb hd_dst_saved)
        (fun a ha => hP1 (hrw_fsp1 a (by rw [State.sp_setMem] at ha; unfold InRegion at ha ⊢; bv_omega)))
    have hbuf2 : s2.mem.readBytes (s0.readReg64 .x1) 64 =
        rem ++ [0x80#8] ++ List.replicate len 0#8 := by
      rw [AgreesOn.readBytes_eq hs2_ag (s0.readReg64 .x1) 64 (by decide)
        (fun a ha => hP1 (hrw_hm1 a (by unfold InRegion at ha ⊢; bv_omega)))]
      have hsplit : (s1.mem.writeBytes dst (List.replicate len 0#8)).readBytes (s0.readReg64 .x1) 64 =
          (s1.mem.writeBytes dst (List.replicate len 0#8)).readBytes (s0.readReg64 .x1) (rem.length + 1) ++
          (s1.mem.writeBytes dst (List.replicate len 0#8)).readBytes
            (s0.readReg64 .x1 + BitVec.ofNat 64 (rem.length + 1)) len := by
        rw [← ProofLib.readBytes_add]; congr 1; have := hpre.rem_lt; dsimp only [len]; omega
      have hdst_eq : s0.readReg64 .x1 + BitVec.ofNat 64 (rem.length + 1) = dst := by
        dsimp only [dst]; rw [BitVec.ofNat_add]; simp [BitVec.add_assoc]
      rw [hsplit, hdst_eq]
      have hl : (s1.mem.writeBytes dst (List.replicate len 0#8)).readBytes
          (s0.readReg64 .x1) (rem.length + 1) = rem ++ [0x80#8] := by
        by_cases h0 : len = 0
        · simp [h0, Memory.writeBytes]; exact hpad1
        · rw [ProofLib.readBytes_writeBytes_disjoint s1.mem (s0.readReg64 .x1) (rem.length + 1)
            dst (List.replicate len 0#8)]
          · exact hpad1
          · rw [List.length_replicate]; have := hpre.rem_lt; dsimp only [dst, len] at h0 ⊢
            unfold DisjointRegions; bv_omega
      have hr : (s1.mem.writeBytes dst (List.replicate len 0#8)).readBytes dst len =
          List.replicate len 0#8 := by
        have hlen_r : (List.replicate len 0#8).length = len := List.length_replicate
        conv => lhs; arg 3; rw [← hlen_r]
        exact ProofLib.readBytes_writeBytes_same s1.mem dst (List.replicate len 0#8)
          (by rw [hlen_r]; dsimp only [len]; omega)
      rw [hl, hr]
    have hd_dst_ist : DisjointRegions dst len (s0.readReg64 .x1 + 0x40#64) 32 := by
      have := hpre.rem_lt; dsimp only [dst, len]; unfold DisjointRegions; bv_omega
    have hd_dst_ost : DisjointRegions dst len (s0.readReg64 .x1 + 0x68#64) 32 := by
      have := hpre.rem_lt; dsimp only [dst, len]; unfold DisjointRegions; bv_omega
    have hd_dst_obl : DisjointRegions dst len (s0.readReg64 .x1 + 0x88#64) 8 := by
      have := hpre.rem_lt; dsimp only [dst, len]; unfold DisjointRegions; bv_omega
    refine ⟨s2, hst2, hvm2, htr2, hv2, ⟨hfr_0_2,
      ⟨hpc2, ⟨hstat2, (CallingConventionPreserved.sp_eq hcc2).trans hsp1,
          (CallingConventionPreserved.x29 hcc2).trans hx29_1,
          (CallingConventionPreserved.x26 hcc2).trans hx26_1,
          (CallingConventionPreserved.x27 hcc2).trans hx27_1,
          (CallingConventionPreserved.x28 hcc2).trans hx28_1, hsaved2, Frame.refl s2.mem _⟩,
        (CallingConventionPreserved.x19 hcc2).trans hx19_1,
        (CallingConventionPreserved.x20 hcc2).trans hx20_1,
        (CallingConventionPreserved.x21 hcc2).trans hx21_1,
        (CallingConventionPreserved.x22 hcc2).trans hx22_1,
        (CallingConventionPreserved.x23 hcc2).trans hx23_1,
        (CallingConventionPreserved.x24 hcc2).trans hx24_1,
        (CallingConventionPreserved.x25 hcc2).trans hx25_1, hbuf2,
        (AgreesOn.readBytes_eq hs2_ag _ 32 (by decide)
          (fun a ha => hP1 (hrw_hm1 a (by rw [State.readReg64_setMem] at ha; unfold InRegion at ha ⊢; bv_omega)))).trans
          ((hag_wb.readBytes_eq hd_dst_ist (by decide)).trans hist1),
        (AgreesOn.readBytes_eq hs2_ag _ 32 (by decide)
          (fun a ha => hP1 (hrw_hm1 a (by rw [State.readReg64_setMem] at ha; unfold InRegion at ha ⊢; bv_omega)))).trans
          ((hag_wb.readBytes_eq hd_dst_ost (by decide)).trans host1),
        (AgreesOn.read64_eq hs2_ag _
          (fun a ha => hP1 (hrw_hm1 a (by rw [State.readReg64_setMem] at ha; unfold InRegion at ha ⊢; bv_omega)))).trans
          ((hag_wb.read64_eq hd_dst_obl).trans hobl1)⟩⟩, hst2.codeLoaded hL1⟩
  refine hp2.trans_full fun s2 ⟨hfr_0_2, hs2⟩ hkf2 => ?_
  have hcl2 : LibsignalCodeLoaded lsmpl s2.mem := (hcl.of_keepsFrozen hkf1).of_keepsFrozen hkf2
  let s0' := s0.setMem s2.mem
  have hmid : FinGenMidPre123 key blocks rem s0' :=
    { key_le := hpre.key_le, blk_mod := hpre.hmac_st.1, blk_le := hpre.hmac_st.2.1,
      rem_lt := hpre.rem_lt, rw_out := hfr_0_2.rw_of_rw _ _ hpre.rw_out,
      rw_hm := hfr_0_2.rw_of_rw _ _ hpre.rw_hm, rw_fsp := hfr_0_2.rw_of_rw _ _ hpre.rw_fsp,
      disj_out_fsp := hpre.disj_out_fsp, disj_hm_fsp := hpre.disj_hm_fsp, sp_aligned := hpre.sp_aligned }
  have hs2_strip : StateGF1 C.F key blocks rem (ProofLib.stripS kp123 s0')
      (ProofLib.stripS kp123 s2) := by
    rcases hs2 with ⟨hpc, ⟨hst, hsp_c, hx29, hx26, hx27, hx28, hsav, _⟩,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
    have hm_eq : (ProofLib.stripS kp123 s0').mem = (ProofLib.stripS kp123 s2).mem := by cases s0; cases s2; rfl
    have hr0 : ∀ r, (ProofLib.stripS kp123 s0').readReg64 r = s0'.readReg64 r := fun _ => by cases s0; rfl
    exact ⟨(by cases s2; exact hpc),
      ⟨(by cases s2; exact hst), (by cases s0; cases s2; exact hsp_c),
        (by cases s0; cases s2; exact hx29), (by cases s0; cases s2; exact hx26),
        (by cases s0; cases s2; exact hx27), (by cases s0; cases s2; exact hx28),
        (stripS_finSaved kp123 s0' s2).mpr hsav, hm_eq ▸ Frame.refl _ _⟩,
      (by cases s0; cases s2; exact hx19), (by cases s0; cases s2; exact hx20),
      (by cases s0; cases s2; exact hx21), (by cases s2; exact hx22), (by cases s2; exact hx23),
      (by cases s2; exact hx24), (by cases s2; exact hx25),
      by rw [hr0, stripS_readBytes]; exact hbuf, by rw [hr0, stripS_readBytes]; exact hist,
      by rw [hr0, stripS_readBytes]; exact host, by rw [hr0, stripS_read64]; exact hobl⟩
  have hp3 : RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s2
      (FinPost C.F key (blocks ++ rem) s0') := by
    refine lift_block_vm_compress_only (Pj := (blkPC_123).rebase (blkPl_123).base H)
      blkLib_eq_123 blk123_noSvc0 blk123_noMsr (by decide) (by decide) hcl2
      (heq123 H ▸ gseg2_to_end_123 hH.compress256 hmid hs2)
      (heq123 _ ▸ gseg2_to_end_123 (hmacCompressOnlyExcHooks_compress C.F H) (hmid.stripS kp123) hs2_strip)
      (fun _ hp => hp.2.1) (fun _ hp => hp.2.1)
      fun sf hvm3 ⟨hpc_f, hstat_f, hcs_f, hout_f, hfr_f⟩ => ?_
    have hr0 : ∀ r, (ProofLib.stripS kp123 s0').readReg64 r = s0'.readReg64 r := fun _ => by cases s0; rfl
    have hsp0 : (ProofLib.stripS kp123 s0').sp = s0'.sp := by cases s0; rfl
    have hm0 : (ProofLib.stripS kp123 s0').mem = ProofLib.stripExecOutside kp123 s2.mem := by cases s0; rfl
    rw [hr0, stripS_readBytes] at hout_f
    rw [hm0, stripS_mem, hr0, hr0, hsp0] at hfr_f
    refine ⟨(by cases s0; cases sf; exact hpc_f), (by cases sf; exact hstat_f),
      ⟨(by cases s0; cases sf; exact hcs_f.1), fun r hr => ?_⟩, hout_f, unstrip_frame hfr_f hvm3.perm_eq⟩
    have := hcs_f.2 r hr; cases s0; cases sf; exact this
  exact hp3.mono fun sf ⟨hpc_f, hstat_f, hcs_f, hout_f, hfr_f⟩ =>
    ⟨hpc_f, hstat_f, hcs_f, hout_f, hfr_0_2.trans (S2Frame.of_frame hfr_f)⟩

/-! ## 3. `memset`-Free Block `54` (`GenericHkdf::extract`) Segments -/

private theorem readable_of_rw {m : Memory} {a : BitVec 64} {n : Nat} (h : m.RW a n) :
    m.Readable a n := fun x hx =>
  let ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (h x hx); ⟨by rw [hp]; rfl, hlf⟩

private def RunsToVmFrom (prog : Program) (s₀ s : State) (P : State → Prop) : Prop :=
  prog.CodeLoaded s.mem →
    ∃ sf, Steps prog s sf ∧ VmPreserved s sf ∧ TraceEq s₀ sf ∧ P sf ∧ prog.CodeLoaded sf.mem

private theorem runsToVm_of_from {prog : Program} {s : State} {P : State → Prop}
    (h : RunsToVmFrom prog s s P) : RunsToVm prog s P := fun hL =>
  let ⟨sf, hst, hvm, ⟨htr, hv⟩, hp, hL'⟩ := h hL; ⟨sf, hst, hvm, htr, hv, hp, hL'⟩

private theorem runsToVmFrom_refl {prog : Program} {s₀ s : State} {P : State → Prop} (h : P s)
    (htr : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)
        | exact ⟨rfl, rfl⟩)) :
    RunsToVmFrom prog s₀ s P := fun hL => ⟨s, .refl s, VmPreserved.refl s, htr, h, hL⟩

private theorem runsToVmFrom_step {prog : Program} {s₀ s : State} {inst : Instr} {P : State → Prop}
    (hrun : s.status = .Running) (hfetch : prog.fetch s.pc = some inst)
    (h : RunsToVmFrom prog s₀ (execInst inst s) P)
    (hnsvc0 : inst.isSvc0 = false := by decide) (hnmsr : inst.isMsrTpidrEl0 = false := by decide)
    (hsvc : prog.svc = Syscall.standard := by first | rfl | exact RunsTo.lsProg_svc) :
    RunsToVmFrom prog s₀ s P := fun hL => by
  have hstep : Step prog s (execInst inst s) :=
    Program.evalInst_eq_execInst inst s hsvc ▸ Step.exec hrun (Program.fetchMem_of_fetch hL hfetch)
  have hvm1 := (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s).toVmPreserved
    (Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s)
  obtain ⟨sf, hst, hvm, htr, hP, hL'⟩ := h (hstep.codeLoaded hL)
  exact ⟨sf, .step hstep hst, hvm1.trans hvm, htr, hP, hL'⟩

private theorem runsToVm_of_steps {prog : Program} {s s₁ : State} {P : State → Prop}
    (hst1 : Steps prog s s₁) (hvm1 : VmPreserved s s₁) (htr1 : TraceEq s s₁)
    (hrest : RunsToVm prog s₁ P) : RunsToVm prog s P := fun hL => by
  obtain ⟨sf, hst2, hvm2, htr2, hv2, hpost, hL2⟩ := hrest (hst1.codeLoaded hL)
  exact ⟨sf, hst1.trans hst2, hvm1.trans hvm2, htr2.trans htr1.1, hv2.trans htr1.2, hpost, hL2⟩

local macro "s2_step_vm" : tactic => `(tactic| (
  refine runsToVmFrom_step (inst := ?inst) ?hrun ?hfetch ?_ ?hnsvc0 ?hnmsr
  case hfetch => ((try simp (config := { decide := true }) only [arm64_norm, *]) <;> rfl)
  (case hnsvc0 => rfl); (case hnmsr => rfl)
  case hrun => (simp only [arm64_norm, *])
  try dsimp only [execInst, execAddSubImm, execAddSubExt, execAddSubShift, execAddSubCarry,
    execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect,
    execCondCompare, execDataProc1, execDataProc2, execDataProc3, execLdr, execLdrLit,
    execStr, execLdp, execStp, evalLogical, evalBitfield, evalAddrMode, AddrMode.baseReg,
    checkRegSPAligned, checkAddrSPAligned, MemWidth.isAligned, State.spAligned, extendVal,
    Reg.fromZRBits, Reg.fromSPBits]
  try simp (config := { decide := true }) only [arm64_norm, *]
  try arm64_discharge_perms_internal))

/-- `memset`-free `Extract.seg1b_placed_runsTo` lifted to `RunsToVm` under `hmc`. -/
public theorem seg1b_hmc [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (hmc : HookSatExactMemcpy H lsMemcpySym)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA 32)
    (hikm_len : x.ikm.length = 32)
    (hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EMemcpyPlaced C.F x s0 sp0 s) :
    RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s (EC88 extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx21, hx22, hx25, hhm⟩
  have hsp_s : s.spAligned = true := by simpa [State.spAligned, hsp] using hsp_al
  have hikm_s : s.mem.readBytes x.ikmA 32 = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ (by decide)]; · exact hikm_mem0
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl; exacts [hd_ikm_out.symm, hd_ikm_stk.symm]
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    rw [show sp0 - (sp0 - 544#64) = 544#64 by bv_lin]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 := hframe.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_32 : s.mem.RW sp0 32 := hrw_sp0_s.sub (by bv_omega)
  have hread_ikm_s : s.mem.Readable x.ikmA 32 := readable_of_rw (hframe.rw_of_rw x.ikmA 32 hRW_ikm)
  have hdisj_ikm : 32 = 0 ∨ DisjointRegions sp0 32 x.ikmA 32 :=
    Or.inr (disj_stk_sub_right hd_ikm_stk sp0 32 ⟨by decide, by omega⟩).symm
  intro hL
  obtain ⟨c, hst1, hvm1, htr1, hv1⟩ :=
    placed_memcpy_budget_steps_sat_exact (prog := (blkPC_54).rebase (blkPl_54).base H) (i := 54)
      hmc hstat hpc hx0 hx1 (by rw [hx2]; rfl) hlr hsp_s hikm_s hrw_sp0_32 hread_ikm_s hdisj_ikm
  refine runsToVm_of_steps hst1 hvm1 ⟨htr1, hv1⟩ (runsToVm_of_from ?_) hL
  dsimp only [applyMemcpyClobber]
  have hag_mc : AgreesOutside s.mem (s.mem.writeBytes sp0 x.ikm) sp0 328 :=
    (ProofLib.AgreesOutside.writeBytes_self s.mem sp0 x.ikm).mono (by omega)
  have hrw_sp0 : (s.mem.writeBytes sp0 x.ikm).RW sp0 432 :=
    CryptoVerification.LibsignalTripleRatchet.rw_of_perm_eq hag_mc.2 hrw_sp0_s
  iterate 3 s2_step_vm
  refine runsToVmFrom_refl ?_
  have hag : AgreesOutside s.mem ((s.mem.writeBytes sp0 x.ikm).write8 (sp0 + 63#64) 32#8) sp0 328 :=
    agreesOutside_sp0_write8 hag_mc (by decide)
  unfold EC88 ExtCommon
  simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
    State.readReg64_setPState, State.readReg64_advancePC, State.readReg64_writeReg64,
    Reg.x19, Reg.x27, Reg.x29, Reg.x22, ite_false, extPlacedFakeB_off_328]
  dsimp only [State.setMem, State.setPC, State.setPState, State.advancePC, State.writeReg64]
  exact ⟨⟨hstat, hsp, hx19, hx27, hx29,
    ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe hag⟩,
    rfl, hx22, HmacSt.of_writeBytes_32_write8_pos hhm hikm_len⟩

/-- `memset`-free `seg1b1_long_placed_runsTo` parameterized only by `hc256`. -/
public theorem seg1b1_long_hc256 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (hc256 : H lsCompress256Sym = some (compress256Hook C.F))
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
  have hikm_le : x.ikm.length ≤ 2 ^ 64 := by rcases hikm_len with h | h | h <;> (rw [h]; decide)
  have hikm_s : s.mem.readBytes x.ikmA x.ikm.length = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ hikm_le]
    · exact hikm_mem0
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl; exacts [hd_ikm_out.symm, hd_ikm_stk.symm]
  have hblk_len : (x.ikm.take (64 * (x.ikm.length / 64))).length = 64 * (x.ikm.length / 64) := by
    simp; omega
  have hblk_s : s.mem.readBytes x.ikmA (64 * (x.ikm.length / 64)) =
      x.ikm.take (64 * (x.ikm.length / 64)) := by
    simpa using readBytes_slice_of_readBytes_eq s.mem x.ikmA x.ikm hikm_s 0
      (64 * (x.ikm.length / 64)) (by omega)
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    rw [show sp0 - (sp0 - 544#64) = 544#64 by bv_lin]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 := hframe.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_40 : s.mem.RW (sp0 + 0x40#64) 32 := hrw_sp0_s.sub (by bv_omega)
  have hx2_nat : (s.readReg64 .x2).toNat = x.ikm.length / 64 := by
    rcases hikm_len with h | h | h <;> (rw [hx2, h]; rfl)
  refine s2_compress256_multi_step_of_eq hc256 hstat hpc hx0 hx1 hx2_nat hlr hist hblk_s hrw_sp0_40 ?_
  generalize hist_def : shaStateBytes
    ((chunks64 (x.ikm.take (64 * (x.ikm.length / 64)))).foldl C.F
      (hmacInnerInit C.F (effectiveSalt x.salt))) = ist'
  have hist'_len : ist'.length = 32 := by rw [← hist_def]; exact shaStateBytes_length _
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (sp0 + 0x40#64) ist') sp0 328 :=
    agreesOutside_writeBytes_sub_sp0 (by rw [hist'_len]; bv_omega)
  have hrw_sp0_1 : (s.mem.writeBytes (sp0 + 0x40#64) ist').RW sp0 432 :=
    CryptoVerification.LibsignalTripleRatchet.rw_of_perm_eq hag_comp.2 hrw_sp0_s
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
    rfl, trivial, trivial, trivial, trivial, hx22, hm.1, hm.2.1.trans hist_def.symm,
    hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2⟩

/-- `memset`-free `seg1b2_long_placed_runsTo` lifted to `RunsToVm` under `hmc`. -/
public theorem seg1b2_long_hmc [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (hmc : HookSatExactMemcpy H lsMemcpySym)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EMemcpyLongPlaced C.F x s0 sp0 s) :
    RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s (EC88Long extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx22, hpos, hist, hcnt1, hout, hcnt2⟩
  have hsp_s : s.spAligned = true := by simpa [State.spAligned, hsp] using hsp_al
  have hikm_le : x.ikm.length ≤ 2 ^ 64 := by rcases hikm_len with h | h | h <;> (rw [h]; decide)
  have hikm_s : s.mem.readBytes x.ikmA x.ikm.length = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ hikm_le]
    · exact hikm_mem0
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl; exacts [hd_ikm_out.symm, hd_ikm_stk.symm]
  have hblk_len : (x.ikm.take (64 * (x.ikm.length / 64))).length = 64 * (x.ikm.length / 64) := by
    simp; omega
  have hrem_len : (x.ikm.drop (64 * (x.ikm.length / 64))).length = x.ikm.length % 64 := by
    simp; omega
  have hrem_s : s.mem.readBytes
      (x.ikmA + BitVec.ofNat 64 (64 * (x.ikm.length / 64))) (x.ikm.length % 64) =
      x.ikm.drop (64 * (x.ikm.length / 64)) := by
    have h := readBytes_slice_of_readBytes_eq s.mem x.ikmA x.ikm hikm_s
      (64 * (x.ikm.length / 64)) (x.ikm.length % 64) (by omega)
    exact h.trans (List.take_of_length_le (by simp; omega))
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    rw [show sp0 - (sp0 - 544#64) = 544#64 by bv_lin]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 := hframe.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_nrem : s.mem.RW sp0 (x.ikm.length % 64) := hrw_sp0_s.sub (by bv_omega)
  have hread_rem_s : s.mem.Readable
      (x.ikmA + BitVec.ofNat 64 (64 * (x.ikm.length / 64))) (x.ikm.length % 64) :=
    readable_of_rw ((hframe.rw_of_rw x.ikmA x.ikm.length hRW_ikm).sub
      (by rcases hikm_len with h | h | h <;> (rw [h]; bv_omega)))
  have hdisj_rem : x.ikm.length % 64 = 0 ∨ DisjointRegions sp0 (x.ikm.length % 64)
      (x.ikmA + BitVec.ofNat 64 (64 * (x.ikm.length / 64))) (x.ikm.length % 64) := by
    by_cases h0 : x.ikm.length % 64 = 0
    · exact Or.inl h0
    · exact Or.inr ((hd_ikm_stk.sub_left _ ⟨by omega,
        by rcases hikm_len with h | h | h <;> (rw [h]; bv_omega)⟩).sub_right sp0
        ⟨by omega, by rcases hikm_len with h | h | h <;> (rw [h] at h0 ⊢; bv_omega)⟩).symm
  have hx2_nat : (s.readReg64 .x2).toNat = x.ikm.length % 64 := by
    rcases hikm_len with h | h | h <;> (rw [hx2, h]; rfl)
  intro hL
  obtain ⟨c, hst1, hvm1, htr1, hv1⟩ :=
    placed_memcpy_budget_steps_sat_exact (prog := (blkPC_54).rebase (blkPl_54).base H) (i := 54)
      hmc hstat hpc hx0 hx1 hx2_nat hlr hsp_s hrem_s hrw_sp0_nrem hread_rem_s hdisj_rem
  refine ⟨_, hst1, hvm1, htr1, hv1, ?_, hst1.codeLoaded hL⟩
  dsimp only [applyMemcpyClobber]
  have hag_mc : AgreesOutside s.mem
      (s.mem.writeBytes sp0 (x.ikm.drop (64 * (x.ikm.length / 64)))) sp0 328 :=
    agreesOutside_writeBytes_sub_sp0 (by rw [BitVec.sub_self, hrem_len]; bv_omega)
  unfold EC88Long ExtCommon
  simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
    State.readReg64_setPState, State.readReg64_writeReg64,
    Reg.x19, Reg.x27, Reg.x29, Reg.x22, ite_false, extPlacedFakeB_off_328]
  dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64]
  refine ⟨⟨hstat, hsp, hx19, hx27, hx29,
    ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe hag_mc⟩, rfl, hx22, ?_⟩
  have hcnt1' : s.mem.read64 (sp0 + 0x60#64) =
      BitVec.ofNat 64 (1 + (x.ikm.take (64 * (x.ikm.length / 64))).length / 64) := by
    rw [hblk_len, Nat.mul_div_cancel_left _ (by decide)]; exact hcnt1
  have hpos' : s.mem.read8 (sp0 + 0x3f#64) =
      BitVec.ofNat 8 (x.ikm.drop (64 * (x.ikm.length / 64))).length := by
    rw [hrem_len]; exact hpos
  exact HmacStGen.of_memcpy_rem (by rw [hblk_len]; omega) (by rw [hblk_len]; omega)
    (by rw [hrem_len]; omega) hpos' hist hcnt1' hout hcnt2

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxASat
