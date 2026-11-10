/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFin
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed
import LibsignalBinary.Specifications.LibsignalE2E.State -- shake: keep

/-!
# Relocatable Multi-Block `finalize_fixed` (Block `123`)

Proves the multi-block `compress256Hook` step `s2_compress256_multi_step_placed` and the relocatable
`[LibsignalPlacement]` `RunsTo` contracts for Block `123` (`finalize_fixed`) over `HmacStGen`
(`blocks.length % 64 = 0`, `blocks.length ≤ 192`, `rem.length < 56`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open CryptoVerification.LibsignalTripleRatchet
open FinalizeFixedProof

open Arm64 ProofLib ProofLib.Variant
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

private theorem mem_setMem_p (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

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

theorem s2_compress256_multi_step_placed [LibsignalPlacement] {prog : Program} {i : Nat}
    (C : Crypto) (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H] [hH : HkdfPlacedHooks C.F H]
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

section PlacedGenFin

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]

private structure StateGF0pPlaced (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 28#64
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x0
  x1_eq   : s.readReg64 .x1 = s0.readReg64 .x1
  hmac_st : HmacStGen s.mem (s0.readReg64 .x1) F key blocks rem

private structure StateGF1Placed (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 76#64
  common  : FinCommon s0 s
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

private structure StateGF2Placed (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 176#64
  common  : FinCommon s0 s
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

private structure StateGF3Placed (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 180#64
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes
      (F ((chunks64 blocks).foldl F (hmacInnerInit F key)) (innerLastBlockGen blocks rem))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateGF3bPlaced (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 304#64
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 =
    outerBlock (digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
      (innerLastBlockGen blocks rem)))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)

private structure StateGF4Placed (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 308#64
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 =
    shaStateBytes (F (hmacOuterInit F key)
      (outerBlock (digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
        (innerLastBlockGen blocks rem)))))

private structure StateGF5Placed (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 420#64
  common : FinCommon s0 s
  out_eq : s.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key (blocks ++ rem)

private theorem gseg1a_placed_runsTo {key blocks rem : List (BitVec 8)} {s0 : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s0 (StateGF0pPlaced C.F key blocks rem s0) := by
  have hpc : s0.pc = (blkPl_123).base := by simpa [arm64_norm] using hpre.pc_eq
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
          frame := by rw [mem_setMem_p]; exact Frame.trans_agreesOutside (Frame.refl s0.mem _) (by simp) hag }
      x0_eq := by fin_reg_p, x1_eq := by fin_reg_p
      hmac_st := by rw [mem_setMem_p]; exact HmacStGen.of_agreesOutside hpre.hmac_st hag hpre.disj_hm_fsp.symm }

private theorem gseg1b_placed_runsTo {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF0pPlaced C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateGF1Placed C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hhmac⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  rcases hhmac with ⟨hmod, hblk_le, hmsg_lt64, hmsg_eq, hpos_eq, hin_eq, hibl_eq, hout_eq, hobl_eq⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hcw_pos : s.mem.canWrite (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 1 = true :=
    hrw_hm.canWrite_sub (by bv_omega) (by decide)
  have hze32 := zeroExtend64_truncate32_ofNat64 hmsg_lt64
  have hze64 := zeroExtend64_ofNat8 hmsg_lt64
  have hxor63 := xor_63_of_lt_64 hmsg_lt64
  iterate 12 s2_step
  have htoNat_sub : (BitVec.ofNat 64 (63 - rem.length)).toNat = 63 - rem.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrw_memset :
      (s.mem.write8 (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 128#8).RW
        (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length + 1#64) (63 - rem.length) := by
    refine Memory.RW.of_perm_eq (by simp) (fun _ => Memory.isLazyFree_write8_of_false _ _) (hrw_hm.sub ?_)
    have := hpre.rem_lt
    bv_omega
  refine s2_memset_step_placed C H
    (dst := s0.readReg64 .x1 + BitVec.ofNat 64 rem.length + 1#64)
    (lr := (blkPl_123).base + 76#64) (len := 63 - rem.length)
    hstat rfl
    (by simp only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm]) htoNat_sub rfl hrw_memset ?_
  refine RunsTo.refl ?_
  have hag := agreesOutside_pad_memset s.mem (s0.readReg64 .x1) rem hpre.rem_lt
  have hd_hm64_fsp : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := rfl
      common :=
        { status := by fin_reg_p, sp_eq := by fin_reg_p, x29_eq := by fin_reg_p,
          x26_eq := by fin_reg_p, x27_eq := by fin_reg_p, x28_eq := by fin_reg_p,
          saved := FinSaved.of_agreesOutside hsaved hag hd_hm64_fsp
          frame := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag }
      x19_eq := by fin_reg_p, x20_eq := by fin_reg_p, x21_eq := by fin_reg_p,
      x22_eq := by fin_reg_p, x23_eq := by fin_reg_p, x24_eq := by fin_reg_p, x25_eq := by fin_reg_p,
      buf_eq := readBytes_64_after_pad_memset s.mem (s0.readReg64 .x1) rem hmsg_eq hpre.rem_lt
      ist_eq := (hag.readBytes_eq hd_hm64_ist (by decide)).trans hin_eq
      ost_eq := (hag.readBytes_eq hd_hm64_ost (by decide)).trans hout_eq
      obl_eq := (hag.read64_eq hd_hm64_obl).trans hobl_eq }

set_option maxHeartbeats 800000 in
private theorem gseg2a_placed_runsTo {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF1Placed C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateGF2Placed C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
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
          frame := by rw [mem_setMem_p]; exact frame_seg2a hframe hag1 hag2 hag3 }
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

private theorem gseg2b_placed_runsTo {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF2Placed C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateGF3Placed C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hblk, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_ist : s.mem.RW (s0.readReg64 .x1 + 0x40#64) 32 := hrw_hm.sub (by bv_omega)
  s2_step
  refine s2_compress256_step_placed C H
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
    { pc_eq := rfl
      common :=
        { status := by fin_reg_p, sp_eq := by fin_reg_p, x29_eq := by fin_reg_p,
          x26_eq := by fin_reg_p, x27_eq := by fin_reg_p, x28_eq := by fin_reg_p,
          saved := FinSaved.of_agreesOutside hsaved hag_comp hd_ist_saved
          frame := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin_reg_p, x20_eq := by fin_reg_p, x21_eq := by fin_reg_p, x22_eq := by fin_reg_p
      ist_eq := by
        have hlen : blk_in.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact Bytes.readBytes_writeBytes_same s.mem _ blk_in (by rw [hlen]; decide)
      ost_eq := (hag_comp.readBytes_eq hd_ist_ost (by decide)).trans host
      obl_eq := (hag_comp.read64_eq hd_ist_obl).trans hobl }

set_option maxHeartbeats 800000 in
private theorem gseg3a_placed_runsTo {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF3Placed C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateGF3bPlaced C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
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
          frame := by rw [mem_setMem_p]; exact frame_seg3a hframe hag1 hag2 hag3 hag4 }
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
        exact ost_eq_seg3a host hag1 hag2 hag3 hag4 hd_hm64_ost hd_fsp64_ost }

private theorem gseg3b_placed_runsTo {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF3bPlaced C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateGF4Placed C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hblk, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_ost : s.mem.RW (s0.readReg64 .x1 + 0x68#64) 32 := hrw_hm.sub (by bv_omega)
  set h_in := C.F ((chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
    (innerLastBlockGen blocks rem)
  s2_step
  refine s2_compress256_step_placed C H
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
    { pc_eq := rfl
      common :=
        { status := by fin_reg_p, sp_eq := by fin_reg_p, x29_eq := by fin_reg_p,
          x26_eq := by fin_reg_p, x27_eq := by fin_reg_p, x28_eq := by fin_reg_p,
          saved := FinSaved.of_agreesOutside hsaved hag_comp hd_ost_saved
          frame := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin_reg_p, x20_eq := by fin_reg_p
      ost_eq := by
        have hlen : blk_out.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact Bytes.readBytes_writeBytes_same s.mem _ blk_out (by rw [hlen]; decide) }

private theorem read32_gseg4a_mid_p (m : Memory) (hm fsp off : BitVec 64) (w : BitVec 32)
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
private theorem gseg4a_placed_runsTo {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF4Placed C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s (StateGF5Placed C.F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe.2 hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 32 := rw_of_perm_eq hframe.2 hpre.rw_out
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_out := C.F (hmacOuterInit C.F key)
    (outerBlock (digestBytes (C.F ((chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
      (innerLastBlockGen blocks rem))))
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_104_of_shaStateBytes s.mem (s0.readReg64 .x1) h_out host
  have hzero64 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
  iterate 11 s2_step
  have hd_fsp64_hm := (gseg4a_disj_p hpre).1
  have hread128 := read32_gseg4a_mid_p s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 128#64 (h_out.get 6)
    (Or.inl rfl) hd_fsp64_hm hw6
  have hread132 := read32_gseg4a_mid_p s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 132#64 (h_out.get 7)
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
          frame := by rw [mem_setMem_p]; exact frame_seg4a hframe hag1 hag2 hag3 hag4 }
      out_eq := by
        rw [mem_setMem_p]
        exact (readBytes_write32_8_digestBytes _ (s0.readReg64 .x0) h_out _ _ _ _ _ _ _ _
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
          (toLEBytes_4_rev32 _)).trans
          (hmacWith_gen C.F key blocks rem hpre.key_le hpre.hmac_st.1 hpre.rem_lt).symm }

private theorem gseg4b_placed_runsTo {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF5Placed C.F key blocks rem s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s
      (FinPost C.F key (blocks ++ rem) s0) := by
  rcases hs with ⟨hpc, hcom, hout⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe.2 hpre.rw_fsp
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
  all_goals simp only [arm64_norm, hx26, hx27, hx28]

/-- Relocatable `RunsTo` contract of Block `123` (`finalize_fixed`) for multi-block `HmacStGen`. -/
theorem finalize_fixed_gen_placed_runsTo {key blocks rem : List (BitVec 8)} {s0 : State}
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base H) s0
      (FinPost C.F key (blocks ++ rem) s0) :=
  (gseg1a_placed_runsTo (H := H) hpre).trans fun _ hs0 =>
    (gseg1b_placed_runsTo (H := H) hpre hs0).trans fun _ hs1 =>
      (gseg2a_placed_runsTo (H := H) hpre hs1).trans fun _ hs2 =>
        (gseg2b_placed_runsTo (H := H) hpre hs2).trans fun _ hs3 =>
          (gseg3a_placed_runsTo (H := H) hpre hs3).trans fun _ hs3b =>
            (gseg3b_placed_runsTo (H := H) hpre hs3b).trans fun _ hs4 =>
              (gseg4a_placed_runsTo (H := H) hpre hs4).trans fun _ hs5 =>
                gseg4b_placed_runsTo (H := H) hpre hs5

theorem finalize_fixed_gen_placed_runsTo_of_other_block {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i H]
    {key blocks rem : List (BitVec 8)} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpre : FinGenPre finPlacedFakeB C.F key blocks rem s0)
    (hi : i < 619 := by decide) :
    RunsTo callerProg s0 (FinPost C.F key (blocks ++ rem) s0) :=
  RunsTo.of_other_block hcl (finalize_fixed_gen_placed_runsTo (H := H) hpre) hi (by decide) (by decide)

end PlacedGenFin

end CryptoVerification.E2E.Pqxdh.ResponderCore
