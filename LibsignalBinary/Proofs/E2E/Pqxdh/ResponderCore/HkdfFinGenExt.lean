/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFin
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt

/-!
# `.inImage`-Free Multi-Block `finalize_fixed`

Proves `finalize_fixed_gen_runsToE_base` and `finalize_fixed_single_runsToE_base` on
`tripleRatchetProgAtExt b ext` at `finalizeFixedStackExt` (`16528` B) for `HmacStGen m a F key blocks rem`
(`blocks.length % 64 = 0`, `blocks.length ≤ 192`, `rem.length < 56`), parameterized over
`MemsetStepExt` and `CompressOneStepExt` without `img.FrozenLoaded` or `symtab`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
open CryptoVerification.LibsignalTripleRatchet.HkdfExt.FinX
open CryptoVerification.LibsignalTripleRatchet.FinalizeFixedProof
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (shaStateBytes readShaState)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

/-- `.inImage`-free `RunsToE` contract shape for `memset` on `tripleRatchetProgAtExt b ext`. -/
def MemsetStepExt (b : BitVec 64) (ext : String → Option (State → State)) : Prop :=
  ∀ {s : State} {dst : BitVec 64} {val : BitVec 8} {n : ℕ},
    s.pc = b + bv% (ls_off% "memset") →
    s.status = .Running →
    s.readReg64 .x0 = dst →
    (s.readReg64 .x1).truncate 8 = val →
    (s.readReg64 .x2).toNat = n →
    RW s.mem dst n →
    RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack →
    DisjointRegions dst n (s.sp - BitVec.ofNat 64 extHookStack) extHookStack →
    (s.sp &&& 15#64) = 0#64 →
    Extract.RunsToE (tripleRatchetProgAtExt b ext) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.readReg64 .x0 = dst ∧
      s'.mem.readBytes dst n = List.replicate n val ∧
      Extract.S2Frame s.mem s'.mem [(dst, n), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)])

/-- `.inImage`-free `RunsToE` contract shape for single-block `compress256` on
`tripleRatchetProgAtExt b ext`. -/
def CompressOneStepExt (b : BitVec 64) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  ∀ {s : State} {stPtr blkPtr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)},
    s.pc = b + bv% (ls_off% "sha2::sha256::compress256") →
    s.status = .Running →
    s.readReg64 .x0 = stPtr →
    s.readReg64 .x1 = blkPtr →
    s.readReg64 .x2 = 1#64 →
    s.mem.readBytes stPtr 32 = LibsignalHmac.shaStateBytes st →
    s.mem.readBytes blkPtr 64 = blk →
    RW s.mem stPtr 32 →
    RW s.mem blkPtr 64 →
    RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack →
    DisjointRegions stPtr 32 blkPtr 64 →
    DisjointRegions stPtr 32 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack →
    DisjointRegions blkPtr 64 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack →
    (s.sp &&& 15#64) = 0#64 →
    Extract.RunsToE (tripleRatchetProgAtExt b ext) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.readBytes stPtr 32 = LibsignalHmac.shaStateBytes (F st blk) ∧
      s'.mem.readBytes blkPtr 64 = blk ∧
      Extract.S2Frame s.mem s'.mem [(stPtr, 32), (s.sp - BitVec.ofNat 64 extHookStack, extHookStack)])

/-- Bundled preconditions of multi-block `finalize_fixed` at `16528` B stack
(`finalizeFixedStackExt`), without `FrozenLoaded` or `symtab`. -/
structure FinGenPreX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 : State) : Prop where
  pc_eq        : s0.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]")
  status       : s0.status = .Running
  key_le       : key.length ≤ 64
  rem_lt       : rem.length < 56
  hmac_st      : HmacStGen s0.mem (s0.readReg64 .x1) F key blocks rem
  rw_out       : RW s0.mem (s0.readReg64 .x0) 32
  rw_hm        : RW s0.mem (s0.readReg64 .x1) 0x90
  rw_fsp       : RW s0.mem (s0.sp - 16528#64) 16528
  disj_out_hm  : DisjointRegions (s0.readReg64 .x0) 32 (s0.readReg64 .x1) 0x90
  disj_out_fsp : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 16528#64) 16528
  disj_hm_fsp  : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 16528#64) 16528
  sp_aligned   : (s0.sp &&& 0b1111#64) = 0#64

theorem HmacStGen.of_hmacSt {m : Memory} {a : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key msg : List (BitVec 8)}
    (h : HmacSt m a F key msg) : HmacStGen m a F key [] msg :=
  ⟨rfl, by decide, h⟩

private theorem FinGenPreX.rw_fsp144 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {key blocks rem : List (BitVec 8)} {s0 : State}
    (h : FinGenPreX b F key blocks rem s0) : RW s0.mem (s0.sp - 144#64) 144 :=
  h.rw_fsp.sub (by bv_omega)

private theorem FinGenPreX.disj_out_fsp144 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {key blocks rem : List (BitVec 8)} {s0 : State}
    (h : FinGenPreX b F key blocks rem s0) :
    DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64) 144 :=
  h.disj_out_fsp.sub_right _ ⟨by decide, by bv_omega⟩

private theorem FinGenPreX.disj_hm_fsp144 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {key blocks rem : List (BitVec 8)} {s0 : State}
    (h : FinGenPreX b F key blocks rem s0) :
    DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64) 144 :=
  h.disj_hm_fsp.sub_right _ ⟨by decide, by bv_omega⟩

private structure StateGF0pX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 28)
  common  : FinCommonX s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x0
  x1_eq   : s.readReg64 .x1 = s0.readReg64 .x1
  hmac_st : HmacStGen s.mem (s0.readReg64 .x1) F key blocks rem

private structure StateGF1X (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 76)
  common  : FinCommonX s0 s
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

private structure StateGF2X (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 176)
  common  : FinCommonX s0 s
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

private structure StateGF3X (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 180)
  common  : FinCommonX s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key)) (innerLastBlockGen blocks rem))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateGF3bX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 304)
  common  : FinCommonX s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 =
    outerBlock (digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
      (innerLastBlockGen blocks rem)))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)

private structure StateGF4X (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 308)
  common  : FinCommonX s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 =
    shaStateBytes (F (hmacOuterInit F key)
      (outerBlock (digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
        (innerLastBlockGen blocks rem)))))

private structure StateGF5X (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 420)
  common : FinCommonX s0 s
  out_eq : s.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key (blocks ++ rem)

local macro "fin_reg_x" : tactic =>
  `(tactic| simp (config := { decide := true }) only [arm64_norm, *])

local macro "solve_fin_saved_x" : tactic =>
  `(tactic| (try rw [HkdfExt.mem_setMem]; simp (config := { decide := true }) only [arm64_norm]))

private theorem gseg1a_x_runsTo {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)} {key blocks rem : List (BitVec 8)} {s0 : State}
    (hpre : FinGenPreX b F key blocks rem s0) :
    Extract.RunsToE (tripleRatchetProgAtExt b ext) s0 (StateGF0pX b F key blocks rem s0) := by
  have hpc := hpre.pc_eq
  have hstat := hpre.status
  have hal0 : (s0.sp &&& 15#64) = 0#64 := hpre.sp_aligned
  have hal_fsp : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hrw_fsp : s0.mem.RW (s0.sp - 144#64) 144 := hpre.rw_fsp144
  have hrun : LibsignalTripleRatchet.RunsTo (tripleRatchetProgAtExt b ext) s0
      (StateGF0pX b F key blocks rem s0) := by
    iterate 7 s2_step
    refine LibsignalTripleRatchet.RunsTo.refl ?_
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
    refine ⟨by fin_reg_x,
      ⟨by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x,
       ⟨by solve_fin_saved_x, by solve_fin_saved_x, by solve_fin_saved_x,
        by solve_fin_saved_x, by solve_fin_saved_x, by solve_fin_saved_x,
        by solve_fin_saved_x, by solve_fin_saved_x, by solve_fin_saved_x⟩,
       by rw [HkdfExt.mem_setMem]
          exact HkdfExt.S2Frame.trans_agreesOutside_sub (Extract.S2Frame.refl s0.mem _)
            (rbase := s0.sp - 16528#64) (rlen := 16528) (by simp) (by bv_omega) hag⟩,
      by fin_reg_x, by fin_reg_x,
      by rw [HkdfExt.mem_setMem]; exact HmacStGen.of_agreesOutside hpre.hmac_st hag hpre.disj_hm_fsp144.symm⟩
  exact HkdfExt.runsTo_toE hrun

private theorem gseg1b_x_runsTo {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hMemset : MemsetStepExt b ext)
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPreX b F key blocks rem s0)
    (hs : StateGF0pX b F key blocks rem s0 s) :
    Extract.RunsToE (tripleRatchetProgAtExt b ext) s (StateGF1X b F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hhmac⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  rcases hhmac with ⟨hmod, hblk_le, hmsg_lt64, hmsg_eq, hpos_eq, hin_eq, hibl_eq, hout_eq, hobl_eq⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_stk : s.mem.RW (s0.sp - 16528#64) 16528 := hframe.rw_of_rw _ _ hpre.rw_fsp
  have hcw_pos : s.mem.canWrite (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 1 = true :=
    hrw_hm.canWrite_sub (by bv_omega) (by decide)
  have hze32 := zeroExtend64_truncate32_ofNat64 hmsg_lt64
  have hze64 := zeroExtend64_ofNat8 hmsg_lt64
  have hxor63 := xor_63_of_lt_64 hmsg_lt64
  set dst := s0.readReg64 .x1 + BitVec.ofNat 64 rem.length + 1#64
  set len := 63 - rem.length
  set m_pre := s.mem.write8 (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 128#8
  have hstep1 : LibsignalTripleRatchet.RunsTo (tripleRatchetProgAtExt b ext) s (fun s1 =>
      s1.pc = b + bv% (ls_off% "memset") ∧
      s1.status = .Running ∧
      s1.sp = s0.sp - 144#64 ∧
      s1.readReg64 .lr = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 76) ∧
      s1.readReg64 .x0 = dst ∧
      (s1.readReg64 .x1).truncate 8 = 0#8 ∧
      (s1.readReg64 .x2).toNat = len ∧
      s1.readReg64 .x19 = s0.readReg64 .x0 ∧
      s1.readReg64 .x20 = s0.readReg64 .x1 ∧
      s1.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64 ∧
      s1.readReg64 .x22 = 0x80#64 ∧
      s1.readReg64 .x23 = BitVec.ofNat 64 rem.length ∧
      s1.readReg64 .x24 = BitVec.ofNat 64 (1 + blocks.length / 64) ∧
      s1.readReg64 .x25 = BitVec.ofNat 64 len ∧
      s1.readReg64 .x26 = s0.readReg64 .x26 ∧
      s1.readReg64 .x27 = s0.readReg64 .x27 ∧
      s1.readReg64 .x28 = s0.readReg64 .x28 ∧
      s1.readReg64 .x29 = s0.sp - 144#64 + 0x40#64 ∧
      s1.mem = m_pre) := by
    iterate 12 s2_step
    have htoNat_sub : (BitVec.ofNat 64 len).toNat = len := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine LibsignalTripleRatchet.RunsTo.refl ⟨by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x,
      by simp only [dst, arm64_norm],
      by simp (config := { decide := true }) only [arm64_norm],
      by simpa only [arm64_norm] using htoNat_sub,
      by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x,
      by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, rfl⟩
  refine (HkdfExt.runsTo_toE hstep1).trans_full fun s1 hs1 _ _ => ?_
  rcases hs1 with ⟨hpc1, hstat1, hsp1, hlr1, hx0_1, hx1_1, hx2_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hmem1⟩
  have hstk_eq : s1.sp - 16384#64 = s0.sp - 16528#64 := by rw [hsp1]; bv_omega
  have hrw_dst : RW s1.mem dst len := by
    rw [hmem1]; refine Memory.RW.of_perm_eq (by simp [m_pre]) (fun _ => Memory.isLazyFree_write8_of_false _ _) (hrw_hm.sub ?_)
    have := hpre.rem_lt; dsimp only [dst, len]; bv_omega
  have hrw_ext_stk : RW s1.mem (s1.sp - 16384#64) 16384 := by
    rw [hmem1, hstk_eq]; refine Memory.RW.of_perm_eq (by simp [m_pre]) (fun _ => Memory.isLazyFree_write8_of_false _ _) (hrw_stk.sub ?_)
    bv_omega
  have hd_dst_stk : DisjointRegions dst len (s1.sp - 16384#64) 16384 := by
    rw [hstk_eq]
    have := hpre.rem_lt
    exact (hpre.disj_hm_fsp.sub_left dst ⟨by dsimp [len]; omega, by dsimp [dst, len]; bv_omega⟩).sub_right
      _ ⟨by decide, by bv_omega⟩
  have hsp1_al : (s1.sp &&& 15#64) = 0#64 := by rw [hsp1]; exact fsp_aligned hpre.sp_aligned
  refine (hMemset hpc1 hstat1 hx0_1 hx1_1 hx2_1 hrw_dst hrw_ext_stk hd_dst_stk hsp1_al).trans_full
    fun s2 hs2 _ _ => ?_
  rcases hs2 with ⟨hpc2, hstat2, hcc2, _, hdst2, hframe2⟩
  intro hL2
  refine ⟨s2, .refl s2, ⟨rfl, rfl⟩, ?_, hL2⟩
  set m_ideal := m_pre.writeBytes dst (List.replicate len 0#8)
  have hag_pad : AgreesOutside s.mem m_ideal (s0.readReg64 .x1) 64 :=
    agreesOutside_pad_memset s.mem (s0.readReg64 .x1) rem hpre.rem_lt
  have hframe2' : Extract.S2Frame m_pre s2.mem [(dst, len), (s0.sp - 16528#64, 16384)] := by
    rwa [← hmem1, ← hstk_eq]
  have hag_on : HkdfExt.AgreesOn
      (fun a => s.mem.permNoLazy a = some Perm.rw ∧ OutsideRegion (s0.sp - 16528#64) 16384 a)
      s2.mem m_ideal := by
    have hdst2' : s2.mem.readBytes dst (List.replicate len 0#8).length = List.replicate len 0#8 := by
      rwa [List.length_replicate]
    have hframe2_rep : Extract.S2Frame m_pre s2.mem
        [(dst, (List.replicate len 0#8).length), (s0.sp - 16528#64, 16384)] := by
      rwa [List.length_replicate]
    have h := HkdfExt.AgreesOn.of_s2Frame_writeBytes hdst2' hframe2_rep
      (by rw [List.length_replicate]; dsimp [len]; omega)
    intro a ⟨hnl, hout⟩
    obtain ⟨hrw, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl
    have hnl_pre : m_pre.permNoLazy a = some Perm.rw :=
      Memory.permNoLazy_eq_some_rw_iff.mpr
        ⟨by simpa [m_pre] using hrw, Memory.isLazyFree_write8_of_false _ _ hlf⟩
    exact h a ⟨hnl_pre, hout⟩
  have hP_saved : ∀ a, InRegion (s0.sp - 144#64 + 0x40#64) 0x50 a →
      s.mem.permNoLazy a = some Perm.rw ∧ OutsideRegion (s0.sp - 16528#64) 16384 a := by
    intro a ha
    have ha_stk : InRegion (s0.sp - 16528#64) 16528 a := by unfold InRegion at ha ⊢; bv_omega
    exact ⟨hrw_stk a ha_stk, by simp only [InRegion, OutsideRegion] at ha ⊢; bv_omega⟩
  have hP_hm : ∀ (off : BitVec 64) (sz : ℕ), off.toNat + sz ≤ 0x90 →
      ∀ a, InRegion (s0.readReg64 .x1 + off) sz a →
      s.mem.permNoLazy a = some Perm.rw ∧ OutsideRegion (s0.sp - 16528#64) 16384 a := by
    intro off sz hsz a ha
    have hin_hm : InRegion (s0.readReg64 .x1) 0x90 a := by unfold InRegion at ha ⊢; bv_omega
    refine ⟨hrw_hm a hin_hm, ?_⟩
    exact DisjointRegions.outside
      (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩) hin_hm (by decide)
  have hd_hm64_fsp : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp144.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  have hframe_s2 : Extract.S2Frame s0.mem s2.mem
      [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 16528#64, 16528)] := by
    have hag_pre : AgreesOutside s.mem m_pre (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 1 := by
      dsimp only [m_pre]; agrees_outside_writes
    have hf1 : Extract.S2Frame s0.mem m_pre
        [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 16528#64, 16528)] := by
      have := hpre.rem_lt
      exact HkdfExt.S2Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
        (by simp) (by bv_omega) hag_pre
    refine hf1.trans (hframe2'.mono fun a ha => ?_)
    intro r hr_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
    rcases hr_mem with rfl | rfl
    · have ha_hm := ha (s0.readReg64 .x1, 0x90) (by simp)
      have := hpre.rem_lt; dsimp only [dst, len]
      unfold OutsideRegion at ha_hm ⊢; bv_omega
    · have ha_stk := ha (s0.sp - 16528#64, 16528) (by simp)
      unfold OutsideRegion at ha_stk ⊢; bv_omega
  refine
    { pc_eq := hpc2.trans hlr1
      common :=
        { status := hstat2
          sp_eq := (Extract.CallingConventionPreserved.sp_eq hcc2).trans hsp1
          x29_eq := (Extract.CallingConventionPreserved.x29 hcc2).trans hx29_1
          x26_eq := hcc2.2.2.2.2.2.2.2.2.1.trans hx26_1
          x27_eq := (Extract.CallingConventionPreserved.x27 hcc2).trans hx27_1
          x28_eq := hcc2.2.2.2.2.2.2.2.2.2.2.1.trans hx28_1
          saved := hag_on.finSaved_of (FinSaved.of_agreesOutside hsaved hag_pad hd_hm64_fsp) hP_saved
          frame := hframe_s2 }
      x19_eq := (Extract.CallingConventionPreserved.x19 hcc2).trans hx19_1
      x20_eq := (Extract.CallingConventionPreserved.x20 hcc2).trans hx20_1
      x21_eq := (Extract.CallingConventionPreserved.x21 hcc2).trans hx21_1
      x22_eq := (Extract.CallingConventionPreserved.x22 hcc2).trans hx22_1
      x23_eq := hcc2.2.2.2.2.2.1.trans hx23_1
      x24_eq := hcc2.2.2.2.2.2.2.1.trans hx24_1
      x25_eq := hcc2.2.2.2.2.2.2.2.1.trans hx25_1
      buf_eq := (hag_on.readBytes_eq (s0.readReg64 .x1) 64 (by decide)
          (fun a ha => hP_hm 0#64 64 (by decide) a (by simpa using ha))).trans
        (readBytes_64_after_pad_memset s.mem (s0.readReg64 .x1) rem hmsg_eq hpre.rem_lt)
      ist_eq := (hag_on.readBytes_eq (s0.readReg64 .x1 + 0x40#64) 32 (by decide)
          (hP_hm 0x40#64 32 (by decide))).trans
        ((hag_pad.readBytes_eq hd_hm64_ist (by decide)).trans hin_eq)
      ost_eq := (hag_on.readBytes_eq (s0.readReg64 .x1 + 0x68#64) 32 (by decide)
          (hP_hm 0x68#64 32 (by decide))).trans
        ((hag_pad.readBytes_eq hd_hm64_ost (by decide)).trans hout_eq)
      obl_eq := (hag_on.read64_eq (s0.readReg64 .x1 + 0x88#64)
          (hP_hm 0x88#64 8 (by decide))).trans
        ((hag_pad.read64_eq hd_hm64_obl).trans hobl_eq) }

private theorem gseg2a_x_runsTo {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPreX b F key blocks rem s0)
    (hs : StateGF1X b F key blocks rem s0 s) :
    Extract.RunsToE (tripleRatchetProgAtExt b ext) s (StateGF2X b F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp144
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hult_7 := ult_7_of_lt_56 hpre.rem_lt
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp144.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hrun : LibsignalTripleRatchet.RunsTo (tripleRatchetProgAtExt b ext) s
      (StateGF2X b F key blocks rem s0) := by
    iterate 6 s2_step
    have hread32 := fun u0 u1 u2 u3 w56 =>
      read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 32#64 (by decide) hd_hm64_fsp64
    have hread40 := fun u0 u1 u2 u3 w56 =>
      read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 40#64 (by decide) hd_hm64_fsp64
    have hread48 := fun u0 u1 u2 u3 w56 =>
      read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 48#64 (by decide) hd_hm64_fsp64
    iterate 7 s2_step
    clear hread32 hread40 hread48
    refine LibsignalTripleRatchet.RunsTo.refl ?_
    obtain ⟨hag1, hag2, hag3⟩ := agreesOutside_seg2a s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
      _ _ _ _ _ _ _ _ _
    have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
      unfold DisjointRegions; bv_omega
    have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
      (hpre.disj_hm_fsp144.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
    have hd_fsp64_ist : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x40#64) 32 :=
      (hpre.disj_hm_fsp144.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
    have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
      unfold DisjointRegions; bv_omega
    have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
      (hpre.disj_hm_fsp144.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
    have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
      unfold DisjointRegions; bv_omega
    have hd_fsp64_obl : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x88#64) 8 :=
      (hpre.disj_hm_fsp144.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
    have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
      unfold DisjointRegions; bv_omega
    refine ⟨by fin_reg_x,
      ⟨by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x,
       by rw [HkdfExt.mem_setMem]
          exact FinSaved.of_agreesOutside
            (FinSaved.of_agreesOutside (FinSaved.of_agreesOutside hsaved hag1 hd_fsp64_saved)
              hag2 hd_hm64_saved) hag3 hd_fsp64_saved,
       by rw [HkdfExt.mem_setMem]; exact s2Frame_of_frame_fsp hframe (frame_seg2a (Frame.refl s.mem _) hag1 hag2 hag3)⟩,
      by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x,
      by rw [HkdfExt.mem_setMem]
         refine (readBytes_fsp_64_seg2 _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
         rw [toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
             toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_rev64,
             readBytes_56_eq_append_8 s.mem (s0.readReg64 .x1),
             readBytes_56_of_buf_eq s.mem (s0.readReg64 .x1) rem hbuf hpre.rem_lt,
             bit_len_inner_gen_eq hpre.hmac_st.1 hpre.hmac_st.2.1 hpre.rem_lt]
         rfl,
      by rw [HkdfExt.mem_setMem]
         exact (hag3.readBytes_eq hd_fsp64_ist (by decide)).trans
           ((hag2.readBytes_eq hd_hm64_ist (by decide)).trans
             ((hag1.readBytes_eq hd_fsp64_ist (by decide)).trans hist)),
      by rw [HkdfExt.mem_setMem]
         exact (hag3.readBytes_eq hd_fsp64_ost (by decide)).trans
           ((hag2.readBytes_eq hd_hm64_ost (by decide)).trans
             ((hag1.readBytes_eq hd_fsp64_ost (by decide)).trans host)),
      by rw [HkdfExt.mem_setMem]
         exact (hag3.read64_eq hd_fsp64_obl).trans
           ((hag2.read64_eq hd_hm64_obl).trans
             ((hag1.read64_eq hd_fsp64_obl).trans hobl))⟩
  exact HkdfExt.runsTo_toE hrun

private theorem gseg2b_x_runsTo {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hComp : CompressOneStepExt b F ext)
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPreX b F key blocks rem s0)
    (hs : StateGF2X b F key blocks rem s0 s) :
    Extract.RunsToE (tripleRatchetProgAtExt b ext) s (StateGF3X b F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hblk, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_stk : s.mem.RW (s0.sp - 16528#64) 16528 := hframe.rw_of_rw _ _ hpre.rw_fsp
  have hstep1 : LibsignalTripleRatchet.RunsTo (tripleRatchetProgAtExt b ext) s (fun s1 =>
      s1.pc = b + bv% (ls_off% "sha2::sha256::compress256") ∧
      s1.status = .Running ∧
      s1.sp = s0.sp - 144#64 ∧
      s1.readReg64 .lr = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 180) ∧
      s1.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64 ∧
      s1.readReg64 .x1 = s0.sp - 144#64 ∧
      s1.readReg64 .x2 = 1#64 ∧
      s1.readReg64 .x19 = s0.readReg64 .x0 ∧
      s1.readReg64 .x20 = s0.readReg64 .x1 ∧
      s1.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64 ∧
      s1.readReg64 .x22 = 0x80#64 ∧
      s1.readReg64 .x26 = s0.readReg64 .x26 ∧
      s1.readReg64 .x27 = s0.readReg64 .x27 ∧
      s1.readReg64 .x28 = s0.readReg64 .x28 ∧
      s1.readReg64 .x29 = s0.sp - 144#64 + 0x40#64 ∧
      s1.mem = s.mem) := by
    s2_step
    refine LibsignalTripleRatchet.RunsTo.refl ⟨rfl, hstat, hsp, rfl,
      by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x,
      by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, rfl⟩
  refine (HkdfExt.runsTo_toE hstep1).trans_full fun s1 hs1 _ _ => ?_
  rcases hs1 with ⟨hpc1, hstat1, hsp1, hlr1, hx0_1, hx1_1, hx2_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx26_1, hx27_1, hx28_1, hx29_1, hmem1⟩
  have hstk_eq : s1.sp - 16384#64 = s0.sp - 16528#64 := by rw [hsp1]; bv_omega
  have hrw_st : RW s1.mem (s0.readReg64 .x1 + 0x40#64) 32 := by
    rw [hmem1]; exact hrw_hm.sub (by bv_omega)
  have hrw_blk : RW s1.mem (s0.sp - 144#64) 64 := by
    rw [hmem1]; exact hrw_stk.sub (by bv_omega)
  have hrw_ext_stk : RW s1.mem (s1.sp - 16384#64) 16384 := by
    rw [hmem1, hstk_eq]; exact hrw_stk.sub (by bv_omega)
  have hd_st_blk : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_st_stk : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s1.sp - 16384#64) 16384 := by
    rw [hstk_eq]
    exact (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_blk_stk : DisjointRegions (s0.sp - 144#64) 64 (s1.sp - 16384#64) 16384 := by
    rw [hstk_eq]; unfold DisjointRegions; bv_omega
  have hsp1_al : (s1.sp &&& 15#64) = 0#64 := by rw [hsp1]; exact fsp_aligned hpre.sp_aligned
  refine (hComp hpc1 hstat1 hx0_1 hx1_1 hx2_1 (hmem1 ▸ hist) (hmem1 ▸ hblk)
    hrw_st hrw_blk hrw_ext_stk hd_st_blk hd_st_stk hd_blk_stk hsp1_al).trans_full
    fun s2 hs2 _ _ => ?_
  rcases hs2 with ⟨hpc2, hstat2, hcc2, hist2, _, hframe2⟩
  intro hL2
  refine ⟨s2, .refl s2, ⟨rfl, rfl⟩, ?_, hL2⟩
  set st0 := (chunks64 blocks).foldl F (hmacInnerInit F key)
  set blk_in := shaStateBytes (F st0 (innerLastBlockGen blocks rem))
  set m_ideal := s.mem.writeBytes (s0.readReg64 .x1 + 0x40#64) blk_in
  have hlen_in : blk_in.length = 32 := HkdfExt.shaStateBytes_length _
  have hag_comp : AgreesOutside s.mem m_ideal (s0.readReg64 .x1 + 0x40#64) 32 := by
    rw [← hlen_in]; exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_in
  have hframe2' : Extract.S2Frame s.mem s2.mem
      [(s0.readReg64 .x1 + 0x40#64, blk_in.length), (s0.sp - 16528#64, 16384)] := by
    dsimp only [extHookStack] at hframe2
    rw [hlen_in, ← hmem1, ← hstk_eq]; exact hframe2
  have hag_on : HkdfExt.AgreesOn
      (fun a => s.mem.permNoLazy a = some Perm.rw ∧ OutsideRegion (s0.sp - 16528#64) 16384 a)
      s2.mem m_ideal :=
    HkdfExt.AgreesOn.of_s2Frame_writeBytes (by rwa [hlen_in]) hframe2' (by rw [hlen_in]; decide)
  have hP_saved : ∀ a, InRegion (s0.sp - 144#64 + 0x40#64) 0x50 a →
      s.mem.permNoLazy a = some Perm.rw ∧ OutsideRegion (s0.sp - 16528#64) 16384 a := by
    intro a ha
    have ha_stk : InRegion (s0.sp - 16528#64) 16528 a := by unfold InRegion at ha ⊢; bv_omega
    exact ⟨hrw_stk a ha_stk, by simp only [InRegion, OutsideRegion] at ha ⊢; bv_omega⟩
  have hP_ost : ∀ a, InRegion (s0.readReg64 .x1 + 0x68#64) 32 a →
      s.mem.permNoLazy a = some Perm.rw ∧ OutsideRegion (s0.sp - 16528#64) 16384 a := by
    intro a ha
    have hin_hm : InRegion (s0.readReg64 .x1) 0x90 a := by unfold InRegion at ha ⊢; bv_omega
    exact ⟨hrw_hm a hin_hm,
      DisjointRegions.outside (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩) hin_hm (by decide)⟩
  have hP_obl : ∀ a, InRegion (s0.readReg64 .x1 + 0x88#64) 8 a →
      s.mem.permNoLazy a = some Perm.rw ∧ OutsideRegion (s0.sp - 16528#64) 16384 a := by
    intro a ha
    have hin_hm : InRegion (s0.readReg64 .x1) 0x90 a := by unfold InRegion at ha ⊢; bv_omega
    exact ⟨hrw_hm a hin_hm,
      DisjointRegions.outside (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩) hin_hm (by decide)⟩
  have hd_ist_saved : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp144.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_ist_ost : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_ist_obl : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  have hframe_s2 : Extract.S2Frame s0.mem s2.mem
      [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 16528#64, 16528)] := by
    refine hframe.trans (hframe2'.mono fun a ha => ?_)
    intro r hr_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
    rcases hr_mem with rfl | rfl
    · have ha_hm := ha (s0.readReg64 .x1, 0x90) (by simp)
      rw [hlen_in]; unfold OutsideRegion at ha_hm ⊢; bv_omega
    · have ha_stk := ha (s0.sp - 16528#64, 16528) (by simp)
      unfold OutsideRegion at ha_stk ⊢; bv_omega
  refine
    { pc_eq := hpc2.trans hlr1
      common :=
        { status := hstat2
          sp_eq := (Extract.CallingConventionPreserved.sp_eq hcc2).trans hsp1
          x29_eq := (Extract.CallingConventionPreserved.x29 hcc2).trans hx29_1
          x26_eq := hcc2.2.2.2.2.2.2.2.2.1.trans hx26_1
          x27_eq := (Extract.CallingConventionPreserved.x27 hcc2).trans hx27_1
          x28_eq := hcc2.2.2.2.2.2.2.2.2.2.2.1.trans hx28_1
          saved := hag_on.finSaved_of (FinSaved.of_agreesOutside hsaved hag_comp hd_ist_saved) hP_saved
          frame := hframe_s2 }
      x19_eq := (Extract.CallingConventionPreserved.x19 hcc2).trans hx19_1
      x20_eq := (Extract.CallingConventionPreserved.x20 hcc2).trans hx20_1
      x21_eq := (Extract.CallingConventionPreserved.x21 hcc2).trans hx21_1
      x22_eq := (Extract.CallingConventionPreserved.x22 hcc2).trans hx22_1
      ist_eq := hist2
      ost_eq := (hag_on.readBytes_eq (s0.readReg64 .x1 + 0x68#64) 32 (by decide) hP_ost).trans
        ((hag_comp.readBytes_eq hd_ist_ost (by decide)).trans host)
      obl_eq := (hag_on.read64_eq (s0.readReg64 .x1 + 0x88#64) hP_obl).trans
        ((hag_comp.read64_eq hd_ist_obl).trans hobl) }

private theorem gseg3a_x_runsTo {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPreX b F key blocks rem s0)
    (hs : StateGF3X b F key blocks rem s0 s) :
    Extract.RunsToE (tripleRatchetProgAtExt b ext) s (StateGF3bX b F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp144
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_in := F ((chunks64 blocks).foldl F (hmacInnerInit F key)) (innerLastBlockGen blocks rem)
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_64_of_shaStateBytes s.mem (s0.readReg64 .x1) h_in hist
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp144.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hrev768 : rev64 (256#64 ||| 512#64) = 0x0003000000000000#64 := by decide
  have hrun : LibsignalTripleRatchet.RunsTo (tripleRatchetProgAtExt b ext) s
      (StateGF3bX b F key blocks rem s0) := by
    have hread32 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
      read64_seg3a_pad_32 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
    have hread40 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
      read64_seg3a_pad_40 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
    iterate 31 s2_step
    clear hread32 hread40
    refine LibsignalTripleRatchet.RunsTo.refl ?_
    obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg3a s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
      _ _ _ _ _ _ _ _ _ _ _ _ 0#64 0x0003000000000000#64 0x80#64 0#64 0#64 0x0003000000000000#64
    have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
      unfold DisjointRegions; bv_omega
    have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
      (hpre.disj_hm_fsp144.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
    have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
      (hpre.disj_hm_fsp144.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
    have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
      unfold DisjointRegions; bv_omega
    refine ⟨by fin_reg_x,
      ⟨by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x,
       by rw [HkdfExt.mem_setMem]
          exact finSaved_seg3a hsaved hag1 hag2 hag3 hag4 hd_hm64_saved hd_fsp64_saved,
       by rw [HkdfExt.mem_setMem]; exact s2Frame_of_frame_fsp hframe (frame_seg3a (Frame.refl s.mem _) hag1 hag2 hag3 hag4)⟩,
      by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x,
      by rw [HkdfExt.mem_setMem]
         refine (readBytes_fsp_64_seg3 _ _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
         rw [toLEBytes_8_rev32_append, toLEBytes_8_rev32_append,
             toLEBytes_8_rev32_append, toLEBytes_8_rev32_append]
         have htail : toLEBytes 8 0x80#64 ++ toLEBytes 8 0#64 ++ toLEBytes 8 0#64 ++
             toLEBytes 8 (rev64 768#64) =
             [0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 768#64 := by decide
         unfold outerBlock
         rw [digestBytes_eq_append h_in]
         simp only [List.append_assoc] at htail ⊢
         rw [htail]; rfl,
      by rw [HkdfExt.mem_setMem]
         exact ost_eq_seg3a host hag1 hag2 hag3 hag4 hd_hm64_ost hd_fsp64_ost⟩
  exact HkdfExt.runsTo_toE hrun

private theorem gseg3b_x_runsTo {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hComp : CompressOneStepExt b F ext)
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPreX b F key blocks rem s0)
    (hs : StateGF3bX b F key blocks rem s0 s) :
    Extract.RunsToE (tripleRatchetProgAtExt b ext) s (StateGF4X b F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hblk, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_stk : s.mem.RW (s0.sp - 16528#64) 16528 := hframe.rw_of_rw _ _ hpre.rw_fsp
  set h_in := F ((chunks64 blocks).foldl F (hmacInnerInit F key)) (innerLastBlockGen blocks rem)
  have hstep1 : LibsignalTripleRatchet.RunsTo (tripleRatchetProgAtExt b ext) s (fun s1 =>
      s1.pc = b + bv% (ls_off% "sha2::sha256::compress256") ∧
      s1.status = .Running ∧
      s1.sp = s0.sp - 144#64 ∧
      s1.readReg64 .lr = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 308) ∧
      s1.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64 ∧
      s1.readReg64 .x1 = s0.sp - 144#64 ∧
      s1.readReg64 .x2 = 1#64 ∧
      s1.readReg64 .x19 = s0.readReg64 .x0 ∧
      s1.readReg64 .x20 = s0.readReg64 .x1 ∧
      s1.readReg64 .x26 = s0.readReg64 .x26 ∧
      s1.readReg64 .x27 = s0.readReg64 .x27 ∧
      s1.readReg64 .x28 = s0.readReg64 .x28 ∧
      s1.readReg64 .x29 = s0.sp - 144#64 + 0x40#64 ∧
      s1.mem = s.mem) := by
    s2_step
    refine LibsignalTripleRatchet.RunsTo.refl ⟨rfl, hstat, hsp, rfl,
      by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x,
      by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, rfl⟩
  refine (HkdfExt.runsTo_toE hstep1).trans_full fun s1 hs1 _ _ => ?_
  rcases hs1 with ⟨hpc1, hstat1, hsp1, hlr1, hx0_1, hx1_1, hx2_1,
    hx19_1, hx20_1, hx26_1, hx27_1, hx28_1, hx29_1, hmem1⟩
  have hstk_eq : s1.sp - 16384#64 = s0.sp - 16528#64 := by rw [hsp1]; bv_omega
  have hrw_st : RW s1.mem (s0.readReg64 .x1 + 0x68#64) 32 := by
    rw [hmem1]; exact hrw_hm.sub (by bv_omega)
  have hrw_blk : RW s1.mem (s0.sp - 144#64) 64 := by
    rw [hmem1]; exact hrw_stk.sub (by bv_omega)
  have hrw_ext_stk : RW s1.mem (s1.sp - 16384#64) 16384 := by
    rw [hmem1, hstk_eq]; exact hrw_stk.sub (by bv_omega)
  have hd_st_blk : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_st_stk : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s1.sp - 16384#64) 16384 := by
    rw [hstk_eq]
    exact (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_blk_stk : DisjointRegions (s0.sp - 144#64) 64 (s1.sp - 16384#64) 16384 := by
    rw [hstk_eq]; unfold DisjointRegions; bv_omega
  have hsp1_al : (s1.sp &&& 15#64) = 0#64 := by rw [hsp1]; exact fsp_aligned hpre.sp_aligned
  refine (hComp hpc1 hstat1 hx0_1 hx1_1 hx2_1 (hmem1 ▸ host) (hmem1 ▸ hblk)
    hrw_st hrw_blk hrw_ext_stk hd_st_blk hd_st_stk hd_blk_stk hsp1_al).trans_full
    fun s2 hs2 _ _ => ?_
  rcases hs2 with ⟨hpc2, hstat2, hcc2, host2, _, hframe2⟩
  intro hL2
  refine ⟨s2, .refl s2, ⟨rfl, rfl⟩, ?_, hL2⟩
  set blk_out := shaStateBytes (F (hmacOuterInit F key) (outerBlock (digestBytes h_in)))
  set m_ideal := s.mem.writeBytes (s0.readReg64 .x1 + 0x68#64) blk_out
  have hlen_out : blk_out.length = 32 := HkdfExt.shaStateBytes_length _
  have hag_comp : AgreesOutside s.mem m_ideal (s0.readReg64 .x1 + 0x68#64) 32 := by
    rw [← hlen_out]; exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_out
  have hframe2' : Extract.S2Frame s.mem s2.mem
      [(s0.readReg64 .x1 + 0x68#64, blk_out.length), (s0.sp - 16528#64, 16384)] := by
    dsimp only [extHookStack] at hframe2
    rw [hlen_out, ← hmem1, ← hstk_eq]; exact hframe2
  have hag_on : HkdfExt.AgreesOn
      (fun a => s.mem.permNoLazy a = some Perm.rw ∧ OutsideRegion (s0.sp - 16528#64) 16384 a)
      s2.mem m_ideal :=
    HkdfExt.AgreesOn.of_s2Frame_writeBytes (by rwa [hlen_out]) hframe2' (by rw [hlen_out]; decide)
  have hP_saved : ∀ a, InRegion (s0.sp - 144#64 + 0x40#64) 0x50 a →
      s.mem.permNoLazy a = some Perm.rw ∧ OutsideRegion (s0.sp - 16528#64) 16384 a := by
    intro a ha
    have ha_stk : InRegion (s0.sp - 16528#64) 16528 a := by unfold InRegion at ha ⊢; bv_omega
    exact ⟨hrw_stk a ha_stk, by simp only [InRegion, OutsideRegion] at ha ⊢; bv_omega⟩
  have hd_ost_saved : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp144.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hframe_s2 : Extract.S2Frame s0.mem s2.mem
      [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 16528#64, 16528)] := by
    refine hframe.trans (hframe2'.mono fun a ha => ?_)
    intro r hr_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
    rcases hr_mem with rfl | rfl
    · have ha_hm := ha (s0.readReg64 .x1, 0x90) (by simp)
      rw [hlen_out]; unfold OutsideRegion at ha_hm ⊢; bv_omega
    · have ha_stk := ha (s0.sp - 16528#64, 16528) (by simp)
      unfold OutsideRegion at ha_stk ⊢; bv_omega
  refine
    { pc_eq := hpc2.trans hlr1
      common :=
        { status := hstat2
          sp_eq := (Extract.CallingConventionPreserved.sp_eq hcc2).trans hsp1
          x29_eq := (Extract.CallingConventionPreserved.x29 hcc2).trans hx29_1
          x26_eq := hcc2.2.2.2.2.2.2.2.2.1.trans hx26_1
          x27_eq := (Extract.CallingConventionPreserved.x27 hcc2).trans hx27_1
          x28_eq := hcc2.2.2.2.2.2.2.2.2.2.2.1.trans hx28_1
          saved := hag_on.finSaved_of (FinSaved.of_agreesOutside hsaved hag_comp hd_ost_saved) hP_saved
          frame := hframe_s2 }
      x19_eq := (Extract.CallingConventionPreserved.x19 hcc2).trans hx19_1
      x20_eq := (Extract.CallingConventionPreserved.x20 hcc2).trans hx20_1
      ost_eq := host2 }

private theorem gseg4a_x_runsTo {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPreX b F key blocks rem s0)
    (hs : StateGF4X b F key blocks rem s0 s) :
    Extract.RunsToE (tripleRatchetProgAtExt b ext) s (StateGF5X b F key blocks rem s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp144
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 32 := hframe.rw_of_rw _ _ hpre.rw_out
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_out := F (hmacOuterInit F key)
    (outerBlock (digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
      (innerLastBlockGen blocks rem))))
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_104_of_shaStateBytes s.mem (s0.readReg64 .x1) h_out host
  have hzero64 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
  have hd_fsp64_hm : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1) 0x90 :=
    hpre.disj_hm_fsp144.symm.sub_left _ ⟨by decide, by bv_omega⟩
  have hrun : LibsignalTripleRatchet.RunsTo (tripleRatchetProgAtExt b ext) s
      (StateGF5X b F key blocks rem s0) := by
    iterate 11 s2_step
    have hread128 := FinX.read32_seg4a_mid_x s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 128#64 (h_out.get 6)
      (Or.inl rfl) hd_fsp64_hm hw6
    have hread132 := FinX.read32_seg4a_mid_x s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 132#64 (h_out.get 7)
      (Or.inr rfl) hd_fsp64_hm hw7
    iterate 2 s2_step
    clear hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hread128 hread132 hd_fsp64_hm host
    iterate 15 s2_step
    refine LibsignalTripleRatchet.RunsTo.refl ?_
    obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg4a s.mem
      (s0.readReg64 .x0) (s0.readReg64 .x1) (s0.sp - 144#64) _ _ _ _ _ _ _ _
    have hd_hm_saved : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64 + 0x40#64) 0x50 :=
      hpre.disj_hm_fsp144.sub_right _ ⟨by decide, by bv_omega⟩
    have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
      unfold DisjointRegions; bv_omega
    have hd_out_saved : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
      hpre.disj_out_fsp144.sub_right _ ⟨by decide, by bv_omega⟩
    refine ⟨by fin_reg_x,
      ⟨by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x, by fin_reg_x,
       by rw [HkdfExt.mem_setMem]
          exact finSaved_seg4a hsaved hag1 hag2 hag3 hag4 hd_hm_saved hd_fsp64_saved hd_out_saved,
       by rw [HkdfExt.mem_setMem]; exact s2Frame_of_frame_fsp hframe (frame_seg4a (Frame.refl s.mem _) hag1 hag2 hag3 hag4)⟩,
      by rw [HkdfExt.mem_setMem]
         exact (readBytes_write32_8_digestBytes _ (s0.readReg64 .x0) h_out _ _ _ _ _ _ _ _
           (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
           (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)).trans
           (hmacWith_gen F key blocks rem hpre.key_le hpre.hmac_st.1 hpre.rem_lt).symm⟩
  exact HkdfExt.runsTo_toE hrun

private theorem gseg4b_x_runsTo {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)} {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPreX b F key blocks rem s0)
    (hs : StateGF5X b F key blocks rem s0 s) :
    Extract.RunsToE (tripleRatchetProgAtExt b ext) s (FinPostX F key (blocks ++ rem) s0) := by
  rcases hs with ⟨hpc, hcom, hout⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.rw_fsp144
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
  have hrun : LibsignalTripleRatchet.RunsTo (tripleRatchetProgAtExt b ext) s
      (FinPostX F key (blocks ++ rem) s0) := by
    iterate 7 s2_step
    refine LibsignalTripleRatchet.RunsTo.refl ⟨by simp (config := { decide := true }) only [arm64_norm], hstat,
      ⟨by simp (config := { decide := true }) only [arm64_norm], fun r hr => ?_⟩, hout, hframe⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [arm64_norm, hx26, hx27, hx28, hs19', hs20', hs21', hs22', hs23', hs24', hs25', hs29', hslr']
  exact HkdfExt.runsTo_toE hrun

/-- Multi-block `finalize_fixed` (`HmacStGen`) on `tripleRatchetProgAtExt b ext` at `16528` B
stack, returning `CallingConventionPreserved s0 s'` and `S2Frame`. -/
theorem finalize_fixed_gen_runsToE_base {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hMemset : MemsetStepExt b ext)
    (hComp : CompressOneStepExt b F ext)
    {s0 : State} {out hm : BitVec 64} {key blocks rem : List (BitVec 8)}
    (hpc : s0.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]"))
    (hstat : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out)
    (hx1 : s0.readReg64 .x1 = hm)
    (hkey_le : key.length ≤ 64)
    (hrem_lt : rem.length < 56)
    (hhm : HmacStGen s0.mem hm F key blocks rem)
    (hrw_out : RW s0.mem out 32)
    (hrw_hm : RW s0.mem hm 0x90)
    (hrw_stk : RW s0.mem (s0.sp - 16528#64) 16528)
    (hd_out_hm : DisjointRegions out 32 hm 0x90)
    (hd_out_stk : DisjointRegions out 32 (s0.sp - 16528#64) 16528)
    (hd_hm_stk : DisjointRegions hm 0x90 (s0.sp - 16528#64) 16528)
    (hsp_al : (s0.sp &&& 15#64) = 0#64) :
    Extract.RunsToE (tripleRatchetProgAtExt b ext) s0 (fun s' =>
      s'.pc = s0.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s0 s' ∧
      s'.mem.readBytes out 32 = hmacWith F key (blocks ++ rem) ∧
      Extract.S2Frame s0.mem s'.mem [(out, 32), (hm, 0x90), (s0.sp - 16528#64, 16528)]) := by
  have hpre : FinGenPreX b F key blocks rem s0 := {
    pc_eq := hpc, status := hstat, key_le := hkey_le, rem_lt := hrem_lt,
    hmac_st := hx1 ▸ hhm, rw_out := hx0 ▸ hrw_out, rw_hm := hx1 ▸ hrw_hm, rw_fsp := hrw_stk,
    disj_out_hm := hx0 ▸ hx1 ▸ hd_out_hm, disj_out_fsp := hx0 ▸ hd_out_stk,
    disj_hm_fsp := hx1 ▸ hd_hm_stk, sp_aligned := hsp_al
  }
  have hchain : Extract.RunsToE (tripleRatchetProgAtExt b ext) s0
      (FinPostX F key (blocks ++ rem) s0) :=
    (gseg1a_x_runsTo hpre).trans fun _ hs1 =>
    (gseg1b_x_runsTo hMemset hpre hs1).trans fun _ hs2 =>
    (gseg2a_x_runsTo hpre hs2).trans fun _ hs3 =>
    (gseg2b_x_runsTo hComp hpre hs3).trans fun _ hs4 =>
    (gseg3a_x_runsTo hpre hs4).trans fun _ hs5 =>
    (gseg3b_x_runsTo hComp hpre hs5).trans fun _ hs6 =>
    (gseg4a_x_runsTo hpre hs6).trans fun _ hs7 =>
    gseg4b_x_runsTo hpre hs7
  intro hL
  obtain ⟨s', hsteps, htr, ⟨hpc', hstat', hcs, hout', hfr'⟩, hL'⟩ := hchain hL
  rw [hx0] at hout' hfr'
  rw [hx1] at hfr'
  exact ⟨s', hsteps, htr,
    ⟨hpc', hstat', LibsignalTripleRatchet.CallingConventionPreserved_of_calleeSaved hcs htr,
      hout', hfr'⟩, hL'⟩

theorem finalize_fixed_single_runsToE_base {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hMemset : MemsetStepExt b ext)
    (hComp : CompressOneStepExt b F ext)
    {s0 : State} {out hm : BitVec 64} {key msg : List (BitVec 8)}
    (hpc : s0.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]"))
    (hstat : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out)
    (hx1 : s0.readReg64 .x1 = hm)
    (hkey_le : key.length ≤ 64)
    (hmsg_lt : msg.length < 56)
    (hhm : HmacSt s0.mem hm F key msg)
    (hrw_out : RW s0.mem out 32)
    (hrw_hm : RW s0.mem hm 0x90)
    (hrw_stk : RW s0.mem (s0.sp - 16528#64) 16528)
    (hd_out_hm : DisjointRegions out 32 hm 0x90)
    (hd_out_stk : DisjointRegions out 32 (s0.sp - 16528#64) 16528)
    (hd_hm_stk : DisjointRegions hm 0x90 (s0.sp - 16528#64) 16528)
    (hsp_al : (s0.sp &&& 15#64) = 0#64) :
    Extract.RunsToE (tripleRatchetProgAtExt b ext) s0 (fun s' =>
      s'.pc = s0.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s0 s' ∧
      s'.mem.readBytes out 32 = hmacWith F key msg ∧
      Extract.S2Frame s0.mem s'.mem [(out, 32), (hm, 0x90), (s0.sp - 16528#64, 16528)]) := by
  simpa only [List.nil_append] using
    finalize_fixed_gen_runsToE_base hMemset hComp hpc hstat hx0 hx1 hkey_le hmsg_lt
      (HmacStGen.of_hmacSt hhm) hrw_out hrw_hm hrw_stk hd_out_hm hd_out_stk hd_hm_stk hsp_al

end CryptoVerification.E2E.Pqxdh.ResponderCore
