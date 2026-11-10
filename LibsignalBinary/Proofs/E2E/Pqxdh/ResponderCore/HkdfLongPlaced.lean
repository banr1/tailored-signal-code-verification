/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLongPlacedA
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlacedA
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Specifications.LibsignalE2E.State -- shake: keep

/-!
# Relocatable `expand_multi_info` (`okmLen = 96`, `info.length = 46`) — Loop Tail and Assembly

Proves the remaining loop body segments, epilogue, and full relocatable
`expand_multi_info_96_46_placed_runsTo` for Block `53` under `[LibsignalPlacement]`.
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

open Arm64 ProofLib ProofLib.Variant
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet.Expand

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

section PlacedPartB

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]

theorem iter_b2_96_placed_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopB1_96Placed C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopB2_96Placed C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hlr := hx.lr_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrw_128 : s.mem.RW (esp s₀ + 128#64) 32 := hrw_esp.sub (by bv_omega)
  have hblk_len : (tPrev ++ info.take 32).length = 64 := by simp [ht_len, hpre.info_len_eq]
  refine s2_compress256_step_placed C H hrun hpc hx0 hx1 hx2 hlr
    hx.ist_128 hx.blk_64 hblk_len hrw_128 ?_
  generalize hist_def : shaStateBytes (C.F (hmacInnerInit C.F prk) (tPrev ++ info.take 32)) = ist'
  have hist'_len : ist'.length = 32 := by rw [← hist_def]; exact shaStateBytes_length _
  generalize hm1_def : s.mem.writeBytes (esp s₀ + 128#64) ist' = m₁
  have hA1 : AgreesOutside s.mem m₁ (esp s₀ + 128#64) 32 := by
    rw [← hm1_def]
    exact agreesOutside_writeBytes_le s.mem (esp s₀ + 128#64) ist' 32 (by rw [hist'_len])
  have hrw_wb : m₁.RW (esp s₀) 496 := rw_of_perm_eq hA1.2 hrw_esp
  have hm0_m1 : m₁.read64 (esp s₀) = infoPtr + 32#64 := by
    rw [hA1.read64_eq (by unfold DisjointRegions; bv_omega), hx.m0_eq]
  iterate 11 s2_step
  refine RunsTo.refl ?_
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  have hA2 : AgreesOutside m₁ ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8)
      (esp s₀ + 127#64) 1 := by
    refine agreesOutside_esp_write8 ?_ (by decide)
    exact agreesOutside_esp_write8 (AgreesOutside.rfl' _ _ _) (by decide)
  have hpos_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).read8
      (esp s₀ + 127#64) = 14#8 :=
    Memory.read8_write8_same _ _ _
  have hist_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).readBytes
      (esp s₀ + 128#64) 32 =
      shaStateBytes (C.F (hmacInnerInit C.F prk) (tPrev ++ info.take 32)) := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    rw [← hm1_def, hist_def]
    have h :=
      Bytes.readBytes_writeBytes_same s.mem (esp s₀ + 128#64) ist' (by rw [hist'_len]; decide)
    rwa [hist'_len] at h
  have hcnt1_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).read64
      (esp s₀ + 160#64) = 2#64 := by
    refine (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    exact (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans hx.cnt1_160
  have host_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).readBytes
      (esp s₀ + 168#64) 32 =
      shaStateBytes (hmacOuterInit C.F prk) := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    exact (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans hx.ost_168
  have hcnt2_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).read64
      (esp s₀ + 200#64) = 1#64 := by
    refine (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    exact (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans hx.cnt2_200
  have hokm_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).readBytes
      (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd1 : DisjointRegions (esp s₀ + 128#64) 32 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 128#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      have hd2 : DisjointRegions (esp s₀ + 127#64) 1 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 127#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      exact (hA2.readBytes_eq hd2 (by omega)).trans
        ((hA1.readBytes_eq hd1 (by omega)).trans hx.okm_pre)
  refine ⟨by simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 127#64) (sz := 1) hc1
      (by simp only [arm64_norm, hrun])
      (by simp (config := { decide := true }) only [arm64_norm, hsp])
      (by simp (config := { decide := true }) only [arm64_norm, hx29])
      (by simp (config := { decide := true }) only [arm64_norm, hx27])
      (by simp (config := { decide := true }) only [arm64_norm, hx20])
      (by simp only [arm64_norm]; exact hA2) (by decide),
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hx19],
    by simp (config := { decide := true }) only [arm64_norm, hx22],
    by simp (config := { decide := true }) only [arm64_norm, hx23],
    by simp (config := { decide := true }) only [arm64_norm, hx26],
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hpos_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hist_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hcnt1_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact host_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hcnt2_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hokm_m2⟩

theorem iter_b3_96_placed_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopB2_96Placed C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopB_96 expPlacedFakeB C.F prk info tPrev okmSoFar i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hlr := hx.lr_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx26 := hx.x26_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 64#64) 14 := hrw_esp.sub (by bv_omega)
  have hread_info46 : s.mem.readBytes infoPtr 46 = info := hpre.info_bytes_eq hx.common.frame
  have hdrop_len : (info.drop 32).length = 14 := by simp [hpre.info_len_eq]
  have hread_info14 : s.mem.readBytes (infoPtr + 32#64) 14 = info.drop 32 := by
    have h := Bytes.readBytes_slice_of_readBytes_eq s.mem infoPtr info
      (by rw [hpre.info_len_eq]; exact hread_info46) 32 14 (by rw [hpre.info_len_eq])
    have htake : (info.drop 32).take 14 = info.drop 32 :=
      List.take_of_length_le (by rw [hdrop_len])
    exact h.trans htake
  have hx2_nat : (s.readReg64 .x2).toNat = 14 := by rw [hx2]; rfl
  refine s2_memcpy_step_placed C H hrun hpc hx0 hx1 hx2_nat hlr hread_info14 hrw_dst ?_
  let m₁ := s.mem.writeBytes (esp s₀ + 64#64) (info.drop 32)
  have hA1 : AgreesOutside s.mem m₁ (esp s₀ + 64#64) 14 :=
    agreesOutside_writeBytes_le s.mem (esp s₀ + 64#64) (info.drop 32) 14 (by rw [hdrop_len])
  have hrw_wb : m₁.RW (esp s₀) 496 := rw_of_perm_eq hA1.2 hrw_esp
  have hpos_m1 : m₁.read8 (esp s₀ + 127#64) = 14#8 := by
    rw [hA1.1 (esp s₀ + 127#64) (by simp only [OutsideRegion]; bv_omega), hx.pos_127]
  dsimp only [m₁] at hrw_wb hpos_m1
  have hi_eq : (BitVec.ofNat 64 i == 255#64) = false := by rcases hi with rfl | rfl <;> rfl
  have hi_ne : (BitVec.ofNat 64 i != 255#64) = true := by rcases hi with rfl | rfl <;> rfl
  have hi_cmp : (AddWithCarry64 (BitVec.ofNat 64 i) (bv% (2 ^ 64 - 256)) true).2.z = false := by
    rcases hi with rfl | rfl <;> rfl
  have hi_add1 : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 i) + 1#32) =
      BitVec.ofNat 64 (i + 1) := by
    rcases hi with rfl | rfl <;> rfl
  iterate 14 s2_step
  refine RunsTo.refl ?_
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  let c := BitVec.ofNat 8 (i + 1)
  have hA2 : AgreesOutside m₁
      (((m₁.write8 (esp s₀ + 240#64) c).write8 (esp s₀ + 78#64) c).write8 (esp s₀ + 127#64) 15#8)
      (esp s₀ + 64#64) 177 := by
    refine agreesOutside_esp_write8 ?_ (by decide)
    refine agreesOutside_esp_write8 ?_ (by decide)
    exact agreesOutside_esp_write8 (AgreesOutside.rfl' _ _ _) (by decide)
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 177) hc1
      (by rw [State.status_setMem]; simp only [arm64_norm, hrun])
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by simp only [arm64_norm]; exact hA2)
      (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx19],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ?_, ?_⟩
  · rw [mem_setMem]
    exact HmacStGen.of_memcpy14_counter ht_len hpre.info_len_eq
      hx.ist_128 hx.cnt1_160 hx.ost_168 hx.cnt2_200
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd1 : DisjointRegions (esp s₀ + 64#64) 14 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      have hd2 : DisjointRegions (esp s₀ + 64#64) 177 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      simp only [arm64_norm]
      exact (hA2.readBytes_eq hd2 (by omega)).trans
        ((hA1.readBytes_eq hd1 (by omega)).trans hx.okm_pre)

theorem iter_c_96_placed_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopB_96 expPlacedFakeB C.F prk info tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopC_96Placed C.F prk info tPrev okmSoFar i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  iterate 17 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 240#64) (sz := 0x90) hx.common
      hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl, hx19,
    by rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl,
    hx22, hx23, hx24,
    by rcases hrem with rfl | rfl <;> rfl,
    hx28, ?_, ?_⟩
  · simp only [mem_setMem]
    exact HmacStGen.of_copy_esp_64_240 hx.hmac_64
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd : DisjointRegions (esp s₀ + 240#64) 0x90 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 240#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 240#64 0x90 hd (by prove_agrees_esp)
        (by omega) hx.okm_pre

theorem iter_fin_96_placed_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopC_96Placed C.F prk info tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar 96 i rem dstOff s₀) := by
  have hmin : min rem 32 = 32 := by rcases hrem with rfl | rfl <;> rfl
  rcases hpre.fin_side_conditions hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hfin_pre : FinGenPre finPlacedFakeB C.F prk (tPrev ++ info.take 32)
      (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) s :=
    { pc_eq := by rw [hx.pc_eq]; simp only [arm64_norm]
      status := hx.common.status
      key_le := hpre.prk_le
      rem_lt := by simp [hpre.info_len_eq]
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_240
      rw_out := by rw [hx.x0_eq]; exact hrw_x0
      rw_hm := by rw [hx.x1_eq]; exact hrw_x1
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sp
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; exact hd_x0_x1
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; exact hd_x0_sp
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; exact hd_x1_sp
      sp_aligned := by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned }
  refine (finalize_fixed_gen_placed_runsTo_of_other_block (C := C) (H := H) hcl hfin_pre).mono
    fun s' ⟨hpc', hrun', hcs, ht, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'
  rw [hx.x0_eq, List.append_assoc, ← List.append_assoc (info.take 32),
      List.take_append_drop, ← List.append_assoc] at ht
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq] at hfr
  have hokm' : s'.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · refine (Expand.Frame.readBytes_eq hfr (fun r hr => ?_) (by omega)).trans hx.okm_pre
      have hd_stk : DisjointRegions (s₀.sp - 640#64) 640 (s₀.readReg64 .x2) dstOff :=
        hpre.disj_x2_stack.symm.sub_right (s₀.readReg64 .x2) ⟨by omega, by bv_omega⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact hd_stk.sub_left _ ⟨by simp, by unfold esp; bv_omega⟩
  exact ⟨by simp only [arm64_norm, hpc'],
    ExpandCommon.of_fin_frame hx.common hrun' hcs hfr,
    (CalleeSaved.x19 hcs).trans hx.x19_eq,
    (CalleeSaved.x21 hcs).trans (by rw [hmin]; exact hx.x21_eq),
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans (by rw [hmin]; exact hx.x23_eq),
    (CalleeSaved.x24 hcs).trans hx.x24_eq,
    (CalleeSaved.x26 hcs).trans (by rw [hmin]; exact hx.x26_eq),
    (CalleeSaved.x28 hcs).trans hx.x28_eq,
    ht, hokm'⟩

theorem iter_d_continue_96_placed_runsTo {prk info tPrev okmSoFar tNext : List (BitVec 8)}
    {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (htNext : tNext = hmacWith C.F prk (tPrev ++ info ++ [2#8]))
    (hx : StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar 96 1 64 32 s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoop expPlacedFakeB 96 tNext (okmSoFar ++ tNext) 2 32 64 s₀) := by
  have ht_208 : s.mem.readBytes (esp s₀ + 208#64) 32 = tNext := htNext ▸ hx.t_208
  have ht_len : tNext.length = 32 := by rw [htNext, length_hmacWith]
  clear htNext
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq
  have hx23 : s.readReg64 .x23 = 32#64 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 : s.readReg64 .x26 = 32#64 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) 96 := hpre.rw_x2_frame hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2 + 32#64) 32 := hrw_x2.sub (by bv_omega)
  iterate 4 s2_step
  refine s2_memcpy_step_placed C H hrun rfl rfl rfl rfl rfl ht_208 hrw_dst ?_
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2 + 32#64) tNext
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + 32#64) 32 :=
    agreesOutside_writeBytes_le s.mem _ tNext 32 (by omega)
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    hpre.common_of_agreesOutside_x2 hx.common hrun hsp hx29 hx27 hx20 hA1 ⟨by decide, by decide⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := hpre.rw_esp hc1.frame
  dsimp only [m₁] at hm16_1 hrw1_esp
  iterate 6 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx24],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_⟩
  · simp only [mem_setMem]
    have ht_m1 : m₁.readBytes (esp s₀ + 208#64) 32 = tNext := by
      have hd : DisjointRegions (s₀.readReg64 .x2 + 32#64) 32 (esp s₀ + 208#64) 32 :=
        (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + 32#64) ⟨by decide, by bv_omega⟩).sub_right
          (esp s₀ + 208#64) ⟨by decide, by unfold esp; bv_omega⟩
      exact (hA1.readBytes_eq hd (by decide)).trans ht_208
    exact readBytes_32_esp_32_of_208 ht_m1
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
  · have hd2 : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) 64 :=
      (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64)
        ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2) ⟨by decide, by bv_omega⟩
    dsimp only [mem_setMem]
    refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd2 (by prove_agrees_esp) (by decide) ?_
    rw [show (64 : ℕ) = 32 + 32 from rfl, Bytes.readBytes_add m₁ (s₀.readReg64 .x2) 32 32]
    have hleft : m₁.readBytes (s₀.readReg64 .x2) 32 = okmSoFar := by
      have hd1 : DisjointRegions (s₀.readReg64 .x2 + 32#64) 32 (s₀.readReg64 .x2) 32 := by
        unfold DisjointRegions; bv_omega
      exact (hA1.readBytes_eq hd1 (by decide)).trans hx.okm_pre
    have hright : m₁.readBytes (s₀.readReg64 .x2 + 32#64) 32 = tNext := by
      have h := Bytes.readBytes_writeBytes_same s.mem (s₀.readReg64 .x2 + 32#64) tNext (by omega)
      rwa [ht_len] at h
    rw [hleft, hright]

theorem iter_d_done_96_placed_runsTo {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hokm : okmSoFar ++ hmacWith C.F prk (tPrev ++ info ++ [3#8]) =
              hkdfExpand C.F prk info 96)
    (hx : StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar 96 2 32 64 s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateDone expPlacedFakeB C.F prk info 96 s₀) := by
  generalize htNext : hmacWith C.F prk (tPrev ++ info ++ [3#8]) = tNext
  have ht_208 : s.mem.readBytes (esp s₀ + 208#64) 32 = tNext := htNext ▸ hx.t_208
  have ht_len : tNext.length = 32 := by rw [← htNext, length_hmacWith]
  rw [htNext] at hokm
  clear htNext
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq
  have hx23 : s.readReg64 .x23 = 32#64 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 : s.readReg64 .x26 = 0#64 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) 96 := hpre.rw_x2_frame hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2 + 64#64) 32 := hrw_x2.sub (by bv_omega)
  iterate 4 s2_step
  refine s2_memcpy_step_placed C H hrun rfl rfl rfl rfl rfl ht_208 hrw_dst ?_
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2 + 64#64) tNext
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + 64#64) 32 :=
    agreesOutside_writeBytes_le s.mem _ tNext 32 (by omega)
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    hpre.common_of_agreesOutside_x2 hx.common hrun hsp hx29 hx27 hx20 hA1 ⟨by decide, by decide⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := hpre.rw_esp hc1.frame
  dsimp only [m₁] at hm16_1 hrw1_esp
  iterate 6 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    ?_⟩
  have hd2 : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) 96 :=
    hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64) ⟨by decide, by unfold esp; bv_omega⟩
  dsimp only [mem_setMem]
  refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd2 (by prove_agrees_esp) (by decide) ?_
  rw [show (96 : ℕ) = 64 + 32 from rfl, Bytes.readBytes_add m₁ (s₀.readReg64 .x2) 64 32]
  have hleft : m₁.readBytes (s₀.readReg64 .x2) 64 = okmSoFar := by
    have hd1 : DisjointRegions (s₀.readReg64 .x2 + 64#64) 32 (s₀.readReg64 .x2) 64 := by
      unfold DisjointRegions; bv_omega
    exact (hA1.readBytes_eq hd1 (by decide)).trans hx.okm_pre
  have hright : m₁.readBytes (s₀.readReg64 .x2 + 64#64) 32 = tNext := by
    have h := Bytes.readBytes_writeBytes_same s.mem (s₀.readReg64 .x2 + 64#64) tNext (by omega)
    rwa [ht_len] at h
  rw [hleft, hright, hokm]

theorem epilogue_96_placed_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hx : StateDone expPlacedFakeB C.F prk info 96 s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s (ExpandPost C.F prk info 96 s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  rcases hx.common.saved with
    ⟨m400, m408, m416, m424, m432, m440, m448, m456, m464, m472, m480, m488⟩
  iterate 8 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl, hrun, ⟨(esp_eq_add s₀).symm, ?_⟩, hx.okm_all, hx.common.frame⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem iter_to_fin_96_placed_runsTo {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {i rem dstOff : ℕ} {s₀ s : State}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoop expPlacedFakeB 96 tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar 96 i rem dstOff s₀) := by
  have h16 : RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopC_96Placed C.F prk info tPrev okmSoFar i rem dstOff s₀) :=
    (iter_a1_96_placed_runsTo hpre hrem hdst hx).trans fun _ hs1 =>
    (iter_a2_96_placed_runsTo hpre ht_len hrem hdst hs1).trans fun _ hs2 =>
    (iter_b1_96_placed_runsTo hpre ht_len hdst hs2).trans fun _ hs3 =>
    (iter_b2_96_placed_runsTo hpre ht_len hdst hs3).trans fun _ hs4 =>
    (iter_b3_96_placed_runsTo hpre ht_len hi hdst hs4).trans fun _ hs5 =>
    iter_c_96_placed_runsTo hpre hrem hdst hs5
  refine h16.trans_keepsFrozen fun s6 hs6 hkf => ?_
  have hcl6 : LibsignalCodeLoaded lsmpl s6.mem :=
    fun j hj hunmut ext panics svc => (hcl j hj hunmut ext panics svc).of_keepsFrozen hkf
  exact iter_fin_96_placed_runsTo hcl6 hpre ht_len hrem hdst hs6

/-- Full relocatable `RunsTo` assembly for `expand_multi_info` (Block `53`) when `okmLen = 96`
and `info.length = 46`. -/
theorem expand_multi_info_96_46_placed_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {s₀ : State}
    (hcl : LibsignalCodeLoaded lsmpl s₀.mem)
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀ (ExpandPost C.F prk info 96 s₀) := by
  have h04 : RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀
      (StateX2Placed C.F prk info 96 s₀) :=
    (seg0_96_placed_runsTo hpre).trans fun _ hs1 =>
    (seg1_96_placed_runsTo hpre hs1).trans fun _ hs2 =>
    (seg2a_96_placed_runsTo hpre hs2).trans fun _ hs3 =>
    seg2b_96_placed_runsTo hpre hs3
  have h06 : RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀
      (StateLoop expPlacedFakeB 96 (t1 C.F prk info) (t1 C.F prk info) 1 64 32 s₀) :=
    h04.trans_keepsFrozen fun s4 hs4 hkf =>
      let hcl4 : LibsignalCodeLoaded lsmpl s4.mem :=
        fun j hj hunmut ext panics svc => (hcl j hj hunmut ext panics svc).of_keepsFrozen hkf
      (fin1_96_placed_runsTo hcl4 hpre hs4).trans fun _ hs5 =>
      seg3_96_placed_runsTo hpre hs5
  have h08 : RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀
      (StateLoop expPlacedFakeB 96 (t2 C.F prk info)
        (t1 C.F prk info ++ t2 C.F prk info) 2 32 64 s₀) :=
    h06.trans_keepsFrozen fun s6 hs6 hkf =>
      let hcl6 : LibsignalCodeLoaded lsmpl s6.mem :=
        fun j hj hunmut ext panics svc => (hcl j hj hunmut ext panics svc).of_keepsFrozen hkf
      (iter_to_fin_96_placed_runsTo hcl6 hpre (t1_length C.F prk info)
        (Or.inl rfl) (Or.inl rfl) (by decide) hs6).trans fun _ hs7 =>
      iter_d_continue_96_placed_runsTo hpre (tNext := t2 C.F prk info) rfl hs7
  refine h08.trans_keepsFrozen fun s8 hs8 hkf => ?_
  have hcl8 : LibsignalCodeLoaded lsmpl s8.mem :=
    fun j hj hunmut ext panics svc => (hcl j hj hunmut ext panics svc).of_keepsFrozen hkf
  refine (iter_to_fin_96_placed_runsTo hcl8 hpre (t2_length C.F prk info)
    (Or.inr rfl) (Or.inr rfl) (by decide) hs8).trans fun s9 hs9 => ?_
  have hokm96 : (t1 C.F prk info ++ t2 C.F prk info) ++
      hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8]) =
      hkdfExpand C.F prk info 96 := by
    rw [show hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8]) = t3 C.F prk info from rfl,
        hkdfExpand_96_eq]
  refine (iter_d_done_96_placed_runsTo hpre hokm96 hs9).trans fun s10 hs10 => ?_
  exact epilogue_96_placed_runsTo hpre hs10

end PlacedPartB

end CryptoVerification.E2E.Pqxdh.ResponderCore
