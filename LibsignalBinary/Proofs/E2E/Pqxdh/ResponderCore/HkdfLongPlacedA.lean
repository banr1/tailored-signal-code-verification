/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLong
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Specifications.LibsignalE2E.State -- shake: keep

/-!
# Relocatable `expand_multi_info` (`okmLen = 96`, `info.length = 46`) — Cut Predicates and Part A

Defines relocatable loop cut-point structures and proves Block 1 (`T(1)`) and loop entry segments
(`iter_a1`, `iter_a2`, `iter_b1`) for Block `53` under `[LibsignalPlacement]`.
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

@[simp, arm64_norm]
theorem expPlacedFakeB_off_892 [LibsignalPlacement] :
    expPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 892) =
      (blkPl_53).base + 892#64 := by
  dsimp only [expPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem expPlacedFakeB_off_920 [LibsignalPlacement] :
    expPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 920) =
      (blkPl_53).base + 920#64 := by
  dsimp only [expPlacedFakeB]; bv_lin

@[simp, arm64_norm]
theorem expPlacedFakeB_off_988 [LibsignalPlacement] :
    expPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 988) =
      (blkPl_53).base + 988#64 := by
  dsimp only [expPlacedFakeB]; bv_lin

/-! ## Placed Loop Cut Predicates -/

/-- Relocatable cut `LoopA2_96Placed` at `lsρ lsMemcpySym` (`memcpy(esp + 96, infoPtr, 32)`). -/
structure StateLoopA2_96Placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (prk tPrev okmSoFar : List (BitVec 8)) (infoPtr : BitVec 64)
    (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = lsρ lsMemcpySym
  common  : ExpandCommon 96 s₀ s
  lr_eq   : s.readReg64 .lr = (blkPl_53).base + 892#64
  x0_eq   : s.readReg64 .x0 = esp s₀ + 96#64
  x1_eq   : s.readReg64 .x1 = infoPtr
  x2_eq   : s.readReg64 .x2 = 32#64
  x19_eq  : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq  : s.readReg64 .x23 = 32#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x28_eq  : s.readReg64 .x28 = 14#64
  m0_eq   : s.mem.read64 (esp s₀) = infoPtr + 32#64
  hmac_64 : HmacSt s.mem (esp s₀ + 64#64) F prk tPrev
  okm_pre : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Relocatable cut `LoopB1_96Placed` at `lsρ lsCompress256Sym` (`compress256(esp + 128, esp + 64, 1)`). -/
structure StateLoopB1_96Placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (prk info tPrev okmSoFar : List (BitVec 8)) (infoPtr : BitVec 64)
    (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq    : s.pc = lsρ lsCompress256Sym
  common   : ExpandCommon 96 s₀ s
  lr_eq    : s.readReg64 .lr = (blkPl_53).base + 920#64
  x0_eq    : s.readReg64 .x0 = esp s₀ + 128#64
  x1_eq    : s.readReg64 .x1 = esp s₀ + 64#64
  x2_eq    : s.readReg64 .x2 = 1#64
  x19_eq   : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq   : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq   : s.readReg64 .x23 = 32#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x28_eq   : s.readReg64 .x28 = 14#64
  m0_eq    : s.mem.read64 (esp s₀) = infoPtr + 32#64
  blk_64   : s.mem.readBytes (esp s₀ + 64#64) 64 = tPrev ++ info.take 32
  ist_128  : s.mem.readBytes (esp s₀ + 128#64) 32 = shaStateBytes (hmacInnerInit F prk)
  cnt1_160 : s.mem.read64 (esp s₀ + 160#64) = 2#64
  ost_168  : s.mem.readBytes (esp s₀ + 168#64) 32 = shaStateBytes (hmacOuterInit F prk)
  cnt2_200 : s.mem.read64 (esp s₀ + 200#64) = 1#64
  okm_pre  : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Relocatable cut `LoopB2_96Placed` at `lsρ lsMemcpySym` (`memcpy(esp + 64, infoPtr + 32, 14)`). -/
structure StateLoopB2_96Placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (prk info tPrev okmSoFar : List (BitVec 8)) (infoPtr : BitVec 64)
    (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq    : s.pc = lsρ lsMemcpySym
  common   : ExpandCommon 96 s₀ s
  lr_eq    : s.readReg64 .lr = (blkPl_53).base + 988#64
  x0_eq    : s.readReg64 .x0 = esp s₀ + 64#64
  x1_eq    : s.readReg64 .x1 = infoPtr + 32#64
  x2_eq    : s.readReg64 .x2 = 14#64
  x19_eq   : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq   : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq   : s.readReg64 .x23 = 32#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 rem
  pos_127  : s.mem.read8 (esp s₀ + 127#64) = 14#8
  ist_128  : s.mem.readBytes (esp s₀ + 128#64) 32 =
               shaStateBytes (F (hmacInnerInit F prk) (tPrev ++ info.take 32))
  cnt1_160 : s.mem.read64 (esp s₀ + 160#64) = 2#64
  ost_168  : s.mem.readBytes (esp s₀ + 168#64) 32 = shaStateBytes (hmacOuterInit F prk)
  cnt2_200 : s.mem.read64 (esp s₀ + 200#64) = 1#64
  okm_pre  : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Relocatable cut `LoopC_96Placed` at `(blkPl_123).base` (`finalize_fixed` entry in loop). -/
structure StateLoopC_96Placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (prk info tPrev okmSoFar : List (BitVec 8))
    (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq    : s.pc = (blkPl_123).base
  common   : ExpandCommon 96 s₀ s
  lr_eq    : s.readReg64 .lr = (blkPl_53).base + 672#64
  x0_eq    : s.readReg64 .x0 = esp s₀ + 208#64
  x1_eq    : s.readReg64 .x1 = esp s₀ + 240#64
  x19_eq   : s.readReg64 .x19 = BitVec.ofNat 64 i
  x21_eq   : s.readReg64 .x21 = s₀.readReg64 .x2 + BitVec.ofNat 64 (dstOff + 32)
  x22_eq   : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq   : s.readReg64 .x23 = 32#64
  x24_eq   : s.readReg64 .x24 = 64#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 (rem - 32)
  x28_eq   : s.readReg64 .x28 = esp s₀ + 64#64
  hmac_240 : HmacStGen s.mem (esp s₀ + 240#64) F prk (tPrev ++ info.take 32)
               (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre  : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-! ## Block 1 (`T(1)`) and Loop Entry Segments -/

section PlacedPartA

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]

theorem seg0_96_placed_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀ (StateX0p expPlacedFakeB 96 s₀) := by
  have hpc := hpre.pc_eq
  have hrun := hpre.status
  have hx3 := hpre.x3_eq
  have hsp_al := hpre.sp_aligned
  have hesp := esp_aligned hsp_al
  have hrw : s₀.mem.RW (esp s₀) 496 := by
    unfold esp; exact hpre.rw_stack.sub (by bv_omega)
  iterate 8 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc],
    by rw [State.status_setMem]; simp only [arm64_norm, hrun],
    by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx3],
    ?_, ?_⟩
  · simp only [mem_setMem]
    exact
      { m400 := by simp (config := { decide := true }) only [arm64_norm]
        m408 := by simp (config := { decide := true }) only [arm64_norm]
        m416 := by simp (config := { decide := true }) only [arm64_norm]
        m424 := by simp (config := { decide := true }) only [arm64_norm]
        m432 := by simp (config := { decide := true }) only [arm64_norm]
        m440 := by simp (config := { decide := true }) only [arm64_norm]
        m448 := by simp (config := { decide := true }) only [arm64_norm]
        m456 := by simp (config := { decide := true }) only [arm64_norm]
        m464 := by simp (config := { decide := true }) only [arm64_norm]
        m472 := by simp (config := { decide := true }) only [arm64_norm]
        m480 := by simp (config := { decide := true }) only [arm64_norm]
        m488 := by simp (config := { decide := true }) only [arm64_norm] }
  · exact ExpandFrame.of_agreesOutside_esp (off := 400#64) (sz := 96)
      (Frame.refl s₀.mem _) (by prove_agrees_esp) (by decide)

theorem seg1_96_placed_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hx : StateX0p expPlacedFakeB 96 s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateX1Placed C.F prk info infoPtr 96 s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.status
  have hsp := hx.sp_eq
  have hx29 := hx.x29_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hx3 := hx.x3_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.frame
  have hread_x0 : s.mem.Readable (s₀.readReg64 .x0) 0x90 := hpre.readable_x0 hx.frame
  have hread_x1 : s.mem.Readable (s₀.readReg64 .x1) 16 := hpre.readable_x1 hx.frame
  rcases hpre.read64_x0_write64_esp with ⟨h_x0_w0, h_x0_w⟩
  rcases hpre.read64_x1_write_esp with ⟨h_x1_w0, h_x1_w8, _, _⟩
  have hx1_val0 : s.mem.read64 (s₀.readReg64 .x1) = infoPtr :=
    hpre.info_ptr_eq hx.frame
  have hx1_val8 : s.mem.read64 (s₀.readReg64 .x1 + 8#64) = 46#64 :=
    hpre.info_len_eq_46 hx.frame
  have hpos_x0 : s.mem.read8 (s₀.readReg64 .x0 + 63#64) = 0#8 :=
    (hpre.hmac_x0 hx.frame).2.2.1
  iterate 40 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ⟨hrun, hsp, hx29, rfl, rfl,
     by simp (config := { decide := true }) only [arm64_norm],
     by simp (config := { decide := true }) only [arm64_norm],
     ExpandSaved.of_agreesOutside_low (off := 8#64) (sz := 312) hx.saved
       (by prove_agrees_esp) (by decide),
     ExpandFrame.of_agreesOutside_esp (off := 8#64) (sz := 312) hx.frame
       (by prove_agrees_esp) (by decide)⟩,
    rfl, rfl, rfl,
    by rw [hpre.info_len_eq]; rfl,
    rfl, rfl, rfl, rfl,
    by rw [hpre.info_len_eq]; rfl,
    ?_⟩
  simp only [mem_setMem]
  exact HmacSt.of_copy_empty_esp_64 (hpre.hmac_x0 hx.frame)
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])

theorem seg2a_96_placed_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hx : StateX1Placed C.F prk info infoPtr 96 s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateX1b expPlacedFakeB C.F prk info 96 s₀) := by
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
  have hx26 : s.readReg64 .x26 = 46#64 := by rw [hx.x26_eq, hpre.info_len_eq]
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 : s.readReg64 .x2 = 46#64 := by rw [hx.x2_eq, hpre.info_len_eq]
  have hlr := hx.lr_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 64#64) 46 := hrw_esp.sub (by bv_omega)
  have hread_info : s.mem.readBytes infoPtr 46 = info :=
    hpre.info_bytes_eq hx.common.frame
  have hx2_nat : (s.readReg64 .x2).toNat = 46 := by rw [hx2]; rfl
  refine s2_memcpy_step_placed C H hrun hpc hx0 hx1 hx2_nat hlr hread_info hrw_dst ?_
  have hA1 : AgreesOutside s.mem (s.mem.writeBytes (esp s₀ + 64#64) info) (esp s₀ + 64#64) 46 :=
    agreesOutside_writeBytes_le s.mem (esp s₀ + 64#64) info 46 (by rw [hpre.info_len_eq])
  have hrw_wb : (s.mem.writeBytes (esp s₀ + 64#64) info).RW (esp s₀) 496 :=
    rw_of_perm_eq hA1.2 hrw_esp
  iterate 13 s2_step
  refine RunsTo.refl ?_
  have hc1 : ExpandCommon 96 s₀ (s.setMem (s.mem.writeBytes (esp s₀ + 64#64) info)) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  refine ⟨by rw [State.pc_setMem]; simp only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 177) hc1
      (by rw [State.status_setMem]; simp only [arm64_norm, hrun])
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp)
      (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ?_⟩
  rw [mem_setMem]
  exact HmacSt.of_memcpy_counter_64_0_46 hx.hmac_64 hpre.info_len_eq

theorem seg2b_96_placed_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hx : StateX1b expPlacedFakeB C.F prk info 96 s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateX2Placed C.F prk info 96 s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx26 := hx.x26_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  iterate 13 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 240#64) (sz := 0x90) hx.common
      hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl, hx22, hx23, hx26, ?_⟩
  simp only [mem_setMem]
  exact HmacSt.of_copy_esp_64_240 hx.hmac_64
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

theorem fin1_96_placed_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hx : StateX2Placed C.F prk info 96 s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateX2r expPlacedFakeB C.F prk info 96 s₀) := by
  rcases hpre.fin_side_conditions hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hfin_pre : FinalizeFixedProof.FinPre finPlacedFakeB C.F prk (info ++ [1#8]) s :=
    { pc_eq := by rw [hx.pc_eq]; simp only [arm64_norm]
      status := hx.common.status
      key_le := hpre.prk_le
      msg_lt := by simp [hpre.info_len_eq]
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_240
      rw_out := by rw [hx.x0_eq]; exact hrw_x0
      rw_hm := by rw [hx.x1_eq]; exact hrw_x1
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sp
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; exact hd_x0_x1
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; exact hd_x0_sp
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; exact hd_x1_sp
      sp_aligned := by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned }
  refine (FinalizeFixedProof.finalize_fixed_placed_runsTo_of_other_block
    (C := C) (H := H) hcl hfin_pre).mono fun s' ⟨hpc', hrun', hcs, ht1, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'
  rw [hx.x0_eq] at ht1
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq] at hfr
  exact ⟨by simp only [arm64_norm, hpc'],
    ExpandCommon.of_fin_frame hx.common hrun' hcs hfr,
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans hx.x23_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq,
    ht1⟩

theorem seg3_96_placed_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hx : StateX2r expPlacedFakeB C.F prk info 96 s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoop expPlacedFakeB 96 (t1 C.F prk info) (t1 C.F prk info) 1 64 32 s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx26 : s.readReg64 .x26 = 64#64 := hx.x26_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) 96 := hpre.rw_x2_frame hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2) 32 := hrw_x2.sub (by bv_omega)
  iterate 4 s2_step
  refine s2_memcpy_step_placed C H hrun rfl rfl rfl rfl rfl hx.t1_208 hrw_dst ?_
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2) (t1 C.F prk info)
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + 0#64) 32 := by
    rw [BitVec.add_zero]
    exact agreesOutside_writeBytes_le s.mem (s₀.readReg64 .x2) (t1 C.F prk info) 32 (by simp)
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    hpre.common_of_agreesOutside_x2 hx.common hrun hsp hx29 hx27 hx20 hA1 ⟨by decide, by decide⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := hpre.rw_esp hc1.frame
  dsimp only [m₁] at hm16_1 hrw1_esp
  iterate 9 s2_step
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    rfl, ?_, ?_⟩
  · simp only [mem_setMem]
    have ht1_m1 : m₁.readBytes (esp s₀ + 208#64) 32 = t1 C.F prk info := by
      have hd : DisjointRegions (s₀.readReg64 .x2 + 0#64) 32 (esp s₀ + 208#64) 32 := by
        rw [BitVec.add_zero]
        exact (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2) ⟨by decide, by bv_omega⟩).sub_right
          (esp s₀ + 208#64) ⟨by decide, by unfold esp; bv_omega⟩
      exact (hA1.readBytes_eq hd (by decide)).trans hx.t1_208
    exact readBytes_32_esp_32_of_208 ht1_m1
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
  · have hd : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) 32 :=
      (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64)
        ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
        ⟨by decide, by bv_omega⟩
    dsimp only [mem_setMem]
    refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd (by prove_agrees_esp) (by decide) ?_
    conv_lhs => rw [← t1_length C.F prk info]
    exact Bytes.readBytes_writeBytes_same s.mem (s₀.readReg64 .x2) (t1 C.F prk info) (by simp)

theorem iter_a1_96_placed_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoop expPlacedFakeB 96 tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopA1 expPlacedFakeB C.F prk tPrev okmSoFar 96 i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx24 := hx.x24_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hread_x0 : s.mem.Readable (s₀.readReg64 .x0) 0x90 := hpre.readable_x0 hx.common.frame
  rcases hpre.read64_x0_write64_esp with ⟨h_x0_w0, h_x0_w⟩
  have hpos_x0 : s.mem.read8 (s₀.readReg64 .x0 + 63#64) = 0#8 :=
    (hpre.hmac_x0 hx.common.frame).2.2.1
  iterate 26 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc],
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 256) hx.common hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx19],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    ?_,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx24],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_, ?_⟩
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]
    rcases hrem with rfl | rfl <;> rfl
  · simp only [mem_setMem]
    exact HmacSt.of_copy_empty_esp_64 (hpre.hmac_x0 hx.common.frame)
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
  · dsimp only [mem_setMem]
    exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 256
      (by unfold DisjointRegions; bv_omega) (by prove_agrees_esp) (by decide) hx.t_cache
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd : DisjointRegions (esp s₀ + 64#64) 256 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 256 hd (by prove_agrees_esp)
        (by omega) hx.okm_pre

theorem iter_a2_96_placed_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopA1 expPlacedFakeB C.F prk tPrev okmSoFar 96 i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopA2_96Placed C.F prk tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  have hmin : min rem 32 = 32 := by rcases hrem with rfl | rfl <;> rfl
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hm8 := hx.common.m8_eq
  have hm16 := hx.common.m16_eq
  have hx8 := hx.x8_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 : s.readReg64 .x23 = 32#64 := by rw [hx.x23_eq, hmin]
  have hx24 := hx.x24_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hread_x1 : s.mem.Readable (s₀.readReg64 .x1) 16 := hpre.readable_x1 hx.common.frame
  rcases hpre.read64_x1_write_esp with ⟨h_x1_w0, h_x1_w8, h_x1_w8_0, h_x1_w8_8⟩
  have hx1_val0 : s.mem.read64 (s₀.readReg64 .x1) = infoPtr := hpre.info_ptr_eq hx.common.frame
  have hx1_val8 : s.mem.read64 (s₀.readReg64 .x1 + 8#64) = 46#64 :=
    hpre.info_len_eq_46 hx.common.frame
  iterate 19 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_write64_esp0_and_low64 hx.common hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) rfl,
    rfl, rfl, rfl, rfl, hx19, hx22, hx23, hx26, rfl,
    by simp (config := { decide := true }) only [arm64_norm],
    ?_, ?_⟩
  · simp only [mem_setMem]
    exact HmacSt.of_write32_empty hx.hmac_64 hx.t_cache ht_len
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
    · have hd64 : DisjointRegions (esp s₀ + 64#64) 64 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      have hd0 : DisjointRegions (esp s₀ + 0#64) 8 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 0#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      dsimp only [mem_setMem]
      refine readBytes_eq_of_agreesOutside_esp s₀ _ 0#64 8 hd0
        (by rw [BitVec.add_zero]
            exact (AgreesOutside.rfl' _ (esp s₀) 8).write64 (by bv_omega) (by decide))
        (by omega) ?_
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 64 hd64 (by prove_agrees_esp)
        (by omega) hx.okm_pre

theorem iter_b1_96_placed_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopA2_96Placed C.F prk tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopB1_96Placed C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := by
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
  have hrw_dst : s.mem.RW (esp s₀ + 96#64) 32 := hrw_esp.sub (by bv_omega)
  have hread_info46 : s.mem.readBytes infoPtr 46 = info := hpre.info_bytes_eq hx.common.frame
  have hread_info32 : s.mem.readBytes infoPtr 32 = info.take 32 := by
    have h := Bytes.readBytes_slice_of_readBytes_eq s.mem infoPtr info
      (by rw [hpre.info_len_eq]; exact hread_info46) 0 32 (by rw [hpre.info_len_eq]; decide)
    simpa using h
  have htake32_len : (info.take 32).length = 32 := by simp [hpre.info_len_eq]
  have hx2_nat : (s.readReg64 .x2).toNat = 32 := by rw [hx2]; rfl
  refine s2_memcpy_step_placed C H hrun hpc hx0 hx1 hx2_nat hlr hread_info32 hrw_dst ?_
  generalize hm1_def : s.mem.writeBytes (esp s₀ + 96#64) (info.take 32) = m₁
  have hA1 : AgreesOutside s.mem m₁ (esp s₀ + 96#64) 32 := by
    rw [← hm1_def]
    exact agreesOutside_writeBytes_le s.mem (esp s₀ + 96#64) (info.take 32) 32 (by rw [htake32_len])
  have hrw_wb : m₁.RW (esp s₀) 496 := rw_of_perm_eq hA1.2 hrw_esp
  have hcnt1_m1 : m₁.read64 (esp s₀ + 160#64) = 1#64 := by
    rw [hA1.read64_eq (by unfold DisjointRegions; bv_omega)]
    have h := hx.hmac_64.2.2.2.2.1
    rwa [show esp s₀ + 64#64 + 0x60#64 = esp s₀ + 160#64 by bv_lin] at h
  have hx27_96 : esp s₀ + 64#64 + 96#64 = esp s₀ + 160#64 := by bv_lin
  have hx27_64 : esp s₀ + 64#64 + 64#64 = esp s₀ + 128#64 := by bv_lin
  iterate 7 s2_step
  refine RunsTo.refl ?_
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  have hA2 : AgreesOutside m₁ (m₁.write64 (esp s₀ + 160#64) 2#64) (esp s₀ + 160#64) 8 :=
    agreesOutside_esp_write64 (AgreesOutside.rfl' _ _ _) (by decide)
  have hm0_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).read64 (esp s₀) = infoPtr + 32#64 := by
    refine (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    exact (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans hx.m0_eq
  have hblk_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).readBytes (esp s₀ + 64#64) 64 =
      tPrev ++ info.take 32 := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    rw [Bytes.readBytes_add m₁ (esp s₀ + 64#64) 32 32,
        show esp s₀ + 64#64 + BitVec.ofNat 64 32 = esp s₀ + 96#64 by bv_lin]
    have hleft : m₁.readBytes (esp s₀ + 64#64) 32 = tPrev := by
      refine (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
      have h := hx.hmac_64.2.1
      rwa [ht_len] at h
    have hright : m₁.readBytes (esp s₀ + 96#64) 32 = info.take 32 := by
      rw [← hm1_def]
      have h := Bytes.readBytes_writeBytes_same s.mem (esp s₀ + 96#64) (info.take 32) (by omega)
      rwa [htake32_len] at h
    rw [hleft, hright]
  have hist_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).readBytes (esp s₀ + 128#64) 32 =
      shaStateBytes (hmacInnerInit C.F prk) := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    refine (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    have h := hx.hmac_64.2.2.2.1
    rwa [show esp s₀ + 64#64 + 0x40#64 = esp s₀ + 128#64 by bv_lin] at h
  have hcnt1_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).read64 (esp s₀ + 160#64) = 2#64 := by
    simp (config := { decide := true }) only [arm64_norm]
  have host_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).readBytes (esp s₀ + 168#64) 32 =
      shaStateBytes (hmacOuterInit C.F prk) := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    refine (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    have h := hx.hmac_64.2.2.2.2.2.1
    rwa [show esp s₀ + 64#64 + 0x68#64 = esp s₀ + 168#64 by bv_lin] at h
  have hcnt2_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).read64 (esp s₀ + 200#64) = 1#64 := by
    refine (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    refine (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    have h := hx.hmac_64.2.2.2.2.2.2
    rwa [show esp s₀ + 64#64 + 0x88#64 = esp s₀ + 200#64 by bv_lin] at h
  have hokm_m2 :
      (m₁.write64 (esp s₀ + 160#64) 2#64).readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd1 : DisjointRegions (esp s₀ + 96#64) 32 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 96#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      have hd2 : DisjointRegions (esp s₀ + 160#64) 8 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 160#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      exact (hA2.readBytes_eq hd2 (by omega)).trans
        ((hA1.readBytes_eq hd1 (by omega)).trans hx.okm_pre)
  refine ⟨by simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 160#64) (sz := 8) hc1
      (by simp only [arm64_norm, hrun])
      (by simp (config := { decide := true }) only [arm64_norm, hsp])
      (by simp (config := { decide := true }) only [arm64_norm, hx29])
      (by simp (config := { decide := true }) only [arm64_norm, hx27])
      (by simp (config := { decide := true }) only [arm64_norm, hx20])
      (by simp only [arm64_norm]; exact hA2) (by decide),
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hx27_64],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hx19],
    by simp (config := { decide := true }) only [arm64_norm, hx22],
    by simp (config := { decide := true }) only [arm64_norm, hx23],
    by simp (config := { decide := true }) only [arm64_norm, hx26],
    by simp (config := { decide := true }) only [arm64_norm, hx28],
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hm0_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hblk_m2,
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

end PlacedPartA

end CryptoVerification.E2E.Pqxdh.ResponderCore
