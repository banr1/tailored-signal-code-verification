/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes

/-!
# Block 1 (`T(1)`) Segment Proofs for `expand_multi_info`

Proves symbolic-execution segments `seg0_runsTo` through `seg3_runsTo` for the initial
`T(1) = HMAC(prk, info ‖ [1])` block of `GenericHkdf<Hmac<Sha256>>::expand_multi_info`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)

namespace Expand

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

section Block1

variable {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
  {abs ext : String → Option (State → State)}

/-- Segment 0 (`b + 0x1a874` → `b + 0x1a894`, 8 steps): prologue saving `x19..x30` at
`esp s₀ + 400 .. 496` and setting `sp = esp s₀`, `x29 = esp s₀ + 400#64`. -/
theorem seg0_runsTo [HkdfHooks C.F ext] {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀) :
    RunsTo (tripleRatchetProgAtExt b ext) s₀ (StateX0p b okmLen s₀) := by
  have hpc := hpre.pc_eq
  have hrun := hpre.status
  have hx3 := hpre.x3_eq
  have hsp_al : (s₀.sp &&& 15#64) = 0#64 := hpre.sp_aligned
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s₀.mem.RW (esp s₀) 496 :=
    ExpandFrame.rw_esp hpre (Frame.refl s₀.mem _)
  iterate 8 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc], hrun,
    by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx3], ?_, ?_⟩
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

/-- Segment 1 (`b + 0x1a894` → `b + 0x51b0c`, 40 steps): copies `Hmac` to `esp + 64`, stores
`(infoHdrA, esp + 32)` at `esp + 8..24`, and sets up `memcpy(esp + 64, infoPtr, info.length)`. -/
theorem seg1_runsTo [HkdfHooks C.F ext] {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀)
    (hx : StateX0p b okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateX1 b C.F prk info infoPtr okmLen s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.status
  have hsp := hx.sp_eq
  have hx29 := hx.x29_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hx3 := hx.x3_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.frame
  have hread_x0 : s.mem.Readable (s₀.readReg64 .x0) 0x90 := ExpandFrame.readable_x0 hpre hx.frame
  have hread_x1 : s.mem.Readable (s₀.readReg64 .x1) 16 := ExpandFrame.readable_x1 hpre hx.frame
  rcases read64_x0_write64_esp hpre with ⟨h_x0_w0, h_x0_w⟩
  rcases read64_x1_write_esp hpre with ⟨h_x1_w0, h_x1_w8, _, _⟩
  have hx1_val0 : s.mem.read64 (s₀.readReg64 .x1) = infoPtr :=
    ExpandFrame.info_ptr_eq hpre hx.frame
  have hx1_val8 : s.mem.read64 (s₀.readReg64 .x1 + 8#64) = BitVec.ofNat 64 info.length :=
    ExpandFrame.info_len_eq hpre hx.frame
  have hpos_x0 : s.mem.read8 (s₀.readReg64 .x0 + 63#64) = 0#8 :=
    (ExpandFrame.hmac_x0 hpre hx.frame).2.2.1
  have h_okm_ule : BitVec.ule 32#64 (BitVec.ofNat 64 okmLen) = true := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  have h_okm_ult : BitVec.ult (BitVec.ofNat 64 okmLen) 32#64 = false := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  have h_okm_hi : BitVec.ult 32#64 (BitVec.ofNat 64 okmLen) = true := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  have h_okm_ls : BitVec.ule (BitVec.ofNat 64 okmLen) 32#64 = false := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  have h_okm_cmp : (AddWithCarry64 (BitVec.ofNat 64 okmLen) (bv% (2 ^ 64 - 33)) true).2.c = true := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  rcases cmp_lt64_lemmas (by have := hpre.info_lt; omega : info.length < 64) with
    ⟨h_info_ule, h_info_ult, h_info_cmp⟩
  iterate 40 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ⟨hrun, hsp, hx29, rfl, rfl,
     by simp (config := { decide := true }) only [arm64_norm],
     by simp (config := { decide := true }) only [arm64_norm],
     ExpandSaved.of_agreesOutside_low (off := 8#64) (sz := 312) hx.saved (by prove_agrees_esp) (by decide),
     ExpandFrame.of_agreesOutside_esp (off := 8#64) (sz := 312) hx.frame (by prove_agrees_esp) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [mem_setMem]
  exact HmacSt.of_copy_empty_esp_64 (ExpandFrame.hmac_x0 hpre hx.frame)
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

private theorem HmacSt.of_memcpy_counter_64_0 {m₀ : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key info : List (BitVec 8)}
    (h₀ : HmacSt m₀ (esp s₀ + 64#64) F key [])
    (hinfo : info.length < 23) :
    HmacSt (((((m₀.writeBytes (esp s₀ + 64#64) info).write8
      (esp s₀ + 127#64) (BitVec.ofNat 8 info.length)).write8
      (esp s₀ + 240#64) 1#8).write8
      (esp s₀ + 64#64 + BitVec.ofNat 64 info.length) 1#8).write8
      (esp s₀ + 127#64) (BitVec.ofNat 8 (info.length + 1)))
      (esp s₀ + 64#64) F key (info ++ [1#8]) := by
  have hm := HmacSt.of_memcpy_counter h₀ (by decide) hinfo
    (b1 := BitVec.ofNat 8 info.length) (c := 1#8)
  dsimp only [List.length_nil, Nat.zero_add, List.nil_append] at hm
  have h64_0 : esp s₀ + 64#64 + BitVec.ofNat 64 0 = esp s₀ + 64#64 := by bv_lin
  have h127 : esp s₀ + 64#64 + 63#64 = esp s₀ + 127#64 := by bv_lin
  have h240 : esp s₀ + 64#64 + 176#64 = esp s₀ + 240#64 := by bv_lin
  rw [h64_0, h127, h240, Nat.zero_add] at hm
  exact hm

theorem canWrite_esp_64_add {m : Memory} {s₀ : State} {k : ℕ}
    (hrw : m.RW (esp s₀) 496) (hk : k < 64) :
    m.canWrite (esp s₀ + (64#64 + BitVec.ofNat 64 k)) 1 = true ∧
    m.canWrite (esp s₀ + 64#64 + BitVec.ofNat 64 k) 1 = true := by
  have h1 : m.canWrite (esp s₀ + (64#64 + BitVec.ofNat 64 k)) 1 = true :=
    hrw.canWrite_sub (by bv_omega) (by decide)
  refine ⟨h1, ?_⟩
  rw [BitVec.add_assoc]; exact h1

private theorem rw_esp_64_sub {m : Memory} {s₀ : State} {k : ℕ}
    (hrw : m.RW (esp s₀) 496) (hk : k < 23) :
    m.RW (esp s₀ + 64#64) k :=
  hrw.sub (by bv_omega)

theorem agreesOutside_counter_writes {m₁ : Memory} {s₀ : State} {k : ℕ}
    {b1 c b2 : BitVec 8} (hk : k < 63) :
    AgreesOutside m₁
      ((((m₁.write8 (esp s₀ + 127#64) b1).write8
        (esp s₀ + 240#64) c).write8
        (esp s₀ + 64#64 + BitVec.ofNat 64 k) c).write8
        (esp s₀ + 127#64) b2)
      (esp s₀ + 64#64) 177 := by
  refine agreesOutside_esp_write8 ?_ (by decide)
  refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
  refine agreesOutside_esp_write8 ?_ (by decide)
  exact agreesOutside_esp_write8 (AgreesOutside.rfl' _ _ _) (by decide)

/-- Segment 2a (`b + 0x51b0c` → `b + 0x1aa34`, 1 `memcpy` + 13 steps): `memcpy` of `info` at
`esp + 64`, appends counter byte `1#8`, sets `pos = info.length + 1` and `x26 = okmLen - 32`. -/
theorem seg2a_runsTo [HkdfHooks C.F ext] {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀)
    (hx : StateX1 b C.F prk info infoPtr okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateX1b b C.F prk info okmLen s₀) := by
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
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hlr := hx.lr_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hinfo_lt := hpre.info_lt
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 64#64) info.length :=
    rw_esp_64_sub hrw_esp hinfo_lt
  have hread_info : s.mem.readBytes infoPtr info.length = info :=
    ExpandFrame.info_bytes_eq hpre hx.common.frame
  have hx2_nat : (s.readReg64 .x2).toNat = info.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine s2_memcpy_step_ext b C ext hrun hpc hx0 hx1 hx2_nat hlr hread_info hrw_dst ?_
  have hA1 : AgreesOutside s.mem (s.mem.writeBytes (esp s₀ + 64#64) info) (esp s₀ + 64#64) 23 :=
    agreesOutside_writeBytes_le s.mem (esp s₀ + 64#64) info 23 (by omega)
  have hrw_wb : (s.mem.writeBytes (esp s₀ + 64#64) info).RW (esp s₀) 496 :=
    rw_of_perm_eq hA1.2 hrw_esp
  rcases canWrite_esp_64_add hrw_wb (by omega : info.length < 64) with ⟨hcw_pos1, hcw_pos2⟩
  have hze32 := zeroExtend64_truncate32_ofNat64 (by omega : info.length < 64)
  have hand255 := zeroExtend64_and255_truncate32_ofNat64 (by omega : info.length < 64)
  have hand64_255 := and64_255_ofNat64 (by omega : info.length < 64)
  have hand40 := and_0xffffffffff_ofNat64 (by omega : info.length < 64)
  rcases cmp32_lt63_lemmas (by omega : info.length < 63) with ⟨hcmp63_eq, hcmp63_ne, hcmp63_z⟩
  have hadd1 := zeroExtend64_add1_truncate32_ofNat64 (by omega : info.length < 63)
  iterate 13 s2_step
  refine RunsTo.refl ?_
  have hc1 : ExpandCommon okmLen s₀ (s.setMem (s.mem.writeBytes (esp s₀ + 64#64) info)) :=
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
      (by rw [mem_setMem, mem_setMem]; exact agreesOutside_counter_writes (by omega : info.length < 63))
      (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    ?_, ?_⟩
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]
    rcases hpre.okm_len with rfl | rfl <;> rfl
  · rw [mem_setMem]
    exact HmacSt.of_memcpy_counter_64_0 hx.hmac_64 hinfo_lt

/-- Segment 2b (`b + 0x1aa34` → `b + 0x30680`, 13 steps): copies `Hmac` from `esp + 64` to
`esp + 240` and calls `finalize_fixed(esp + 208, esp + 240)`. -/
theorem seg2b_runsTo [HkdfHooks C.F ext] {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀)
    (hx : StateX1b b C.F prk info okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateX2 b C.F prk info okmLen s₀) := by
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
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  iterate 13 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 240#64) (sz := 0x90) hx.common hrun hsp hx29 hx27 hx20
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

/-- `finalize_fixed` #1 (`b + 0x30680` → `b + 0x1aa68`), parameterized by
`(hFin : Fin.FinalizeFixedRunsToExt b C ext)`: produces `T(1) = t1 C.F prk info` at
`esp s₀ + 208#64`. -/
theorem fin1_runsTo (hFin : Fin.FinalizeFixedRunsToExt b C ext)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀)
    (hx : StateX2 b C.F prk info okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateX2r b C.F prk info okmLen s₀) := by
  rcases fin_side_conditions hpre hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hfin_pre : FinalizeFixedProof.FinPre b C.F prk (info ++ [1#8]) s :=
    { pc_eq := hx.pc_eq
      status := hx.common.status
      key_le := hpre.prk_le
      msg_lt := by have := hpre.info_lt; simp; omega
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_240
      rw_out := by rw [hx.x0_eq]; exact hrw_x0
      rw_hm := by rw [hx.x1_eq]; exact hrw_x1
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sp
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; exact hd_x0_x1
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; exact hd_x0_sp
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; exact hd_x1_sp
      sp_aligned := by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned }
  refine (hFin hfin_pre).mono fun s' ⟨hpc', hrun', hcs, ht1, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'
  rw [hx.x0_eq] at ht1
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq] at hfr
  exact ⟨hpc',
    ExpandCommon.of_fin_frame hx.common hrun' hcs hfr,
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans hx.x23_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq,
    ht1⟩

/-- Segment 3 (`b + 0x1aa68` → `b + 0x1ab3c`, 4 steps + `memcpy` + 9 steps): copies `T(1)` (32 B)
from `esp + 208` to `s₀.x2`, caches `T(1)` at `esp + 32..64`, and enters the loop at `0x1ab3c`
with `i = 1`, `rem = okmLen - 32`, `dstOff = 32`. -/
theorem seg3_runsTo [HkdfHooks C.F ext] {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀)
    (hx : StateX2r b C.F prk info okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoop b okmLen (t1 C.F prk info) (t1 C.F prk info) 1 (okmLen - 32) 32 s₀) := by
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
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) okmLen := ExpandFrame.rw_x2 hpre hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2) 32 :=
    hrw_x2.sub (by have := hpre.okm_len; bv_omega)
  iterate 4 s2_step
  refine s2_memcpy_step_ext b C ext hrun rfl rfl rfl rfl rfl hx.t1_208 hrw_dst ?_
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2) (t1 C.F prk info)
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + 0#64) 32 := by
    rw [BitVec.add_zero]
    exact agreesOutside_writeBytes_le s.mem (s₀.readReg64 .x2) (t1 C.F prk info) 32 (by simp)
  have hc1 : ExpandCommon okmLen s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_x2 hpre hx.common hrun hsp hx29 hx27 hx20 hA1
      ⟨by decide, by have := hpre.okm_len; simp; omega⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hc1.frame
  dsimp only [m₁] at hm16_1 hrw1_esp
  have h_rem_ne : (BitVec.ofNat 64 (okmLen - 32) == 0#64) = false := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  iterate 9 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
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
        exact (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2)
          ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ + 208#64)
          ⟨by decide, by unfold esp; bv_omega⟩
      exact (hA1.readBytes_eq hd (by decide)).trans hx.t1_208
    exact readBytes_32_esp_32_of_208 ht1_m1
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
  · have hd : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) 32 :=
      (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64)
        ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
        ⟨by decide, by have := hpre.okm_len; bv_omega⟩
    dsimp only [mem_setMem]
    refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd (by prove_agrees_esp) (by decide) ?_
    conv_lhs => rw [← t1_length C.F prk info]
    exact Bytes.readBytes_writeBytes_same s.mem (s₀.readReg64 .x2) (t1 C.F prk info) (by simp)

end Block1

/-! ## Relocatable `[LibsignalPlacement]` Segment Proofs -/

section Block1Placed

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]

theorem seg0_placed_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀ (StateX0p expPlacedFakeB okmLen s₀) := by
  have hpc := hpre.pc_eq
  have hrun := hpre.status
  have hx3 := hpre.x3_eq
  have hsp_al : (s₀.sp &&& 15#64) = 0#64 := hpre.sp_aligned
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s₀.mem.RW (esp s₀) 496 :=
    ExpandFrame.rw_esp hpre (Frame.refl s₀.mem _)
  iterate 8 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc], hrun,
    by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx3], ?_, ?_⟩
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

theorem seg1_placed_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hx : StateX0p expPlacedFakeB okmLen s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s (StateX1Placed C.F prk info infoPtr okmLen s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.status
  have hsp := hx.sp_eq
  have hx29 := hx.x29_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hx3 := hx.x3_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.frame
  have hread_x0 : s.mem.Readable (s₀.readReg64 .x0) 0x90 := ExpandFrame.readable_x0 hpre hx.frame
  have hread_x1 : s.mem.Readable (s₀.readReg64 .x1) 16 := ExpandFrame.readable_x1 hpre hx.frame
  rcases read64_x0_write64_esp hpre with ⟨h_x0_w0, h_x0_w⟩
  rcases read64_x1_write_esp hpre with ⟨h_x1_w0, h_x1_w8, _, _⟩
  have hx1_val0 : s.mem.read64 (s₀.readReg64 .x1) = infoPtr :=
    ExpandFrame.info_ptr_eq hpre hx.frame
  have hx1_val8 : s.mem.read64 (s₀.readReg64 .x1 + 8#64) = BitVec.ofNat 64 info.length :=
    ExpandFrame.info_len_eq hpre hx.frame
  have hpos_x0 : s.mem.read8 (s₀.readReg64 .x0 + 63#64) = 0#8 :=
    (ExpandFrame.hmac_x0 hpre hx.frame).2.2.1
  have h_okm_ule : BitVec.ule 32#64 (BitVec.ofNat 64 okmLen) = true := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  have h_okm_ult : BitVec.ult (BitVec.ofNat 64 okmLen) 32#64 = false := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  have h_okm_hi : BitVec.ult 32#64 (BitVec.ofNat 64 okmLen) = true := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  have h_okm_ls : BitVec.ule (BitVec.ofNat 64 okmLen) 32#64 = false := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  have h_okm_cmp : (AddWithCarry64 (BitVec.ofNat 64 okmLen) (bv% (2 ^ 64 - 33)) true).2.c = true := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  rcases cmp_lt64_lemmas (by have := hpre.info_lt; omega : info.length < 64) with
    ⟨h_info_ule, h_info_ult, h_info_cmp⟩
  iterate 40 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ⟨hrun, hsp, hx29, rfl, rfl,
     by simp (config := { decide := true }) only [arm64_norm],
     by simp (config := { decide := true }) only [arm64_norm],
     ExpandSaved.of_agreesOutside_low (off := 8#64) (sz := 312) hx.saved (by prove_agrees_esp) (by decide),
     ExpandFrame.of_agreesOutside_esp (off := 8#64) (sz := 312) hx.frame (by prove_agrees_esp) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [mem_setMem]
  exact HmacSt.of_copy_empty_esp_64 (ExpandFrame.hmac_x0 hpre hx.frame)
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

theorem seg2a_placed_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hx : StateX1Placed C.F prk info infoPtr okmLen s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s (StateX1b expPlacedFakeB C.F prk info okmLen s₀) := by
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
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hlr := hx.lr_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hinfo_lt := hpre.info_lt
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 64#64) info.length :=
    rw_esp_64_sub hrw_esp hinfo_lt
  have hread_info : s.mem.readBytes infoPtr info.length = info :=
    ExpandFrame.info_bytes_eq hpre hx.common.frame
  have hx2_nat : (s.readReg64 .x2).toNat = info.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine s2_memcpy_step_placed C H hrun hpc hx0 hx1 hx2_nat hlr hread_info hrw_dst ?_
  have hA1 : AgreesOutside s.mem (s.mem.writeBytes (esp s₀ + 64#64) info) (esp s₀ + 64#64) 23 :=
    agreesOutside_writeBytes_le s.mem (esp s₀ + 64#64) info 23 (by omega)
  have hrw_wb : (s.mem.writeBytes (esp s₀ + 64#64) info).RW (esp s₀) 496 :=
    rw_of_perm_eq hA1.2 hrw_esp
  rcases canWrite_esp_64_add hrw_wb (by omega : info.length < 64) with ⟨hcw_pos1, hcw_pos2⟩
  have hze32 := zeroExtend64_truncate32_ofNat64 (by omega : info.length < 64)
  have hand255 := zeroExtend64_and255_truncate32_ofNat64 (by omega : info.length < 64)
  have hand64_255 := and64_255_ofNat64 (by omega : info.length < 64)
  have hand40 := and_0xffffffffff_ofNat64 (by omega : info.length < 64)
  rcases cmp32_lt63_lemmas (by omega : info.length < 63) with ⟨hcmp63_eq, hcmp63_ne, hcmp63_z⟩
  have hadd1 := zeroExtend64_add1_truncate32_ofNat64 (by omega : info.length < 63)
  iterate 13 s2_step
  refine RunsTo.refl ?_
  have hc1 : ExpandCommon okmLen s₀ (s.setMem (s.mem.writeBytes (esp s₀ + 64#64) info)) :=
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
      (by rw [mem_setMem, mem_setMem]; exact agreesOutside_counter_writes (by omega : info.length < 63))
      (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    ?_, ?_⟩
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]
    rcases hpre.okm_len with rfl | rfl <;> rfl
  · rw [mem_setMem]
    exact HmacSt.of_memcpy_counter_64_0 hx.hmac_64 hinfo_lt

theorem seg2b_placed_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hx : StateX1b expPlacedFakeB C.F prk info okmLen s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s (StateX2Placed C.F prk info okmLen s₀) := by
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
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  iterate 13 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 240#64) (sz := 0x90) hx.common hrun hsp hx29 hx27 hx20
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

theorem fin1_placed_runsTo
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hFin : ∀ {key msg : List (BitVec 8)} {s : State},
      ExpandFrame okmLen s₀ s.mem →
      FinalizeFixedProof.FinPre finPlacedFakeB C.F key msg s →
      RunsTo ((blkPC_53).rebase (blkPl_53).base H) s (FinalizeFixedProof.FinPost C.F key msg s))
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hx : StateX2Placed C.F prk info okmLen s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s (StateX2r expPlacedFakeB C.F prk info okmLen s₀) := by
  rcases fin_side_conditions hpre hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hfin_pre : FinalizeFixedProof.FinPre finPlacedFakeB C.F prk (info ++ [1#8]) s :=
    { pc_eq := by rw [hx.pc_eq]; simp only [arm64_norm]
      status := hx.common.status
      key_le := hpre.prk_le
      msg_lt := by have := hpre.info_lt; simp; omega
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_240
      rw_out := by rw [hx.x0_eq]; exact hrw_x0
      rw_hm := by rw [hx.x1_eq]; exact hrw_x1
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sp
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; exact hd_x0_x1
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; exact hd_x0_sp
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; exact hd_x1_sp
      sp_aligned := by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned }
  refine (hFin hx.common.frame hfin_pre).mono
    fun s' ⟨hpc', hrun', hcs, ht1, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'
  rw [hx.x0_eq] at ht1
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq] at hfr
  exact ⟨by simp only [arm64_norm, hpc'],
    ExpandCommon.of_fin_frame hx.common hrun' hcs hfr,
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans hx.x23_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq,
    ht1⟩

theorem seg3_placed_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hx : StateX2r expPlacedFakeB C.F prk info okmLen s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoop expPlacedFakeB okmLen (t1 C.F prk info) (t1 C.F prk info) 1 (okmLen - 32) 32 s₀) := by
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
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) okmLen := ExpandFrame.rw_x2 hpre hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2) 32 :=
    hrw_x2.sub (by have := hpre.okm_len; bv_omega)
  iterate 4 s2_step
  refine s2_memcpy_step_placed C H hrun rfl rfl rfl rfl rfl hx.t1_208 hrw_dst ?_
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2) (t1 C.F prk info)
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + 0#64) 32 := by
    rw [BitVec.add_zero]
    exact agreesOutside_writeBytes_le s.mem (s₀.readReg64 .x2) (t1 C.F prk info) 32 (by simp)
  have hc1 : ExpandCommon okmLen s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_x2 hpre hx.common hrun hsp hx29 hx27 hx20 hA1
      ⟨by decide, by have := hpre.okm_len; simp; omega⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hc1.frame
  dsimp only [m₁] at hm16_1 hrw1_esp
  have h_rem_ne : (BitVec.ofNat 64 (okmLen - 32) == 0#64) = false := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
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
        exact (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2)
          ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ + 208#64)
          ⟨by decide, by unfold esp; bv_omega⟩
      exact (hA1.readBytes_eq hd (by decide)).trans hx.t1_208
    exact readBytes_32_esp_32_of_208 ht1_m1
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
  · have hd : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) 32 :=
      (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64)
        ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
        ⟨by decide, by have := hpre.okm_len; bv_omega⟩
    dsimp only [mem_setMem]
    refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd (by prove_agrees_esp) (by decide) ?_
    conv_lhs => rw [← t1_length C.F prk info]
    exact Bytes.readBytes_writeBytes_same s.mem (s₀.readReg64 .x2) (t1 C.F prk info) (by simp)

end Block1Placed
end Expand
end CryptoVerification.LibsignalTripleRatchet
