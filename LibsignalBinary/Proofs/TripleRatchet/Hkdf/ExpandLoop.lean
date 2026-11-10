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
# Loop Iteration and Epilogue Proofs for `expand_multi_info`

Proves the per-iteration `RunsTo` segments `iter_a1_runsTo` through `iter_d_done_runsTo`
and `epilogue_runsTo` for `GenericHkdf<Hmac<Sha256>>::expand_multi_info`.
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

section Loop

variable {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
  {abs ext : String → Option (State → State)}

/-- Loop cut `A1` at `b + 0x1aba4` (after 26 steps from `0x1ab3c`): fresh `Hmac` copied to
`esp + 64` and `x23 = min rem 32`. -/
structure StateLoopA1 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 816)
  common  : ExpandCommon okmLen s₀ s
  x8_eq   : s.readReg64 .x8 = 0#64
  x19_eq  : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 (min rem 32)
  x24_eq  : s.readReg64 .x24 = 64#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x28_eq  : s.readReg64 .x28 = esp s₀ + 64#64
  hmac_64 : HmacSt s.mem (esp s₀ + 64#64) F prk []
  t_cache : s.mem.readBytes (esp s₀ + 32#64) 32 = tPrev
  okm_pre : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Loop cut `A2` at `b + 0x47f50` (after 17 steps from `0x1aba4`): `tPrev` (32 B) copied to
`esp + 64..96`, `pos = 32`, and `memcpy(esp + 96, infoPtr, info.length)` set up. -/
structure StateLoopA2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (tPrev okmSoFar : List (BitVec 8))
    (okmLen i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "memcpy")
  common  : ExpandCommon okmLen s₀ s
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 1124)
  x0_eq   : s.readReg64 .x0 = esp s₀ + 96#64
  x1_eq   : s.readReg64 .x1 = infoPtr
  x2_eq   : s.readReg64 .x2 = BitVec.ofNat 64 info.length
  x19_eq  : s.readReg64 .x19 = BitVec.ofNat 64 i
  x21_eq  : s.readReg64 .x21 = 32#64
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 (min rem 32)
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x28_eq  : s.readReg64 .x28 = esp s₀ + 64#64
  hmac_64 : HmacSt s.mem (esp s₀ + 64#64) F prk tPrev
  okm_pre : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Loop cut `B` at `b + 0x1aad0` (after `memcpy` + 14 steps): `info` and counter byte `(i + 1)#8`
appended to `Hmac` at `esp + 64`. -/
structure StateLoopB (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 604)
  common  : ExpandCommon okmLen s₀ s
  x19_eq  : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 (min rem 32)
  x24_eq  : s.readReg64 .x24 = 64#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x28_eq  : s.readReg64 .x28 = esp s₀ + 64#64
  hmac_64 : HmacSt s.mem (esp s₀ + 64#64) F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Loop cut `C` at `b + 0x30680` (after 17 steps from `0x1aad0`): `Hmac` copied from `esp + 64`
to `esp + 240` and `finalize_fixed(esp + 208, esp + 240)` called. -/
structure StateLoopC (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]")
  common   : ExpandCommon okmLen s₀ s
  lr_eq    : s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 672)
  x0_eq    : s.readReg64 .x0 = esp s₀ + 208#64
  x1_eq    : s.readReg64 .x1 = esp s₀ + 240#64
  x19_eq   : s.readReg64 .x19 = BitVec.ofNat 64 i
  x21_eq   : s.readReg64 .x21 = s₀.readReg64 .x2 + BitVec.ofNat 64 (dstOff + min rem 32)
  x22_eq   : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq   : s.readReg64 .x23 = BitVec.ofNat 64 (min rem 32)
  x24_eq   : s.readReg64 .x24 = 64#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 (rem - min rem 32)
  x28_eq   : s.readReg64 .x28 = esp s₀ + 64#64
  hmac_240 : HmacSt s.mem (esp s₀ + 240#64) F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre  : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Loop cut `Fin` at `b + 0x1ab14` (after `finalize_fixed` returns): `T(i+1)` is at `esp + 208`. -/
structure StateLoopFin (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 672)
  common  : ExpandCommon okmLen s₀ s
  x19_eq  : s.readReg64 .x19 = BitVec.ofNat 64 i
  x21_eq  : s.readReg64 .x21 = s₀.readReg64 .x2 + BitVec.ofNat 64 (dstOff + min rem 32)
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 (min rem 32)
  x24_eq  : s.readReg64 .x24 = 64#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 (rem - min rem 32)
  x28_eq  : s.readReg64 .x28 = esp s₀ + 64#64
  t_208   : s.mem.readBytes (esp s₀ + 208#64) 32 =
              hmacWith F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

theorem iter_a1_runsTo [HkdfHooks C.F ext] {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀)
    (hrem : rem = 32 ∨ rem = 48 ∨ rem = 16)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoop b okmLen tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopA1 b C.F prk tPrev okmSoFar okmLen i rem dstOff s₀) := by
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
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  have hread_x0 : s.mem.Readable (s₀.readReg64 .x0) 0x90 :=
    ExpandFrame.readable_x0 hpre hx.common.frame
  rcases read64_x0_write64_esp hpre with ⟨h_x0_w0, h_x0_w⟩
  have hpos_x0 : s.mem.read8 (s₀.readReg64 .x0 + 63#64) = 0#8 :=
    (ExpandFrame.hmac_x0 hpre hx.common.frame).2.2.1
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
    rcases hrem with rfl | rfl | rfl <;> rfl
  · simp only [mem_setMem]
    exact HmacSt.of_copy_empty_esp_64 (ExpandFrame.hmac_x0 hpre hx.common.frame)
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
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 256 hd (by prove_agrees_esp)
        (by have := hpre.okm_len; omega) hx.okm_pre

theorem iter_a2_runsTo [HkdfHooks C.F ext] {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA1 b C.F prk tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopA2 b C.F prk info infoPtr tPrev okmSoFar okmLen i rem dstOff s₀) := by
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
  have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  have hread_x1 : s.mem.Readable (s₀.readReg64 .x1) 16 :=
    ExpandFrame.readable_x1 hpre hx.common.frame
  rcases read64_x1_write_esp hpre with ⟨h_x1_w0, h_x1_w8, h_x1_w8_0, h_x1_w8_8⟩
  have hx1_val0 : s.mem.read64 (s₀.readReg64 .x1) = infoPtr :=
    ExpandFrame.info_ptr_eq hpre hx.common.frame
  have hx1_val8 : s.mem.read64 (s₀.readReg64 .x1 + 8#64) = BitVec.ofNat 64 info.length :=
    ExpandFrame.info_len_eq hpre hx.common.frame
  rcases cmp_lt32_lemmas (by have := hpre.info_lt; omega : info.length < 32) with
    ⟨h_info_ule32, h_info_ult32, h_info_cmp32⟩
  iterate 17 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 64) hx.common hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl, rfl, hx19, rfl, hx22, hx23, rfl, hx26, rfl, ?_, ?_⟩
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
    · have hd : DisjointRegions (esp s₀ + 64#64) 64 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 64 hd (by prove_agrees_esp)
        (by have := hpre.okm_len; omega) hx.okm_pre

private theorem HmacSt.of_memcpy_counter_64_32 {m₀ : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key tPrev info : List (BitVec 8)} {i : ℕ}
    (h₀ : HmacSt m₀ (esp s₀ + 64#64) F key tPrev)
    (ht : tPrev.length = 32)
    (hinfo : info.length < 23) :
    HmacSt (((((m₀.writeBytes (esp s₀ + 96#64) info).write8
      (esp s₀ + 127#64) (BitVec.ofNat 8 (32 + info.length))).write8
      (esp s₀ + 240#64) (BitVec.ofNat 8 (i + 1))).write8
      (esp s₀ + 64#64 + BitVec.ofNat 64 (32 + info.length)) (BitVec.ofNat 8 (i + 1))).write8
      (esp s₀ + 127#64) (BitVec.ofNat 8 (32 + info.length + 1)))
      (esp s₀ + 64#64) F key (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) := by
  have hm := HmacSt.of_memcpy_counter h₀ (by omega) hinfo
    (b1 := BitVec.ofNat 8 (32 + info.length)) (c := BitVec.ofNat 8 (i + 1))
  dsimp only [] at hm
  have h96 : esp s₀ + 64#64 + BitVec.ofNat 64 tPrev.length = esp s₀ + 96#64 := by
    rw [ht]; bv_lin
  have h127 : esp s₀ + 64#64 + 63#64 = esp s₀ + 127#64 := by bv_lin
  have h240 : esp s₀ + 64#64 + 176#64 = esp s₀ + 240#64 := by bv_lin
  have hpos : esp s₀ + 64#64 + BitVec.ofNat 64 (tPrev.length + info.length) =
      esp s₀ + 64#64 + BitVec.ofNat 64 (32 + info.length) := by
    rw [ht]
  have hlen1 : tPrev.length + info.length + 1 = 32 + info.length + 1 := by omega
  rw [h96, h127, h240, hpos, hlen1] at hm
  exact hm

private theorem canWrite_esp_64_add {m : Memory} {s₀ : State} {k : ℕ}
    (hrw : m.RW (esp s₀) 496) (hk : k < 64) :
    m.canWrite (esp s₀ + (64#64 + BitVec.ofNat 64 k)) 1 = true ∧
    m.canWrite (esp s₀ + 64#64 + BitVec.ofNat 64 k) 1 = true := by
  have h1 : m.canWrite (esp s₀ + (64#64 + BitVec.ofNat 64 k)) 1 = true :=
    hrw.canWrite_sub (by bv_omega) (by decide)
  refine ⟨h1, ?_⟩
  rw [BitVec.add_assoc]; exact h1

private theorem rw_esp_96_sub {m : Memory} {s₀ : State} {k : ℕ}
    (hrw : m.RW (esp s₀) 496) (hk : k < 23) :
    m.RW (esp s₀ + 96#64) k :=
  hrw.sub (by bv_omega)

private theorem agreesOutside_counter_writes {m₁ : Memory} {s₀ : State} {k : ℕ}
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

private theorem disj_esp_x2_sub_96_64 {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen dstOff : ℕ} {s₀ : State}
    (hpre : ExpandPre b F prk info infoPtr okmLen s₀)
    (h0 : dstOff ≠ 0) (hdst : dstOff ≤ okmLen) :
    DisjointRegions (esp s₀ + 64#64) 177 (s₀.readReg64 .x2) dstOff ∧
    DisjointRegions (esp s₀ + 96#64) 23 (s₀.readReg64 .x2) dstOff :=
  ⟨(hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
     ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
     ⟨by omega, by have := hpre.okm_len; bv_omega⟩,
   (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 96#64)
     ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
     ⟨by omega, by have := hpre.okm_len; bv_omega⟩⟩

theorem iter_b_runsTo [HkdfHooks C.F ext] {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA2 b C.F prk info infoPtr tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopB b C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx25 := hx.x25_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hlr := hx.lr_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hinfo_lt := hpre.info_lt
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 96#64) info.length :=
    rw_esp_96_sub hrw_esp hinfo_lt
  have hread_info : s.mem.readBytes infoPtr info.length = info :=
    ExpandFrame.info_bytes_eq hpre hx.common.frame
  have hx2_nat : (s.readReg64 .x2).toNat = info.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine s2_memcpy_step_ext b C ext hrun hpc hx0 hx1 hx2_nat hlr hread_info hrw_dst ?_
  let m₁ := s.mem.writeBytes (esp s₀ + 96#64) info
  have hA1 : AgreesOutside s.mem m₁ (esp s₀ + 96#64) 23 :=
    agreesOutside_writeBytes_le s.mem (esp s₀ + 96#64) info 23 (by omega)
  have hrw_wb : m₁.RW (esp s₀) 496 :=
    rw_of_perm_eq hA1.2 hrw_esp
  rcases canWrite_esp_64_add hrw_wb (by omega : 32 + info.length < 64) with ⟨hcw_pos1, hcw_pos2⟩
  dsimp only [m₁] at hrw_wb hcw_pos1 hcw_pos2
  have hadd32 := zeroExtend64_add32_truncate32_ofNat64 (by omega : info.length < 32)
  have hand255 := zeroExtend64_and255_truncate32_ofNat64 (by omega : 32 + info.length < 64)
  have hand64_255 := and64_255_ofNat64 (by omega : 32 + info.length < 64)
  have hze8_32 := zeroExtend32_ofNat8_eq_truncate32 (by omega : 32 + info.length < 64)
  have hze8_64 := zeroExtend64_ofNat8 (by omega : 32 + info.length < 64)
  have hi1_ze := zeroExtend64_truncate32_ofNat64 (by omega : i + 1 < 64)
  rcases cmp32_lt63_lemmas (by omega : 32 + info.length < 63) with ⟨hcmp63_eq, hcmp63_ne, hcmp63_z⟩
  have hadd1 := zeroExtend64_add1_truncate32_ofNat64 (by omega : 32 + info.length < 63)
  have hi_eq : (BitVec.ofNat 64 i == 255#64) = false := by rcases hi with rfl | rfl <;> rfl
  have hi_ne : (BitVec.ofNat 64 i != 255#64) = true := by rcases hi with rfl | rfl <;> rfl
  have hi_cmp : (AddWithCarry64 (BitVec.ofNat 64 i) (bv% (2 ^ 64 - 256)) true).2.z = false := by
    rcases hi with rfl | rfl <;> rfl
  have hi_add1 : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 i) + 1#32) =
      BitVec.ofNat 64 (i + 1) := by
    rcases hi with rfl | rfl <;> rfl
  iterate 14 s2_step
  refine RunsTo.refl ?_
  have hc1 : ExpandCommon okmLen s₀ (s.setMem (s.mem.writeBytes (esp s₀ + 96#64) info)) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  have hA2 := agreesOutside_counter_writes (m₁ := m₁) (s₀ := s₀)
    (b1 := BitVec.ofNat 8 (32 + info.length)) (c := BitVec.ofNat 8 (i + 1))
    (b2 := BitVec.ofNat 8 (32 + info.length + 1)) (by omega : 32 + info.length < 63)
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 177) hc1
      (by rw [State.status_setMem]; simp only [arm64_norm, hrun])
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by rw [mem_setMem, mem_setMem, zeroExtend64_truncate32_ofNat64 (by omega : 32 + info.length < 64)]; exact hA2)
      (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx19],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_⟩
  · rw [mem_setMem, zeroExtend64_truncate32_ofNat64 (by omega : 32 + info.length < 64)]
    exact HmacSt.of_memcpy_counter_64_32 hx.hmac_64 ht_len hinfo_lt
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · rcases disj_esp_x2_sub_96_64 hpre h0 hdst with ⟨hd2, hd1⟩
      rw [mem_setMem, zeroExtend64_truncate32_ofNat64 (by omega : 32 + info.length < 64)]
      refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 64#64 177 hd2 hA2
        (by have := hpre.okm_len; omega) ?_
      exact (hA1.readBytes_eq hd1 (by have := hpre.okm_len; omega)).trans hx.okm_pre

theorem iter_c_runsTo [HkdfHooks C.F ext] {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀)
    (hrem : rem = 32 ∨ rem = 48 ∨ rem = 16)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopB b C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopC b C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀) := by
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
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  iterate 17 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 240#64) (sz := 0x90) hx.common hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl, hx19, ?_, hx22, hx23, hx24, ?_, hx28, ?_, ?_⟩
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]
    rcases hrem with rfl | rfl | rfl <;> rfl
  · simp only [mem_setMem]
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
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd : DisjointRegions (esp s₀ + 240#64) 0x90 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 240#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 240#64 0x90 hd (by prove_agrees_esp)
        (by have := hpre.okm_len; omega) hx.okm_pre

theorem iter_fin_runsTo (hFin : Fin.FinalizeFixedRunsToExt b C ext)
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopC b C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopFin b C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀) := by
  rcases fin_side_conditions hpre hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hfin_pre : FinalizeFixedProof.FinPre b C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) s :=
    { pc_eq := hx.pc_eq
      status := hx.common.status
      key_le := hpre.prk_le
      msg_lt := by have := hpre.info_lt; simp [ht_len]; omega
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_240
      rw_out := by rw [hx.x0_eq]; exact hrw_x0
      rw_hm := by rw [hx.x1_eq]; exact hrw_x1
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sp
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; exact hd_x0_x1
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; exact hd_x0_sp
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; exact hd_x1_sp
      sp_aligned := by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned }
  refine (hFin hfin_pre).mono fun s' ⟨hpc', hrun', hcs, ht, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'
  rw [hx.x0_eq] at ht
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq] at hfr
  have hokm' : s'.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · refine (Frame.readBytes_eq hfr (fun r hr => ?_) (by have := hpre.okm_len; omega)).trans hx.okm_pre
      have hd_stk : DisjointRegions (s₀.sp - 640#64) 640 (s₀.readReg64 .x2) dstOff :=
        hpre.disj_x2_stack.symm.sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact hd_stk.sub_left _ ⟨by simp, by unfold esp; bv_omega⟩
  exact ⟨hpc',
    ExpandCommon.of_fin_frame hx.common hrun' hcs hfr,
    (CalleeSaved.x19 hcs).trans hx.x19_eq,
    (CalleeSaved.x21 hcs).trans hx.x21_eq,
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans hx.x23_eq,
    (CalleeSaved.x24 hcs).trans hx.x24_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq,
    (CalleeSaved.x28 hcs).trans hx.x28_eq,
    ht, hokm'⟩

/-- Loop tail (`b + 0x1ab14` → `b + 0x1ab3c` when `rem = 48`): copies 32 bytes of `tNext` to
`s₀.x2 + dstOff`, caches `tNext` at `esp + 32`, and branches back to `0x1ab3c` with `rem' = 16`. -/
theorem iter_d_continue_runsTo [HkdfHooks C.F ext] {prk info tPrev okmSoFar tNext : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀)
    (hi : i = 1)
    (hdst : dstOff + 32 ≤ okmLen)
    (htNext : tNext = hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]))
    (hx : StateLoopFin b C.F prk info tPrev okmSoFar okmLen i 48 dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoop b okmLen tNext (okmSoFar ++ tNext) (i + 1) 16 (dstOff + 32) s₀) := by
  subst hi
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
  have hx26 : s.readReg64 .x26 = 16#64 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) okmLen := ExpandFrame.rw_x2 hpre hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 :=
    hrw_x2.sub (by have := hpre.okm_len; bv_omega)
  iterate 4 s2_step
  refine s2_memcpy_step_ext b C ext hrun rfl rfl rfl rfl rfl ht_208 hrw_dst ?_
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) tNext
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 :=
    agreesOutside_writeBytes_le s.mem _ tNext 32 (by omega)
  have hc1 : ExpandCommon okmLen s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_x2 hpre hx.common hrun hsp hx29 hx27 hx20 hA1
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hc1.frame
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
    ?_,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx24],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_⟩
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]; rfl
  · simp only [mem_setMem]
    have ht_m1 : m₁.readBytes (esp s₀ + 208#64) 32 = tNext := by
      have hd : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 (esp s₀ + 208#64) 32 :=
        (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
          ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ + 208#64)
          ⟨by decide, by unfold esp; bv_omega⟩
      exact (hA1.readBytes_eq hd (by decide)).trans ht_208
    exact readBytes_32_esp_32_of_208 ht_m1
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
  · have hd2 : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) (dstOff + 32) :=
      (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64)
        ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
        ⟨by omega, by have := hpre.okm_len; bv_omega⟩
    dsimp only [mem_setMem]
    refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd2 (by prove_agrees_esp)
      (by have := hpre.okm_len; omega) ?_
    rw [Bytes.readBytes_add m₁ (s₀.readReg64 .x2) dstOff 32]
    have hleft : m₁.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
      by_cases h0 : dstOff = 0
      · subst h0; exact hx.okm_pre
      · have hd1 : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 (s₀.readReg64 .x2) dstOff := by
          unfold DisjointRegions; have := hpre.okm_len; bv_omega
        exact (hA1.readBytes_eq hd1 (by have := hpre.okm_len; omega)).trans hx.okm_pre
    have hright : m₁.readBytes (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 = tNext := by
      conv_lhs => rw [← ht_len]
      exact Bytes.readBytes_writeBytes_same s.mem _ tNext (by omega)
    rw [hleft, hright]

/-- Loop tail (`b + 0x1ab14` → `b + 0x1ad0c` when `rem ≤ 32`): copies `rem` bytes of `tNext` to
`s₀.x2 + dstOff`, caches `tNext` at `esp + 32`, and branches to the epilogue at `0x1ad0c`. -/
theorem iter_d_done_runsTo [HkdfHooks C.F ext] {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 32 ∨ rem = 16)
    (hdst : dstOff + rem = okmLen)
    (hokm : okmSoFar ++ (hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])).take rem =
              hkdfExpand C.F prk info okmLen)
    (hx : StateLoopFin b C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateDone b C.F prk info okmLen s₀) := by
  let tNext := hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])
  have hmin : min rem 32 = rem := by rcases hrem with rfl | rfl <;> rfl
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq
  have hx23 : s.readReg64 .x23 = BitVec.ofNat 64 rem := by rw [hx.x23_eq, hmin]
  have hx24 := hx.x24_eq
  have hx26 : s.readReg64 .x26 = 0#64 := by
    have h := hx.x26_eq; rw [hmin, Nat.sub_self] at h; exact h
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) okmLen := ExpandFrame.rw_x2 hpre hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem :=
    hrw_x2.sub (by have := hpre.okm_len; bv_omega)
  have hread_rem : s.mem.readBytes (esp s₀ + 208#64) rem = tNext.take rem := by
    have hslice := Bytes.readBytes_slice_of_readBytes_eq s.mem (esp s₀ + 208#64) tNext
      (by rw [length_hmacWith]; exact hx.t_208) 0 rem (by rw [length_hmacWith]; omega)
    simpa using hslice
  iterate 4 s2_step
  have hx2_nat : (BitVec.ofNat 64 rem).toNat = rem := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine s2_memcpy_step_ext b C ext hrun rfl rfl rfl hx2_nat rfl hread_rem hrw_dst ?_
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) (tNext.take rem)
  have htake_len : (tNext.take rem).length = rem := by
    rw [List.length_take, length_hmacWith]; omega
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem :=
    agreesOutside_writeBytes_le s.mem _ (tNext.take rem) rem (by omega)
  have hc1 : ExpandCommon okmLen s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_x2 hpre hx.common hrun hsp hx29 hx27 hx20 hA1
      ⟨by omega, by have := hpre.okm_len; bv_omega⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hc1.frame
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
  have hd2 : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) okmLen :=
    hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64) ⟨by decide, by unfold esp; bv_omega⟩
  dsimp only [mem_setMem]
  refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd2 (by prove_agrees_esp)
    (by have := hpre.okm_len; omega) ?_
  rw [← hdst, Bytes.readBytes_add m₁ (s₀.readReg64 .x2) dstOff rem]
  have hleft : m₁.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd1 : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem (s₀.readReg64 .x2) dstOff := by
        unfold DisjointRegions; have := hpre.okm_len; bv_omega
      exact (hA1.readBytes_eq hd1 (by have := hpre.okm_len; omega)).trans hx.okm_pre
  have hright : m₁.readBytes (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem = tNext.take rem := by
    conv_lhs => rw [← htake_len]
    exact Bytes.readBytes_writeBytes_same s.mem _ (tNext.take rem) (by omega)
  rw [hleft, hright, hokm, hdst]

/-- Full loop body for one iteration up to `StateLoopFin` (`0x1ab3c` → `0x1ab14`), parameterized
by `(hFin : Fin.FinalizeFixedRunsToExt b C ext)`. -/
theorem iter_to_fin_runsTo [HkdfHooks C.F ext] (hFin : Fin.FinalizeFixedRunsToExt b C ext)
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 32 ∨ rem = 48 ∨ rem = 16)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoop b okmLen tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopFin b C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀) := by
  refine (iter_a1_runsTo hpre hrem hdst hx).trans fun s1 hs1 => ?_
  refine (iter_a2_runsTo hpre ht_len hdst hs1).trans fun s2 hs2 => ?_
  refine (iter_b_runsTo hpre ht_len hi hdst hs2).trans fun s3 hs3 => ?_
  refine (iter_c_runsTo hpre hrem hdst hs3).trans fun s4 hs4 => ?_
  exact iter_fin_runsTo hFin hpre ht_len hdst hs4

/-- Epilogue (`b + 0x1ad0c` → `s₀.readReg64 .lr`, 8 steps): restores `x19..x30` and `sp = s₀.sp`,
and returns. -/
theorem epilogue_runsTo [HkdfHooks C.F ext] {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀)
    (hx : StateDone b C.F prk info okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (ExpandPost C.F prk info okmLen s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  rcases hx.common.saved with ⟨m400, m408, m416, m424, m432, m440, m448, m456, m464, m472, m480, m488⟩
  iterate 8 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl, hrun, ⟨(esp_eq_add s₀).symm, ?_⟩, hx.okm_all, hx.common.frame⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end Loop

/-! ## Relocatable `[LibsignalPlacement]` Loop and Epilogue Proofs -/

section LoopPlaced

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]

/-- Relocatable loop cut `A2` at `lsρ lsMemcpySym` (after 17 steps from `0x1aba4`). -/
structure StateLoopA2Placed (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (tPrev okmSoFar : List (BitVec 8))
    (okmLen i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = lsρ lsMemcpySym
  common  : ExpandCommon okmLen s₀ s
  lr_eq   : s.readReg64 .lr = (blkPl_53).base + 1124#64
  x0_eq   : s.readReg64 .x0 = esp s₀ + 96#64
  x1_eq   : s.readReg64 .x1 = infoPtr
  x2_eq   : s.readReg64 .x2 = BitVec.ofNat 64 info.length
  x19_eq  : s.readReg64 .x19 = BitVec.ofNat 64 i
  x21_eq  : s.readReg64 .x21 = 32#64
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 (min rem 32)
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x28_eq  : s.readReg64 .x28 = esp s₀ + 64#64
  hmac_64 : HmacSt s.mem (esp s₀ + 64#64) F prk tPrev
  okm_pre : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Relocatable loop cut `C` at `(blkPl_123).base` (after 17 steps from `0x1aad0`). -/
structure StateLoopCPlaced (F : ShaState → List (BitVec 8) → ShaState)
    (prk info tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq    : s.pc = (blkPl_123).base
  common   : ExpandCommon okmLen s₀ s
  lr_eq    : s.readReg64 .lr = (blkPl_53).base + 672#64
  x0_eq    : s.readReg64 .x0 = esp s₀ + 208#64
  x1_eq    : s.readReg64 .x1 = esp s₀ + 240#64
  x19_eq   : s.readReg64 .x19 = BitVec.ofNat 64 i
  x21_eq   : s.readReg64 .x21 = s₀.readReg64 .x2 + BitVec.ofNat 64 (dstOff + min rem 32)
  x22_eq   : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq   : s.readReg64 .x23 = BitVec.ofNat 64 (min rem 32)
  x24_eq   : s.readReg64 .x24 = 64#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 (rem - min rem 32)
  x28_eq   : s.readReg64 .x28 = esp s₀ + 64#64
  hmac_240 : HmacSt s.mem (esp s₀ + 240#64) F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre  : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

theorem iter_a1_placed_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hrem : rem = 32 ∨ rem = 48 ∨ rem = 16)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoop expPlacedFakeB okmLen tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopA1 expPlacedFakeB C.F prk tPrev okmSoFar okmLen i rem dstOff s₀) := by
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
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  have hread_x0 : s.mem.Readable (s₀.readReg64 .x0) 0x90 :=
    ExpandFrame.readable_x0 hpre hx.common.frame
  rcases read64_x0_write64_esp hpre with ⟨h_x0_w0, h_x0_w⟩
  have hpos_x0 : s.mem.read8 (s₀.readReg64 .x0 + 63#64) = 0#8 :=
    (ExpandFrame.hmac_x0 hpre hx.common.frame).2.2.1
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
    rcases hrem with rfl | rfl | rfl <;> rfl
  · simp only [mem_setMem]
    exact HmacSt.of_copy_empty_esp_64 (ExpandFrame.hmac_x0 hpre hx.common.frame)
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
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 256 hd (by prove_agrees_esp)
        (by have := hpre.okm_len; omega) hx.okm_pre

theorem iter_a2_placed_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA1 expPlacedFakeB C.F prk tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopA2Placed C.F prk info infoPtr tPrev okmSoFar okmLen i rem dstOff s₀) := by
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
  have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  have hread_x1 : s.mem.Readable (s₀.readReg64 .x1) 16 :=
    ExpandFrame.readable_x1 hpre hx.common.frame
  rcases read64_x1_write_esp hpre with ⟨h_x1_w0, h_x1_w8, h_x1_w8_0, h_x1_w8_8⟩
  have hx1_val0 : s.mem.read64 (s₀.readReg64 .x1) = infoPtr :=
    ExpandFrame.info_ptr_eq hpre hx.common.frame
  have hx1_val8 : s.mem.read64 (s₀.readReg64 .x1 + 8#64) = BitVec.ofNat 64 info.length :=
    ExpandFrame.info_len_eq hpre hx.common.frame
  rcases cmp_lt32_lemmas (by have := hpre.info_lt; omega : info.length < 32) with
    ⟨h_info_ule32, h_info_ult32, h_info_cmp32⟩
  iterate 17 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 64) hx.common hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl, rfl, hx19, rfl, hx22, hx23, rfl, hx26, rfl, ?_, ?_⟩
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
    · have hd : DisjointRegions (esp s₀ + 64#64) 64 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 64 hd (by prove_agrees_esp)
        (by have := hpre.okm_len; omega) hx.okm_pre

theorem iter_b_placed_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA2Placed C.F prk info infoPtr tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopB expPlacedFakeB C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx25 := hx.x25_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hlr := hx.lr_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hinfo_lt := hpre.info_lt
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 96#64) info.length :=
    rw_esp_96_sub hrw_esp hinfo_lt
  have hread_info : s.mem.readBytes infoPtr info.length = info :=
    ExpandFrame.info_bytes_eq hpre hx.common.frame
  have hx2_nat : (s.readReg64 .x2).toNat = info.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine s2_memcpy_step_placed C H hrun hpc hx0 hx1 hx2_nat hlr hread_info hrw_dst ?_
  let m₁ := s.mem.writeBytes (esp s₀ + 96#64) info
  have hA1 : AgreesOutside s.mem m₁ (esp s₀ + 96#64) 23 :=
    agreesOutside_writeBytes_le s.mem (esp s₀ + 96#64) info 23 (by omega)
  have hrw_wb : m₁.RW (esp s₀) 496 :=
    rw_of_perm_eq hA1.2 hrw_esp
  rcases canWrite_esp_64_add hrw_wb (by omega : 32 + info.length < 64) with ⟨hcw_pos1, hcw_pos2⟩
  dsimp only [m₁] at hrw_wb hcw_pos1 hcw_pos2
  have hadd32 := zeroExtend64_add32_truncate32_ofNat64 (by omega : info.length < 32)
  have hand255 := zeroExtend64_and255_truncate32_ofNat64 (by omega : 32 + info.length < 64)
  have hand64_255 := and64_255_ofNat64 (by omega : 32 + info.length < 64)
  have hze8_32 := zeroExtend32_ofNat8_eq_truncate32 (by omega : 32 + info.length < 64)
  have hze8_64 := zeroExtend64_ofNat8 (by omega : 32 + info.length < 64)
  have hi1_ze := zeroExtend64_truncate32_ofNat64 (by omega : i + 1 < 64)
  rcases cmp32_lt63_lemmas (by omega : 32 + info.length < 63) with ⟨hcmp63_eq, hcmp63_ne, hcmp63_z⟩
  have hadd1 := zeroExtend64_add1_truncate32_ofNat64 (by omega : 32 + info.length < 63)
  have hi_eq : (BitVec.ofNat 64 i == 255#64) = false := by rcases hi with rfl | rfl <;> rfl
  have hi_ne : (BitVec.ofNat 64 i != 255#64) = true := by rcases hi with rfl | rfl <;> rfl
  have hi_cmp : (AddWithCarry64 (BitVec.ofNat 64 i) (bv% (2 ^ 64 - 256)) true).2.z = false := by
    rcases hi with rfl | rfl <;> rfl
  have hi_add1 : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 i) + 1#32) =
      BitVec.ofNat 64 (i + 1) := by
    rcases hi with rfl | rfl <;> rfl
  iterate 14 s2_step
  refine RunsTo.refl ?_
  have hc1 : ExpandCommon okmLen s₀ (s.setMem (s.mem.writeBytes (esp s₀ + 96#64) info)) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  have hA2 := agreesOutside_counter_writes (m₁ := m₁) (s₀ := s₀)
    (b1 := BitVec.ofNat 8 (32 + info.length)) (c := BitVec.ofNat 8 (i + 1))
    (b2 := BitVec.ofNat 8 (32 + info.length + 1)) (by omega : 32 + info.length < 63)
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 177) hc1
      (by rw [State.status_setMem]; simp only [arm64_norm, hrun])
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by rw [mem_setMem, mem_setMem, zeroExtend64_truncate32_ofNat64 (by omega : 32 + info.length < 64)]; exact hA2)
      (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx19],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_⟩
  · rw [mem_setMem, zeroExtend64_truncate32_ofNat64 (by omega : 32 + info.length < 64)]
    exact HmacSt.of_memcpy_counter_64_32 hx.hmac_64 ht_len hinfo_lt
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · rcases disj_esp_x2_sub_96_64 hpre h0 hdst with ⟨hd2, hd1⟩
      rw [mem_setMem, zeroExtend64_truncate32_ofNat64 (by omega : 32 + info.length < 64)]
      refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 64#64 177 hd2 hA2
        (by have := hpre.okm_len; omega) ?_
      exact (hA1.readBytes_eq hd1 (by have := hpre.okm_len; omega)).trans hx.okm_pre

theorem iter_c_placed_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hrem : rem = 32 ∨ rem = 48 ∨ rem = 16)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopB expPlacedFakeB C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopCPlaced C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀) := by
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
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  iterate 17 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 240#64) (sz := 0x90) hx.common hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl, hx19, ?_, hx22, hx23, hx24, ?_, hx28, ?_, ?_⟩
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]
    rcases hrem with rfl | rfl | rfl <;> rfl
  · simp only [mem_setMem]
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
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd : DisjointRegions (esp s₀ + 240#64) 0x90 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 240#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 240#64 0x90 hd (by prove_agrees_esp)
        (by have := hpre.okm_len; omega) hx.okm_pre

theorem iter_fin_placed_runsTo
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hFin : ∀ {key msg : List (BitVec 8)} {s : State},
      ExpandFrame okmLen s₀ s.mem →
      FinalizeFixedProof.FinPre finPlacedFakeB C.F key msg s →
      RunsTo ((blkPC_53).rebase (blkPl_53).base H) s (FinalizeFixedProof.FinPost C.F key msg s))
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopCPlaced C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀) := by
  rcases fin_side_conditions hpre hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hfin_pre : FinalizeFixedProof.FinPre finPlacedFakeB C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) s :=
    { pc_eq := by rw [hx.pc_eq]; simp only [arm64_norm]
      status := hx.common.status
      key_le := hpre.prk_le
      msg_lt := by have := hpre.info_lt; simp [ht_len]; omega
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_240
      rw_out := by rw [hx.x0_eq]; exact hrw_x0
      rw_hm := by rw [hx.x1_eq]; exact hrw_x1
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sp
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; exact hd_x0_x1
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; exact hd_x0_sp
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; exact hd_x1_sp
      sp_aligned := by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned }
  refine (hFin hx.common.frame hfin_pre).mono
    fun s' ⟨hpc', hrun', hcs, ht, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'
  rw [hx.x0_eq] at ht
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq] at hfr
  have hokm' : s'.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · refine (Frame.readBytes_eq hfr (fun r hr => ?_) (by have := hpre.okm_len; omega)).trans hx.okm_pre
      have hd_stk : DisjointRegions (s₀.sp - 640#64) 640 (s₀.readReg64 .x2) dstOff :=
        hpre.disj_x2_stack.symm.sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact hd_stk.sub_left _ ⟨by simp, by unfold esp; bv_omega⟩
  exact ⟨by simp only [arm64_norm, hpc'],
    ExpandCommon.of_fin_frame hx.common hrun' hcs hfr,
    (CalleeSaved.x19 hcs).trans hx.x19_eq,
    (CalleeSaved.x21 hcs).trans hx.x21_eq,
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans hx.x23_eq,
    (CalleeSaved.x24 hcs).trans hx.x24_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq,
    (CalleeSaved.x28 hcs).trans hx.x28_eq,
    ht, hokm'⟩

theorem iter_d_continue_placed_runsTo {prk info tPrev okmSoFar tNext : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hi : i = 1)
    (hdst : dstOff + 32 ≤ okmLen)
    (htNext : tNext = hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]))
    (hx : StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar okmLen i 48 dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoop expPlacedFakeB okmLen tNext (okmSoFar ++ tNext) (i + 1) 16 (dstOff + 32) s₀) := by
  subst hi
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
  have hx26 : s.readReg64 .x26 = 16#64 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) okmLen := ExpandFrame.rw_x2 hpre hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 :=
    hrw_x2.sub (by have := hpre.okm_len; bv_omega)
  iterate 4 s2_step
  refine s2_memcpy_step_placed C H hrun rfl rfl rfl rfl rfl ht_208 hrw_dst ?_
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) tNext
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 :=
    agreesOutside_writeBytes_le s.mem _ tNext 32 (by omega)
  have hc1 : ExpandCommon okmLen s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_x2 hpre hx.common hrun hsp hx29 hx27 hx20 hA1
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hc1.frame
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
    ?_,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx24],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_⟩
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]; rfl
  · simp only [mem_setMem]
    have ht_m1 : m₁.readBytes (esp s₀ + 208#64) 32 = tNext := by
      have hd : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 (esp s₀ + 208#64) 32 :=
        (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
          ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ + 208#64)
          ⟨by decide, by unfold esp; bv_omega⟩
      exact (hA1.readBytes_eq hd (by decide)).trans ht_208
    exact readBytes_32_esp_32_of_208 ht_m1
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
  · have hd2 : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) (dstOff + 32) :=
      (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64)
        ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
        ⟨by omega, by have := hpre.okm_len; bv_omega⟩
    dsimp only [mem_setMem]
    refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd2 (by prove_agrees_esp)
      (by have := hpre.okm_len; omega) ?_
    rw [Bytes.readBytes_add m₁ (s₀.readReg64 .x2) dstOff 32]
    have hleft : m₁.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
      by_cases h0 : dstOff = 0
      · subst h0; exact hx.okm_pre
      · have hd1 : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 (s₀.readReg64 .x2) dstOff := by
          unfold DisjointRegions; have := hpre.okm_len; bv_omega
        exact (hA1.readBytes_eq hd1 (by have := hpre.okm_len; omega)).trans hx.okm_pre
    have hright : m₁.readBytes (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 = tNext := by
      conv_lhs => rw [← ht_len]
      exact Bytes.readBytes_writeBytes_same s.mem _ tNext (by omega)
    rw [hleft, hright]

theorem iter_d_done_placed_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 32 ∨ rem = 16)
    (hdst : dstOff + rem = okmLen)
    (hokm : okmSoFar ++ (hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])).take rem =
              hkdfExpand C.F prk info okmLen)
    (hx : StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateDone expPlacedFakeB C.F prk info okmLen s₀) := by
  let tNext := hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])
  have hmin : min rem 32 = rem := by rcases hrem with rfl | rfl <;> rfl
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq
  have hx23 : s.readReg64 .x23 = BitVec.ofNat 64 rem := by rw [hx.x23_eq, hmin]
  have hx24 := hx.x24_eq
  have hx26 : s.readReg64 .x26 = 0#64 := by
    have h := hx.x26_eq; rw [hmin, Nat.sub_self] at h; exact h
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) okmLen := ExpandFrame.rw_x2 hpre hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem :=
    hrw_x2.sub (by have := hpre.okm_len; bv_omega)
  have hread_rem : s.mem.readBytes (esp s₀ + 208#64) rem = tNext.take rem := by
    have hslice := Bytes.readBytes_slice_of_readBytes_eq s.mem (esp s₀ + 208#64) tNext
      (by rw [length_hmacWith]; exact hx.t_208) 0 rem (by rw [length_hmacWith]; omega)
    simpa using hslice
  iterate 4 s2_step
  have hx2_nat : (BitVec.ofNat 64 rem).toNat = rem := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine s2_memcpy_step_placed C H hrun rfl rfl rfl hx2_nat rfl hread_rem hrw_dst ?_
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) (tNext.take rem)
  have htake_len : (tNext.take rem).length = rem := by
    rw [List.length_take, length_hmacWith]; omega
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem :=
    agreesOutside_writeBytes_le s.mem _ (tNext.take rem) rem (by omega)
  have hc1 : ExpandCommon okmLen s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_x2 hpre hx.common hrun hsp hx29 hx27 hx20 hA1
      ⟨by omega, by have := hpre.okm_len; bv_omega⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hc1.frame
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
  have hd2 : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) okmLen :=
    hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64) ⟨by decide, by unfold esp; bv_omega⟩
  dsimp only [mem_setMem]
  refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd2 (by prove_agrees_esp)
    (by have := hpre.okm_len; omega) ?_
  rw [← hdst, Bytes.readBytes_add m₁ (s₀.readReg64 .x2) dstOff rem]
  have hleft : m₁.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd1 : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem (s₀.readReg64 .x2) dstOff := by
        unfold DisjointRegions; have := hpre.okm_len; bv_omega
      exact (hA1.readBytes_eq hd1 (by have := hpre.okm_len; omega)).trans hx.okm_pre
  have hright : m₁.readBytes (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem = tNext.take rem := by
    conv_lhs => rw [← htake_len]
    exact Bytes.readBytes_writeBytes_same s.mem _ (tNext.take rem) (by omega)
  rw [hleft, hright, hokm, hdst]

theorem iter_to_fin_placed_runsTo
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hFin : ∀ {key msg : List (BitVec 8)} {s : State},
      ExpandFrame okmLen s₀ s.mem →
      FinalizeFixedProof.FinPre finPlacedFakeB C.F key msg s →
      RunsTo ((blkPC_53).rebase (blkPl_53).base H) s (FinalizeFixedProof.FinPost C.F key msg s))
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 32 ∨ rem = 48 ∨ rem = 16)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoop expPlacedFakeB okmLen tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar okmLen i rem dstOff s₀) := by
  refine (iter_a1_placed_runsTo hpre hrem hdst hx).trans fun s1 hs1 => ?_
  refine (iter_a2_placed_runsTo hpre ht_len hdst hs1).trans fun s2 hs2 => ?_
  refine (iter_b_placed_runsTo hpre ht_len hi hdst hs2).trans fun s3 hs3 => ?_
  refine (iter_c_placed_runsTo hpre hrem hdst hs3).trans fun s4 hs4 => ?_
  exact iter_fin_placed_runsTo hFin hpre ht_len hdst hs4

theorem epilogue_placed_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀)
    (hx : StateDone expPlacedFakeB C.F prk info okmLen s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s (ExpandPost C.F prk info okmLen s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrame.rw_esp hpre hx.common.frame
  rcases hx.common.saved with ⟨m400, m408, m416, m424, m432, m440, m448, m456, m464, m472, m480, m488⟩
  iterate 8 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl, hrun, ⟨(esp_eq_add s₀).symm, ?_⟩, hx.okm_all, hx.common.frame⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end LoopPlaced
end Expand
end CryptoVerification.LibsignalTripleRatchet
