/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandHelpersExt
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt

/-!
# Extended-Stack Cut Predicates and Segments for `expand_multi_info`

Defines `extHookStack` cut-point predicates `StateX0pX`–`ExpandPostX` and proves the
Block 1 and loop-entry segments of `GenericHkdf<Hmac<Sha256>>::expand_multi_info` on
`tripleRatchetProgAtExt`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.LibsignalTripleRatchet.HkdfExt.ExpandExt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
open CryptoVerification.LibsignalTripleRatchet.Extract (frame_of_agreesOutside RunsToE S2Frame)
open CryptoVerification.LibsignalTripleRatchet.Expand
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)

attribute [scoped simp, local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint
  sp_sub_496_eq_esp sp_add_neg496_eq_esp esp_add_496_sub_496
  read8_write64_120_127 CryptoVerification.LibsignalTripleRatchet.Expand.truncate8_ofNat64
  bv32_zero_add bv8_zero_add
  t1_length t2_length t3_length

private theorem runsTo_toE_local {prog : Program} {s₀ : State} {P : State → Prop}
    (h : RunsTo prog s₀ P) : RunsToE prog s₀ P :=
  fun hL => by
    obtain ⟨sf, hst, htr, hP, hLf⟩ := h hL
    exact ⟨sf, hst, htr, hP, hLf⟩

/-- Preserves `HmacSt m₀ a F key pmsg` across `memcpyRO` writing `info` (`info.length < 23`)
at `a + BitVec.ofNat 64 pmsg.length` (`a = esp s₀ + 64#64`, `pmsg.length ≤ 32`). -/
theorem HmacSt.of_memcpyRO_frame {m₀ m₁ : Memory} {s₀ : State} {infoPtr : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key pmsg info : List (BitVec 8)}
    (h₀ : HmacSt m₀ (esp s₀ + 64#64) F key pmsg)
    (hrw_esp : m₀.RW (esp s₀) 496)
    (hp : pmsg.length ≤ 32)
    (hinfo : info.length < 23)
    (hfr : S2FrameRO infoPtr info.length m₀ m₁
      [(esp s₀ + 64#64 + BitVec.ofNat 64 pmsg.length, info.length),
       (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    HmacSt m₁ (esp s₀ + 64#64) F key pmsg := by
  let a := esp s₀ + 64#64
  rcases h₀ with ⟨hlen, hpmsg, hpos, hin, hcnt1, hout, hcnt2⟩
  have hread_hi : ∀ (off : BitVec 64) (sz : ℕ),
      0 < sz → 64 ≤ off.toNat → off.toNat + sz ≤ 144 →
      m₁.readBytes (a + off) sz = m₀.readBytes (a + off) sz := by
    intro off sz hsz0 h64 h144
    refine hfr.readBytes_eq (hrw_esp.sub (by dsimp [a]; bv_omega)) (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold DisjointRegions; dsimp [a]; bv_omega
    · change DisjointRegions (esp s₀ - 16384#64) 16384 (a + off) sz
      unfold DisjointRegions; dsimp [a]; bv_omega
  have hread64_hi : ∀ (off : BitVec 64),
      64 ≤ off.toNat → off.toNat + 8 ≤ 144 →
      m₁.read64 (a + off) = m₀.read64 (a + off) := by
    intro off h64 h144
    refine hfr.read64_eq (hrw_esp.sub (by dsimp [a]; bv_omega)) (fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold DisjointRegions; dsimp [a]; bv_omega
    · change DisjointRegions (esp s₀ - 16384#64) 16384 (a + off) 8
      unfold DisjointRegions; dsimp [a]; bv_omega
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hp0 : pmsg.length = 0
    · simp [hp0] at hpmsg ⊢; exact hpmsg
    · refine (hfr.readBytes_eq (hrw_esp.sub (by dsimp [a]; bv_omega)) (fun r hr => ?_) (by omega)).trans hpmsg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · unfold DisjointRegions; dsimp [a]; bv_omega
      · change DisjointRegions (esp s₀ - 16384#64) 16384 a pmsg.length
        unfold DisjointRegions; dsimp [a]; bv_omega
  · refine (hfr.1 (a + 0x3f#64)
      (hrw_esp.readable (a + 0x3f#64) (by unfold InRegion; dsimp [a]; bv_omega)).1
      (hrw_esp.readable (a + 0x3f#64) (by unfold InRegion; dsimp [a]; bv_omega)).2
      (fun r hr => ?_)).trans hpos
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold OutsideRegion; dsimp [a]; bv_omega
    · change OutsideRegion (esp s₀ - 16384#64) 16384 (a + 0x3f#64)
      unfold OutsideRegion; dsimp [a]; bv_omega
  · exact (hread_hi 0x40#64 32 (by decide) (by decide) (by decide)).trans hin
  · exact (hread64_hi 0x60#64 (by decide) (by decide)).trans hcnt1
  · exact (hread_hi 0x68#64 32 (by decide) (by decide) (by decide)).trans hout
  · exact (hread64_hi 0x88#64 (by decide) (by decide)).trans hcnt2

/-- Given `HmacSt m₁ a F key pmsg` and `m₁.readBytes (a + BitVec.ofNat 64 pmsg.length) info.length = info`,
the 4 byte writes of counter `c` and cursor `pmsg.length + info.length + 1` produce
`HmacSt m₂ a F key (pmsg ++ info ++ [c])`. -/
theorem HmacSt.of_counter_writes {m₁ : Memory} {a : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key pmsg info : List (BitVec 8)}
    {b1 c : BitVec 8}
    (h₀ : HmacSt m₁ a F key pmsg)
    (hinfo_m₁ : m₁.readBytes (a + BitVec.ofNat 64 pmsg.length) info.length = info)
    (hp : pmsg.length ≤ 32)
    (hinfo : info.length < 23) :
    let m₂ := (((m₁.write8 (a + 63#64) b1).write8 (a + 176#64) c).write8
      (a + BitVec.ofNat 64 (pmsg.length + info.length)) c).write8
      (a + 63#64) (BitVec.ofNat 8 (pmsg.length + info.length + 1))
    HmacSt m₂ a F key (pmsg ++ info ++ [c]) := by
  intro m₂
  rcases h₀ with ⟨_, hpmsg, _, hin, hcnt1, hout, hcnt2⟩
  have hlen : (pmsg ++ info ++ [c]).length = pmsg.length + info.length + 1 := by
    simp; omega
  have hag_w : AgreesOutside m₁ m₂ (a + BitVec.ofNat 64 (pmsg.length + info.length)) 177 := by
    dsimp only [m₂]
    refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
    refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
    refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
    exact AgreesOutside.write8 (AgreesOutside.rfl' _ _ _) (by simp only [InRegion]; bv_omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen,
        Bytes.readBytes_add m₂ a (pmsg.length + info.length) 1,
        Bytes.readBytes_add m₂ a pmsg.length info.length]
    have h_pmsg : m₂.readBytes a pmsg.length = pmsg := by
      by_cases hp0 : pmsg.length = 0
      · simp [hp0] at hpmsg ⊢; exact hpmsg
      · have hd2 : DisjointRegions (a + BitVec.ofNat 64 (pmsg.length + info.length)) 177 a pmsg.length := by
          unfold DisjointRegions; bv_omega
        rw [hag_w.readBytes_eq hd2 (by omega), hpmsg]
    have h_info : m₂.readBytes (a + BitVec.ofNat 64 pmsg.length) info.length = info := by
      by_cases hi0 : info.length = 0
      · have hnil : info = [] := List.eq_nil_of_length_eq_zero hi0
        subst hnil; rfl
      · have hd2 : DisjointRegions (a + BitVec.ofNat 64 (pmsg.length + info.length)) 177
            (a + BitVec.ofNat 64 pmsg.length) info.length := by
          unfold DisjointRegions; bv_omega
        rw [hag_w.readBytes_eq hd2 (by omega), hinfo_m₁]
    have h_c : m₂.readBytes (a + BitVec.ofNat 64 (pmsg.length + info.length)) 1 = [c] := by
      dsimp only [Memory.readBytes, m₂]
      rw [Memory.read8_write8_ne (by bv_omega), Memory.read8_write8_same]
    rw [h_pmsg, h_info, h_c, List.append_assoc]
  · rw [hlen, show (0x3f#64 : BitVec 64) = 63#64 from rfl]
    dsimp only [m₂]
    exact Memory.read8_write8_same _ _ _
  · have h_ag_st : ∀ (off : BitVec 64) (sz : ℕ),
        0 < sz → 64 ≤ off.toNat → off.toNat + sz ≤ 144 →
        m₂.readBytes (a + off) sz = m₁.readBytes (a + off) sz := by
      intro off sz hsz0 h64 h144
      dsimp only [m₂]
      rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by omega),
          (AgreesOutside.rfl' _ (a + BitVec.ofNat 64 (pmsg.length + info.length)) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by omega),
          (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by omega),
          (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by omega)]
    exact (h_ag_st 0x40#64 32 (by decide) (by decide) (by decide)).trans hin
  · dsimp only [m₂]
    rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + BitVec.ofNat 64 (pmsg.length + info.length)) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        hcnt1]
  · have h_ag_out : m₂.readBytes (a + 0x68#64) 32 = m₁.readBytes (a + 0x68#64) 32 := by
      dsimp only [m₂]
      rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (a + BitVec.ofNat 64 (pmsg.length + info.length)) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide)]
    exact h_ag_out.trans hout
  · dsimp only [m₂]
    rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + BitVec.ofNat 64 (pmsg.length + info.length)) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        hcnt2]

/-! ## Cut-Point Predicates -/

structure StateX0pX (b infoPtr : BitVec 64) (infoLen okmLen : ℕ) (s₀ s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 32)
  status : s.status = .Running
  sp_eq  : s.sp = esp s₀
  x29_eq : s.readReg64 .x29 = esp s₀ + 400#64
  x0_eq  : s.readReg64 .x0 = s₀.readReg64 .x0
  x1_eq  : s.readReg64 .x1 = s₀.readReg64 .x1
  x2_eq  : s.readReg64 .x2 = s₀.readReg64 .x2
  x3_eq  : s.readReg64 .x3 = BitVec.ofNat 64 okmLen
  saved  : ExpandSaved s₀ s.mem
  frame  : ExpandFrameX infoPtr infoLen okmLen s₀ s.mem

structure StateX1X (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (okmLen : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "memcpy")
  common  : ExpandCommonX infoPtr info.length okmLen s₀ s
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 192)
  x0_eq   : s.readReg64 .x0 = esp s₀ + 64#64
  x1_eq   : s.readReg64 .x1 = infoPtr
  x2_eq   : s.readReg64 .x2 = BitVec.ofNat 64 info.length
  x19_eq  : s.readReg64 .x19 = 0#64
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2
  x23_eq  : s.readReg64 .x23 = 32#64
  x24_eq  : s.readReg64 .x24 = BitVec.ofNat 64 okmLen
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 info.length
  hmac_64 : HmacSt s.mem (esp s₀ + 64#64) F prk []

structure StateX1bX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (okmLen : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 448)
  common  : ExpandCommonX infoPtr info.length okmLen s₀ s
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2
  x23_eq  : s.readReg64 .x23 = 32#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32)
  hmac_64 : HmacSt s.mem (esp s₀ + 64#64) F prk (info ++ [1#8])

structure StateX2X (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (okmLen : ℕ) (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]")
  common   : ExpandCommonX infoPtr info.length okmLen s₀ s
  lr_eq    : s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 500)
  x0_eq    : s.readReg64 .x0 = esp s₀ + 208#64
  x1_eq    : s.readReg64 .x1 = esp s₀ + 240#64
  x22_eq   : s.readReg64 .x22 = s₀.readReg64 .x2
  x23_eq   : s.readReg64 .x23 = 32#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32)
  hmac_240 : HmacSt s.mem (esp s₀ + 240#64) F prk (info ++ [1#8])

structure StateX2rX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (okmLen : ℕ) (s₀ s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 500)
  common : ExpandCommonX infoPtr info.length okmLen s₀ s
  x22_eq : s.readReg64 .x22 = s₀.readReg64 .x2
  x23_eq : s.readReg64 .x23 = 32#64
  x26_eq : s.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32)
  t1_208 : s.mem.readBytes (esp s₀ + 208#64) 32 = t1 F prk info

structure StateLoopX (b infoPtr : BitVec 64) (infoLen okmLen : ℕ)
    (tPrev okmSoFar : List (BitVec 8)) (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 712)
  common  : ExpandCommonX infoPtr infoLen okmLen s₀ s
  x19_eq  : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x24_eq  : s.readReg64 .x24 = 64#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x28_eq  : s.readReg64 .x28 = esp s₀ + 64#64
  t_cache : s.mem.readBytes (esp s₀ + 32#64) 32 = tPrev
  okm_pre : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

structure StateLoopA1X (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk tPrev okmSoFar : List (BitVec 8)) (infoPtr : BitVec 64)
    (infoLen okmLen i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 816)
  common  : ExpandCommonX infoPtr infoLen okmLen s₀ s
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

structure StateLoopA2X (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (tPrev okmSoFar : List (BitVec 8))
    (okmLen i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "memcpy")
  common  : ExpandCommonX infoPtr info.length okmLen s₀ s
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

structure StateLoopBX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info tPrev okmSoFar : List (BitVec 8)) (infoPtr : BitVec 64)
    (okmLen i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 604)
  common  : ExpandCommonX infoPtr info.length okmLen s₀ s
  x19_eq  : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 (min rem 32)
  x24_eq  : s.readReg64 .x24 = 64#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x28_eq  : s.readReg64 .x28 = esp s₀ + 64#64
  hmac_64 : HmacSt s.mem (esp s₀ + 64#64) F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

structure StateLoopCX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info tPrev okmSoFar : List (BitVec 8)) (infoPtr : BitVec 64)
    (okmLen i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]")
  common   : ExpandCommonX infoPtr info.length okmLen s₀ s
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

structure StateLoopFinX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info tPrev okmSoFar : List (BitVec 8)) (infoPtr : BitVec 64)
    (okmLen i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 672)
  common  : ExpandCommonX infoPtr info.length okmLen s₀ s
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

structure StateDoneX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (okmLen : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 1176)
  common  : ExpandCommonX infoPtr info.length okmLen s₀ s
  okm_all : s.mem.readBytes (s₀.readReg64 .x2) okmLen = hkdfExpand F prk info okmLen

def ExpandPostX (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (okmLen : ℕ) (s₀ s' : State) : Prop :=
  s'.pc = s₀.readReg64 .lr ∧
  s'.status = .Running ∧
  CalleeSaved s₀ s' ∧
  s'.mem.readBytes (s₀.readReg64 .x2) okmLen = hkdfExpand F prk info okmLen ∧
  ExpandFrameX infoPtr info.length okmLen s₀ s'.mem

/-! ## Block 1 and Loop Segment Proofs -/

theorem CallingConventionPreserved.x23 {s s' : State} (h : CallingConventionPreserved s s') :
    s'.readReg64 .x23 = s.readReg64 .x23 := h.2.2.2.2.2.1
theorem CallingConventionPreserved.x24 {s s' : State} (h : CallingConventionPreserved s s') :
    s'.readReg64 .x24 = s.readReg64 .x24 := h.2.2.2.2.2.2.1
theorem CallingConventionPreserved.x25 {s s' : State} (h : CallingConventionPreserved s s') :
    s'.readReg64 .x25 = s.readReg64 .x25 := h.2.2.2.2.2.2.2.1
theorem CallingConventionPreserved.x26 {s s' : State} (h : CallingConventionPreserved s s') :
    s'.readReg64 .x26 = s.readReg64 .x26 := h.2.2.2.2.2.2.2.2.1
theorem CallingConventionPreserved.x28 {s s' : State} (h : CallingConventionPreserved s s') :
    s'.readReg64 .x28 = s.readReg64 .x28 := h.2.2.2.2.2.2.2.2.2.2.1

theorem ExpandPreX.out_info_esp_off {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    {off : BitVec 64} {sz : ℕ} (hoff : off.toNat + sz ≤ 496) :
    ∀ a, InRegion infoPtr info.length a → OutsideRegion (esp s₀ + off) sz a := by
  intro a ha
  have hout := hpre.out_info_stk a ha
  unfold OutsideRegion esp at *
  bv_omega

theorem ExpandPreX.out_info_extStack {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀) :
    ∀ a, InRegion infoPtr info.length a →
      OutsideRegion (esp s₀ - BitVec.ofNat 64 extHookStack) extHookStack a := by
  intro a ha
  have hout := hpre.out_info_stk a ha
  change OutsideRegion (esp s₀ - 16384#64) 16384 a
  unfold OutsideRegion esp at *
  bv_omega

theorem HmacSt.of_counter_writes_64_0 {m₁ : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key info : List (BitVec 8)}
    (h₀ : HmacSt m₁ (esp s₀ + 64#64) F key [])
    (hinfo_m₁ : m₁.readBytes (esp s₀ + 64#64) info.length = info)
    (hinfo : info.length < 23) :
    HmacSt ((((m₁.write8 (esp s₀ + 127#64) (BitVec.ofNat 8 info.length)).write8
      (esp s₀ + 240#64) 1#8).write8
      (esp s₀ + 64#64 + BitVec.ofNat 64 info.length) 1#8).write8
      (esp s₀ + 127#64) (BitVec.ofNat 8 (info.length + 1)))
      (esp s₀ + 64#64) F key (info ++ [1#8]) := by
  have h64_0 : esp s₀ + 64#64 + BitVec.ofNat 64 ([] : List (BitVec 8)).length = esp s₀ + 64#64 := by
    dsimp only [List.length_nil]; bv_lin
  have hm := HmacSt.of_counter_writes h₀ (by rw [h64_0]; exact hinfo_m₁) (by decide) hinfo
    (b1 := BitVec.ofNat 8 info.length) (c := 1#8)
  simp only [List.length_nil, Nat.zero_add, List.nil_append] at hm
  have h127 : esp s₀ + 64#64 + 63#64 = esp s₀ + 127#64 := by bv_lin
  have h240 : esp s₀ + 64#64 + 176#64 = esp s₀ + 240#64 := by bv_lin
  rw [h127, h240] at hm
  exact hm

theorem HmacSt.of_counter_writes_64_32 {m₁ : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key tPrev info : List (BitVec 8)} {i : ℕ}
    (h₀ : HmacSt m₁ (esp s₀ + 64#64) F key tPrev)
    (hinfo_m₁ : m₁.readBytes (esp s₀ + 96#64) info.length = info)
    (ht : tPrev.length = 32)
    (hinfo : info.length < 23) :
    HmacSt ((((m₁.write8 (esp s₀ + 127#64) (BitVec.ofNat 8 (32 + info.length))).write8
      (esp s₀ + 240#64) (BitVec.ofNat 8 (i + 1))).write8
      (esp s₀ + 64#64 + BitVec.ofNat 64 (32 + info.length)) (BitVec.ofNat 8 (i + 1))).write8
      (esp s₀ + 127#64) (BitVec.ofNat 8 (32 + info.length + 1)))
      (esp s₀ + 64#64) F key (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) := by
  have h96 : esp s₀ + 64#64 + BitVec.ofNat 64 tPrev.length = esp s₀ + 96#64 := by
    rw [ht]; bv_lin
  have hm := HmacSt.of_counter_writes h₀ (by rw [h96]; exact hinfo_m₁) (by omega) hinfo
    (b1 := BitVec.ofNat 8 (32 + info.length)) (c := BitVec.ofNat 8 (i + 1))
  dsimp only [] at hm
  have h127 : esp s₀ + 64#64 + 63#64 = esp s₀ + 127#64 := by bv_lin
  have h240 : esp s₀ + 64#64 + 176#64 = esp s₀ + 240#64 := by bv_lin
  have hpos : esp s₀ + 64#64 + BitVec.ofNat 64 (tPrev.length + info.length) =
      esp s₀ + 64#64 + BitVec.ofNat 64 (32 + info.length) := by rw [ht]
  have hlen1 : tPrev.length + info.length + 1 = 32 + info.length + 1 := by omega
  rw [h127, h240, hpos, hlen1] at hm
  exact hm

theorem canWrite_esp_64_add {m : Memory} {s₀ : State} {k : ℕ}
    (hrw : m.RW (esp s₀) 496) (hk : k < 64) :
    m.canWrite (esp s₀ + (64#64 + BitVec.ofNat 64 k)) 1 = true ∧
    m.canWrite (esp s₀ + 64#64 + BitVec.ofNat 64 k) 1 = true := by
  have h1 : m.canWrite (esp s₀ + (64#64 + BitVec.ofNat 64 k)) 1 = true :=
    hrw.canWrite_sub (by bv_omega) (by decide)
  refine ⟨h1, ?_⟩
  rw [BitVec.add_assoc]; exact h1

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

section SegmentsX

variable {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
  {ext : String → Option (State → State)}

theorem seg0_x_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s₀ (StateX0pX img.base infoPtr info.length okmLen s₀) := by
  have hpc := hpre.pc_eq
  have hrun := hpre.status
  have hx3 := hpre.x3_eq
  have hsp_al : (s₀.sp &&& 15#64) = 0#64 := hpre.sp_aligned
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s₀.mem.RW (esp s₀) 496 :=
    ExpandFrameX.rw_esp hpre (S2FrameRO.refl infoPtr info.length s₀.mem _)
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
  · exact ExpandFrameX.of_agreesOutside_esp (off := 400#64) (sz := 96)
      (S2FrameRO.refl infoPtr info.length s₀.mem _) (by prove_agrees_esp) (by decide)

theorem seg1_x_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hx : StateX0pX img.base infoPtr info.length okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (StateX1X img.base F prk info infoPtr okmLen s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.status
  have hsp := hx.sp_eq
  have hx29 := hx.x29_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hx3 := hx.x3_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hx.frame
  have hread_x0 : s.mem.Readable (s₀.readReg64 .x0) 0x90 := ExpandFrameX.readable_x0 hpre hx.frame
  have hread_x1 : s.mem.Readable (s₀.readReg64 .x1) 16 := ExpandFrameX.readable_x1 hpre hx.frame
  rcases read64_x0_write64_esp hpre.toExpandPre with ⟨h_x0_w0, h_x0_w⟩
  rcases read64_x1_write_esp hpre.toExpandPre with ⟨h_x1_w0, h_x1_w8, _, _⟩
  have hx1_val0 : s.mem.read64 (s₀.readReg64 .x1) = infoPtr :=
    ExpandFrameX.info_ptr_eq hpre hx.frame
  have hx1_val8 : s.mem.read64 (s₀.readReg64 .x1 + 8#64) = BitVec.ofNat 64 info.length :=
    ExpandFrameX.info_len_eq hpre hx.frame
  have hpos_x0 : s.mem.read8 (s₀.readReg64 .x0 + 63#64) = 0#8 :=
    (ExpandFrameX.hmac_x0 hpre hx.frame).2.2.1
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
     ExpandFrameX.of_agreesOutside_esp (off := 8#64) (sz := 312) hx.frame (by prove_agrees_esp) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [mem_setMem]
  exact HmacSt.of_copy_empty_esp_64 (ExpandFrameX.hmac_x0 hpre hx.frame)
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

theorem seg2a_tail_x_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ}
    {s₀ s₁ : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hpc : s₁.pc = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 192))
    (hc1 : ExpandCommonX infoPtr info.length okmLen s₀ s₁)
    (hx19 : s₁.readReg64 .x19 = 0#64)
    (hx22 : s₁.readReg64 .x22 = s₀.readReg64 .x2)
    (hx23 : s₁.readReg64 .x23 = 32#64)
    (hx24 : s₁.readReg64 .x24 = BitVec.ofNat 64 okmLen)
    (hx26 : s₁.readReg64 .x26 = BitVec.ofNat 64 info.length)
    (hhm : HmacSt s₁.mem (esp s₀ + 64#64) F prk [])
    (hinfo_m₁ : s₁.mem.readBytes (esp s₀ + 64#64) info.length = info) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s₁ (StateX1bX img.base F prk info infoPtr okmLen s₀) := by
  have hrun := hc1.status
  have hsp := hc1.sp_eq
  have hx29 := hc1.x29_eq
  have hx27 := hc1.x27_eq
  have hx20 := hc1.x20_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hinfo_lt := hpre.info_lt
  have hrw_esp : s₁.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hc1.frame
  rcases canWrite_esp_64_add hrw_esp (by omega : info.length < 64) with ⟨hcw_pos1, hcw_pos2⟩
  have hze32 := zeroExtend64_truncate32_ofNat64 (by omega : info.length < 64)
  have hand255 := zeroExtend64_and255_truncate32_ofNat64 (by omega : info.length < 64)
  have hand64_255 := and64_255_ofNat64 (by omega : info.length < 64)
  have hand40 := and_0xffffffffff_ofNat64 (by omega : info.length < 64)
  rcases cmp32_lt63_lemmas (by omega : info.length < 63) with ⟨hcmp63_eq, hcmp63_ne, hcmp63_z⟩
  have hadd1 := zeroExtend64_add1_truncate32_ofNat64 (by omega : info.length < 63)
  iterate 13 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp only [arm64_norm, hpc],
    ExpandCommonX.of_agreesOutside_low32 (off := 64#64) (sz := 177) hc1
      (by rw [State.status_setMem]; simp only [arm64_norm, hrun])
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by rw [mem_setMem]; exact agreesOutside_counter_writes (by omega : info.length < 63))
      (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    ?_, ?_⟩
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]
    rcases hpre.okm_len with rfl | rfl <;> rfl
  · rw [mem_setMem]
    exact HmacSt.of_counter_writes_64_0 hhm hinfo_m₁ hinfo_lt

theorem seg2a_x_runsTo (hRO : MemcpyROContract img ext)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hkf : s₀.mem.KeepsFrozen s.mem)
    (hsym : s.symtab = s₀.symtab)
    (hx : StateX1X img.base F prk info infoPtr okmLen s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateX1bX img.base F prk info infoPtr okmLen s₀) := by
  have hinfo_lt := hpre.info_lt
  have hrw_stk : s.mem.RW (s₀.sp - 17024#64) 17024 := ExpandFrameX.rw_stkX hpre hx.common.frame
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 64#64) info.length := hrw_esp.sub (by bv_omega)
  have hread_src : s.mem.Readable infoPtr info.length := ExpandFrameX.readable_info hpre hx.common.frame
  have hread_info : s.mem.readBytes infoPtr info.length = info :=
    ExpandFrameX.info_bytes_eq hpre hx.common.frame
  have hrw_ext : s.mem.RW (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hx.common.sp_eq]
    change s.mem.RW (esp s₀ - 16384#64) 16384
    exact hrw_stk.sub (by unfold esp; bv_omega)
  have hd_dst_stk : DisjointRegions (esp s₀ + 64#64) info.length
      (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hx.common.sp_eq]
    change DisjointRegions (esp s₀ + 64#64) info.length (esp s₀ - 16384#64) 16384
    unfold DisjointRegions; bv_omega
  have hx2_nat : (s.readReg64 .x2).toNat = info.length := by
    rw [hx.x2_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmc := memcpyRO_subroutine_runsTo hRO
    (hpre.frozen.of_keepsFrozen hkf)
    (hsym.trans hpre.symtab_eq)
    hx.pc_eq hx.common.status hx.x0_eq hx.x1_eq hx2_nat (by omega)
    hread_info hrw_dst hread_src hrw_ext hd_dst_stk
    (hpre.out_info_esp_off (by simp; omega))
    (by rw [hx.common.sp_eq]; exact hpre.out_info_extStack)
    (by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned)
  refine hmc.trans fun s₁ hs₁ => ?_
  rcases hs₁ with ⟨hpc₁, hstat₁, hcc₁, _, hdst₁, _, hfr_mc⟩
  rw [hx.common.sp_eq] at hfr_mc
  have hc1 : ExpandCommonX infoPtr info.length okmLen s₀ s₁ :=
    ExpandCommonX.of_memcpyRO_frame hpre hx.common ⟨by decide, by simp; omega⟩ hstat₁ hcc₁ hfr_mc
  have h64_0 : esp s₀ + 64#64 + BitVec.ofNat 64 ([] : List (BitVec 8)).length = esp s₀ + 64#64 := by
    dsimp only [List.length_nil]; bv_lin
  have hhm₁ : HmacSt s₁.mem (esp s₀ + 64#64) F prk [] :=
    HmacSt.of_memcpyRO_frame hx.hmac_64 hrw_esp (by decide) hinfo_lt (by rw [h64_0]; exact hfr_mc)
  exact runsTo_toE_local (seg2a_tail_x_runsTo hpre (hpc₁.trans hx.lr_eq) hc1
    ((Extract.CallingConventionPreserved.x19 hcc₁).trans hx.x19_eq)
    ((Extract.CallingConventionPreserved.x22 hcc₁).trans hx.x22_eq)
    ((CallingConventionPreserved.x23 hcc₁).trans hx.x23_eq)
    ((CallingConventionPreserved.x24 hcc₁).trans hx.x24_eq)
    ((CallingConventionPreserved.x26 hcc₁).trans hx.x26_eq)
    hhm₁ hdst₁)

theorem seg2b_x_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hx : StateX1bX img.base F prk info infoPtr okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (StateX2X img.base F prk info infoPtr okmLen s₀) := by
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
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hx.common.frame
  iterate 13 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommonX.of_agreesOutside_low32 (off := 240#64) (sz := 0x90) hx.common hrun hsp hx29 hx27 hx20
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

theorem seg3_head_x_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ}
    {s₀ s : State}
    (hx : StateX2rX img.base F prk info infoPtr okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (fun s_mc =>
      s_mc.pc = img.base + bv% (ls_off% "memcpy") ∧
      s_mc.status = .Running ∧
      s_mc.sp = esp s₀ ∧
      s_mc.readReg64 .lr = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 516) ∧
      s_mc.readReg64 .x0 = s₀.readReg64 .x2 ∧
      s_mc.readReg64 .x1 = esp s₀ + 208#64 ∧
      s_mc.readReg64 .x2 = 32#64 ∧
      s_mc.readReg64 .x20 = s₀.readReg64 .x0 ∧
      s_mc.readReg64 .x22 = s₀.readReg64 .x2 ∧
      s_mc.readReg64 .x23 = 32#64 ∧
      s_mc.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32) ∧
      s_mc.readReg64 .x27 = esp s₀ + 64#64 ∧
      s_mc.readReg64 .x29 = esp s₀ + 400#64 ∧
      s_mc.mem = s.mem) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx26 := hx.x26_eq
  iterate 4 s2_step
  refine RunsTo.refl ?_
  exact ⟨rfl, hrun, hsp, rfl, rfl, rfl, rfl, hx20, hx22, hx23, hx26, hx27, hx29, rfl⟩

theorem seg3_tail_x_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ}
    {s₀ s₁ : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hpc₁ : s₁.pc = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 516))
    (hc1 : ExpandCommonX infoPtr info.length okmLen s₀ s₁)
    (hx22 : s₁.readReg64 .x22 = s₀.readReg64 .x2)
    (hx23 : s₁.readReg64 .x23 = 32#64)
    (hx26 : s₁.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32))
    (ht1_x2 : s₁.mem.readBytes (s₀.readReg64 .x2) 32 = t1 F prk info)
    (ht1_208 : s₁.mem.readBytes (esp s₀ + 208#64) 32 = t1 F prk info) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s₁
      (StateLoopX img.base infoPtr info.length okmLen
        (t1 F prk info) (t1 F prk info) 1 (okmLen - 32) 32 s₀) := by
  have hrun := hc1.status
  have hsp := hc1.sp_eq
  have hx29 := hc1.x29_eq
  have hx27 := hc1.x27_eq
  have hx20 := hc1.x20_eq
  have hm16_1 : s₁.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw1_esp : s₁.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hc1.frame
  have h_rem_ne : (BitVec.ofNat 64 (okmLen - 32) == 0#64) = false := by
    rcases hpre.okm_len with rfl | rfl <;> rfl
  iterate 9 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommonX.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    rfl, ?_, ?_⟩
  · simp only [mem_setMem]
    exact readBytes_32_esp_32_of_208 ht1_208
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
  · have hd : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) 32 :=
      (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64)
        ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
        ⟨by decide, by have := hpre.okm_len; bv_omega⟩
    try dsimp only [mem_setMem]
    exact readBytes_eq_of_agreesOutside_esp s₀ s₁.mem 32#64 32 hd (by prove_agrees_esp) (by decide) ht1_x2

theorem seg3_x_runsTo
    (hMemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memcpy"))
      ((sessionMemcpySpec extHookStack).inImage img))
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hkf : s₀.mem.KeepsFrozen s.mem)
    (hsym : s.symtab = s₀.symtab)
    (hx : StateX2rX img.base F prk info infoPtr okmLen s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateLoopX img.base infoPtr info.length okmLen
        (t1 F prk info) (t1 F prk info) 1 (okmLen - 32) 32 s₀) := by
  refine RunsToE.trans_full (runsTo_toE_local (seg3_head_x_runsTo hx)) fun s_mc h_mc hkf_mc hsym_mc => ?_
  rcases h_mc with ⟨hpc_mc, hstat_mc, hsp_mc, hlr_mc, hx0_mc, hx1_mc, hx2_mc,
    hx20_mc, hx22_mc, hx23_mc, hx26_mc, hx27_mc, hx29_mc, hmem_mc⟩
  have hrw_stk : s_mc.mem.RW (s₀.sp - 17024#64) 17024 := by
    rw [hmem_mc]; exact ExpandFrameX.rw_stkX hpre hx.common.frame
  have hrw_esp : s_mc.mem.RW (esp s₀) 496 := by
    rw [hmem_mc]; exact ExpandFrameX.rw_esp hpre hx.common.frame
  have hrw_x2 : s_mc.mem.RW (s₀.readReg64 .x2) okmLen := by
    rw [hmem_mc]; exact ExpandFrameX.rw_x2 hpre hx.common.frame
  have hrw_dst : s_mc.mem.RW (s₀.readReg64 .x2) 32 :=
    hrw_x2.sub (by have := hpre.okm_len; bv_omega)
  have hrw_src : s_mc.mem.RW (esp s₀ + 208#64) 32 := hrw_esp.sub (by bv_omega)
  have hrw_ext : s_mc.mem.RW (s_mc.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_mc]
    change s_mc.mem.RW (esp s₀ - 16384#64) 16384
    exact hrw_stk.sub (by unfold esp; bv_omega)
  have hd_dst_src : DisjointRegions (s₀.readReg64 .x2) 32 (esp s₀ + 208#64) 32 :=
    (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2)
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ + 208#64)
      ⟨by decide, by unfold esp; bv_omega⟩
  have hd_dst_ext : DisjointRegions (s₀.readReg64 .x2) 32
      (s_mc.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_mc]
    change DisjointRegions (s₀.readReg64 .x2) 32 (esp s₀ - 16384#64) 16384
    exact (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2)
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ - 16384#64)
      ⟨by decide, by unfold esp; bv_omega⟩
  have hd_src_ext : DisjointRegions (esp s₀ + 208#64) 32
      (s_mc.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_mc]
    change DisjointRegions (esp s₀ + 208#64) 32 (esp s₀ - 16384#64) 16384
    unfold DisjointRegions; bv_omega
  have ht1_len : (t1 F prk info).length = 32 := t1_length F prk info
  have hc_mc : ExpandCommonX infoPtr info.length okmLen s₀ s_mc :=
    ⟨hstat_mc, hsp_mc, hx29_mc, hx27_mc, hx20_mc,
     by rw [hmem_mc]; exact hx.common.m8_eq,
     by rw [hmem_mc]; exact hx.common.m16_eq,
     by rw [hmem_mc]; exact hx.common.saved,
     by rw [hmem_mc]; exact hx.common.frame⟩
  have hmc := memcpy_subroutine_runsTo hMemcpy
    (bs := t1 F prk info)
    ((hpre.frozen.of_keepsFrozen hkf).of_keepsFrozen hkf_mc)
    (hsym_mc.trans (hsym.trans hpre.symtab_eq))
    hpc_mc hstat_mc hx0_mc hx1_mc
    (by rw [hx2_mc, ht1_len]; rfl)
    (by rw [ht1_len, hmem_mc]; exact hx.t1_208)
    (by rw [ht1_len]; exact hrw_dst)
    (by rw [ht1_len]; exact hrw_src)
    hrw_ext
    (by rw [ht1_len]; exact hd_dst_src)
    (by rw [ht1_len]; exact hd_dst_ext)
    (by rw [ht1_len]; exact hd_src_ext)
    (by rw [hsp_mc]; exact esp_aligned hpre.sp_aligned)
  refine hmc.trans fun s₁ hs₁ => ?_
  rcases hs₁ with ⟨hpc₁, hstat₁, hcc₁, _, ht1_x2, ht1_208, hfr_mc⟩
  rw [hsp_mc, ht1_len] at hfr_mc
  rw [ht1_len] at ht1_x2 ht1_208
  have hfr_mc0 : S2Frame s_mc.mem s₁.mem
      [(s₀.readReg64 .x2 + 0#64, 32), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    rw [BitVec.add_zero]; exact hfr_mc
  have hc1 : ExpandCommonX infoPtr info.length okmLen s₀ s₁ :=
    ExpandCommonX.of_memcpy_x2_frame hpre hc_mc ⟨by decide, by have := hpre.okm_len; simp; omega⟩
      hstat₁ hcc₁ hfr_mc0
  exact runsTo_toE_local (seg3_tail_x_runsTo hpre (hpc₁.trans hlr_mc) hc1
    ((Extract.CallingConventionPreserved.x22 hcc₁).trans hx22_mc)
    ((CallingConventionPreserved.x23 hcc₁).trans hx23_mc)
    ((CallingConventionPreserved.x26 hcc₁).trans hx26_mc)
    ht1_x2 ht1_208)

theorem iter_a1_x_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hrem : rem = 32 ∨ rem = 48 ∨ rem = 16)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopX img.base infoPtr info.length okmLen tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s
      (StateLoopA1X img.base F prk tPrev okmSoFar infoPtr info.length okmLen i rem dstOff s₀) := by
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
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hx.common.frame
  have hread_x0 : s.mem.Readable (s₀.readReg64 .x0) 0x90 :=
    ExpandFrameX.readable_x0 hpre hx.common.frame
  rcases read64_x0_write64_esp hpre.toExpandPre with ⟨h_x0_w0, h_x0_w⟩
  have hpos_x0 : s.mem.read8 (s₀.readReg64 .x0 + 63#64) = 0#8 :=
    (ExpandFrameX.hmac_x0 hpre hx.common.frame).2.2.1
  iterate 26 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc],
    ExpandCommonX.of_agreesOutside_low32 (off := 64#64) (sz := 256) hx.common hrun
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
    exact HmacSt.of_copy_empty_esp_64 (ExpandFrameX.hmac_x0 hpre hx.common.frame)
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
  · try dsimp only [mem_setMem]
    exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 256
      (by unfold DisjointRegions; bv_omega) (by prove_agrees_esp) (by decide) hx.t_cache
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd : DisjointRegions (esp s₀ + 64#64) 256 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      try dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 256 hd (by prove_agrees_esp)
        (by have := hpre.okm_len; omega) hx.okm_pre

theorem iter_a2_x_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA1X img.base F prk tPrev okmSoFar infoPtr info.length okmLen i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s
      (StateLoopA2X img.base F prk info infoPtr tPrev okmSoFar okmLen i rem dstOff s₀) := by
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
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hx.common.frame
  have hread_x1 : s.mem.Readable (s₀.readReg64 .x1) 16 :=
    ExpandFrameX.readable_x1 hpre hx.common.frame
  rcases read64_x1_write_esp hpre.toExpandPre with ⟨h_x1_w0, h_x1_w8, h_x1_w8_0, h_x1_w8_8⟩
  have hx1_val0 : s.mem.read64 (s₀.readReg64 .x1) = infoPtr :=
    ExpandFrameX.info_ptr_eq hpre hx.common.frame
  have hx1_val8 : s.mem.read64 (s₀.readReg64 .x1 + 8#64) = BitVec.ofNat 64 info.length :=
    ExpandFrameX.info_len_eq hpre hx.common.frame
  rcases cmp_lt32_lemmas (by have := hpre.info_lt; omega : info.length < 32) with
    ⟨h_info_ule32, h_info_ult32, h_info_cmp32⟩
  iterate 17 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommonX.of_agreesOutside_low32 (off := 64#64) (sz := 64) hx.common hrun hsp hx29 hx27 hx20
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
      try dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 64 hd (by prove_agrees_esp)
        (by have := hpre.okm_len; omega) hx.okm_pre

theorem iter_b_tail_x_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s₁ : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hdst : dstOff ≤ okmLen)
    (hpc₁ : s₁.pc = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 1124))
    (hc1 : ExpandCommonX infoPtr info.length okmLen s₀ s₁)
    (hx19 : s₁.readReg64 .x19 = BitVec.ofNat 64 i)
    (hx21 : s₁.readReg64 .x21 = 32#64)
    (hx22 : s₁.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
    (hx23 : s₁.readReg64 .x23 = BitVec.ofNat 64 (min rem 32))
    (hx25 : s₁.readReg64 .x25 = BitVec.ofNat 64 info.length)
    (hx26 : s₁.readReg64 .x26 = BitVec.ofNat 64 rem)
    (hx28 : s₁.readReg64 .x28 = esp s₀ + 64#64)
    (hhm : HmacSt s₁.mem (esp s₀ + 64#64) F prk tPrev)
    (hinfo_m₁ : s₁.mem.readBytes (esp s₀ + 96#64) info.length = info)
    (hokm₁ : s₁.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s₁
      (StateLoopBX img.base F prk info tPrev okmSoFar infoPtr okmLen i rem dstOff s₀) := by
  have hrun := hc1.status
  have hsp := hc1.sp_eq
  have hx29 := hc1.x29_eq
  have hx27 := hc1.x27_eq
  have hx20 := hc1.x20_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hinfo_lt := hpre.info_lt
  have hrw_esp : s₁.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hc1.frame
  rcases canWrite_esp_64_add hrw_esp (by omega : 32 + info.length < 64) with ⟨hcw_pos1, hcw_pos2⟩
  have hadd32 := zeroExtend64_add32_truncate32_ofNat64 (by omega : info.length < 32)
  have hand255 := zeroExtend64_and255_truncate32_ofNat64 (by omega : 32 + info.length < 64)
  have hand64_255 := and64_255_ofNat64 (by omega : 32 + info.length < 64)
  have hze8_32 := zeroExtend32_ofNat8_eq_truncate32 (by omega : 32 + info.length < 64)
  have hze8_64 := Expand.zeroExtend64_ofNat8 (by omega : 32 + info.length < 64)
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
  have hA2 := agreesOutside_counter_writes (m₁ := s₁.mem) (s₀ := s₀)
    (b1 := BitVec.ofNat 8 (32 + info.length)) (c := BitVec.ofNat 8 (i + 1))
    (b2 := BitVec.ofNat 8 (32 + info.length + 1)) (by omega : 32 + info.length < 63)
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc₁],
    ExpandCommonX.of_agreesOutside_low32 (off := 64#64) (sz := 177) hc1
      (by rw [State.status_setMem]; simp only [arm64_norm, hrun])
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by rw [mem_setMem, zeroExtend64_truncate32_ofNat64 (by omega : 32 + info.length < 64)]; exact hA2)
      (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx19],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_⟩
  · rw [mem_setMem, zeroExtend64_truncate32_ofNat64 (by omega : 32 + info.length < 64)]
    exact HmacSt.of_counter_writes_64_32 hhm hinfo_m₁ ht_len hinfo_lt
  · by_cases h0 : dstOff = 0
    · subst h0; exact hokm₁
    · have hd2 : DisjointRegions (esp s₀ + 64#64) 177 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      rw [mem_setMem, zeroExtend64_truncate32_ofNat64 (by omega : 32 + info.length < 64)]
      exact readBytes_eq_of_agreesOutside_esp s₀ s₁.mem 64#64 177 hd2 hA2
        (by have := hpre.okm_len; omega) hokm₁

theorem iter_b_x_runsTo (hRO : MemcpyROContract img ext)
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hdst : dstOff ≤ okmLen)
    (hkf : s₀.mem.KeepsFrozen s.mem)
    (hsym : s.symtab = s₀.symtab)
    (hx : StateLoopA2X img.base F prk info infoPtr tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateLoopBX img.base F prk info tPrev okmSoFar infoPtr okmLen i rem dstOff s₀) := by
  have hinfo_lt := hpre.info_lt
  have hrw_stk : s.mem.RW (s₀.sp - 17024#64) 17024 := ExpandFrameX.rw_stkX hpre hx.common.frame
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hx.common.frame
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) okmLen := ExpandFrameX.rw_x2 hpre hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 96#64) info.length := hrw_esp.sub (by bv_omega)
  have hread_src : s.mem.Readable infoPtr info.length := ExpandFrameX.readable_info hpre hx.common.frame
  have hread_info : s.mem.readBytes infoPtr info.length = info :=
    ExpandFrameX.info_bytes_eq hpre hx.common.frame
  have hrw_ext : s.mem.RW (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hx.common.sp_eq]
    change s.mem.RW (esp s₀ - 16384#64) 16384
    exact hrw_stk.sub (by unfold esp; bv_omega)
  have hd_dst_stk : DisjointRegions (esp s₀ + 96#64) info.length
      (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hx.common.sp_eq]
    change DisjointRegions (esp s₀ + 96#64) info.length (esp s₀ - 16384#64) 16384
    unfold DisjointRegions; bv_omega
  have hx2_nat : (s.readReg64 .x2).toNat = info.length := by
    rw [hx.x2_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmc := memcpyRO_subroutine_runsTo hRO
    (hpre.frozen.of_keepsFrozen hkf)
    (hsym.trans hpre.symtab_eq)
    hx.pc_eq hx.common.status hx.x0_eq hx.x1_eq hx2_nat (by omega)
    hread_info hrw_dst hread_src hrw_ext hd_dst_stk
    (hpre.out_info_esp_off (by simp; omega))
    (by rw [hx.common.sp_eq]; exact hpre.out_info_extStack)
    (by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned)
  refine hmc.trans fun s₁ hs₁ => ?_
  rcases hs₁ with ⟨hpc₁, hstat₁, hcc₁, _, hdst₁, _, hfr_mc⟩
  rw [hx.common.sp_eq] at hfr_mc
  have hc1 : ExpandCommonX infoPtr info.length okmLen s₀ s₁ :=
    ExpandCommonX.of_memcpyRO_frame hpre hx.common ⟨by decide, by simp; omega⟩ hstat₁ hcc₁ hfr_mc
  have h96 : esp s₀ + 64#64 + BitVec.ofNat 64 tPrev.length = esp s₀ + 96#64 := by
    rw [ht_len]; bv_lin
  have hhm₁ : HmacSt s₁.mem (esp s₀ + 64#64) F prk tPrev :=
    HmacSt.of_memcpyRO_frame hx.hmac_64 hrw_esp (by omega) hinfo_lt (by rw [h96]; exact hfr_mc)
  have hokm₁ : s₁.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · refine (hfr_mc.readBytes_eq (hrw_x2.sub (by bv_omega)) (fun r hr => ?_)
        (by have := hpre.okm_len; omega)).trans hx.okm_pre
      have hd_stk : DisjointRegions (s₀.sp - 17024#64) 17024 (s₀.readReg64 .x2) dstOff :=
        hpre.disj_x2_stack.symm.sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · by_cases hi0 : info.length = 0
        · rw [hi0]
          unfold DisjointRegions
          refine ⟨by omega, ?_⟩
          have hd96 := hd_stk.sub_left (esp s₀ + 96#64) (m₁ := 1) ⟨by decide, by unfold esp; bv_omega⟩
          exact hd96.2
        · exact hd_stk.sub_left (esp s₀ + 96#64) ⟨by omega, by unfold esp; bv_omega⟩
      · change DisjointRegions (esp s₀ - 16384#64) 16384 (s₀.readReg64 .x2) dstOff
        exact hd_stk.sub_left (esp s₀ - 16384#64) ⟨by decide, by unfold esp; bv_omega⟩
  exact runsTo_toE_local (iter_b_tail_x_runsTo hpre ht_len hi hdst (hpc₁.trans hx.lr_eq) hc1
    ((Extract.CallingConventionPreserved.x19 hcc₁).trans hx.x19_eq)
    ((Extract.CallingConventionPreserved.x21 hcc₁).trans hx.x21_eq)
    ((Extract.CallingConventionPreserved.x22 hcc₁).trans hx.x22_eq)
    ((CallingConventionPreserved.x23 hcc₁).trans hx.x23_eq)
    ((CallingConventionPreserved.x25 hcc₁).trans hx.x25_eq)
    ((CallingConventionPreserved.x26 hcc₁).trans hx.x26_eq)
    ((CallingConventionPreserved.x28 hcc₁).trans hx.x28_eq)
    hhm₁ hdst₁ hokm₁)

end SegmentsX

end CryptoVerification.LibsignalTripleRatchet.HkdfExt.ExpandExt
