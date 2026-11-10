/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLongExtA
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCallees
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand

/-!
# `.inImage`-Free `expand_multi_info` (`okmLen = 96`, `info.length = 46`): Loop and Top-Level Proof

Proves the multi-block loop segments (`T(2)` and `T(3)`), `expand_multi_info_96_46_runsToE_ext`, and
`expand_multi_info_96_46_ok_ext` on `tripleRatchetProgAtExt b ext` at `expandMultiInfoStackExt`
(`17024` B) from `HkdfStubsExt`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
open CryptoVerification.LibsignalTripleRatchet.HkdfExt.ExpandExt
open CryptoVerification.LibsignalTripleRatchet.Extract (frame_of_agreesOutside RunsToE S2Frame)
open CryptoVerification.LibsignalTripleRatchet.Expand
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (shaStateBytes readShaState)
open CryptoVerification.E2E.Pqxdh.Initiator (hkdfExpandMultiInfoSym)

attribute [local simp, local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint
  sp_sub_496_eq_esp sp_add_neg496_eq_esp esp_add_496_sub_496
  read8_write64_120_127 CryptoVerification.LibsignalTripleRatchet.Expand.truncate8_ofNat64
  bv32_zero_add bv8_zero_add
  t1_length t2_length t3_length

namespace HkdfLongExt

section Loop

variable {b : BitVec 64} {F : ShaCompress}
  {ext : String → Option (State → State)}

private theorem okm_of_agreesOutside_esp {prk info okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {s₀ : State} {m₁ m₂ : Memory} (off : BitVec 64) (sz dstOff : ℕ)
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ 496) (hdst : dstOff ≤ 96)
    (hA : AgreesOutside m₁ m₂ (esp s₀ + off) sz)
    (hokm : m₁.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar) :
    m₂.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
  by_cases h0 : dstOff = 0
  · subst h0; exact hokm
  · have hd : DisjointRegions (esp s₀ + off) sz (s₀.readReg64 .x2) dstOff :=
      (hpre.disj_x2_stack.symm.sub_left (esp s₀ + off) ⟨hoff.1, by unfold esp; bv_omega⟩).sub_right
        (s₀.readReg64 .x2) ⟨by omega, by bv_omega⟩
    exact (hA.readBytes_eq hd (by omega)).trans hokm

theorem iter_a1_96_x_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hrem : rem = 64 ∨ rem = 32) (hdst : dstOff ≤ 96)
    (hx : StateLoopX b infoPtr info.length 96 tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopA1X b F prk tPrev okmSoFar infoPtr info.length 96 i rem dstOff s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq; have hx27 := hx.common.x27_eq; have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq; have hx22 := hx.x22_eq; have hx24 := hx.x24_eq
  have hx26 := hx.x26_eq; have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned; have hrw := hpre.rw_esp hx.common.frame
  have hread_x0 := hpre.readable_x0 hx.common.frame
  rcases hpre.toExpandPre96_46.read64_x0_write64_esp with ⟨h_x0_w0, h_x0_w⟩
  have hpos_x0 : s.mem.read8 (s₀.readReg64 .x0 + 63#64) = 0#8 :=
    (hpre.hmac_x0 hx.common.frame).2.2.1
  iterate 26 s2_step
  refine RunsTo.refl ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc],
    ExpandCommonX.of_agreesOutside_low32 (off := 64#64) (sz := 256) hx.common hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx19],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm];
       rcases hrem with rfl | rfl <;> rfl,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx24],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_, ?_⟩
  · simp only [Expand.mem_setMem]
    refine HmacSt.of_copy_empty_esp_64 (hpre.hmac_x0 hx.common.frame)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w]
  · dsimp only [Expand.mem_setMem]
    exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 256
      (by unfold DisjointRegions; bv_omega) (by prove_agrees_esp) (by decide) hx.t_cache
  · rw [Expand.mem_setMem]
    exact okm_of_agreesOutside_esp 64#64 256 dstOff hpre ⟨by decide, by decide⟩ hdst
      (by prove_agrees_esp) hx.okm_pre

theorem iter_a2_96_x_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32) (hrem : rem = 64 ∨ rem = 32) (hdst : dstOff ≤ 96)
    (hx : StateLoopA1X b F prk tPrev okmSoFar infoPtr info.length 96 i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopA2_96X b F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  have hmin : min rem 32 = 32 := by rcases hrem with rfl | rfl <;> rfl
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq; have hx27 := hx.common.x27_eq; have hx20 := hx.common.x20_eq
  have hm8 := hx.common.m8_eq; have hm16 := hx.common.m16_eq; have hx8 := hx.x8_eq
  have hx19 := hx.x19_eq; have hx22 := hx.x22_eq
  have hx23 : s.readReg64 .x23 = 32#64 := by rw [hx.x23_eq, hmin]
  have hx24 := hx.x24_eq; have hx26 := hx.x26_eq; have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned; have hrw := hpre.rw_esp hx.common.frame
  have hread_x1 := hpre.readable_x1 hx.common.frame
  rcases hpre.toExpandPre96_46.read64_x1_write_esp with ⟨h_x1_w0, h_x1_w8, h_x1_w8_0, h_x1_w8_8⟩
  have hx1_val0 := hpre.info_ptr_eq hx.common.frame
  have hx1_val8 := hpre.info_len_eq_46 hx.common.frame
  iterate 19 s2_step
  refine RunsTo.refl ⟨rfl,
    ExpandPre96_46X.common_of_write64_esp0_and_low64 hx.common hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) rfl,
    rfl, rfl, rfl, rfl, hx19, hx22, hx23, hx26, rfl,
    by simp (config := { decide := true }) only [arm64_norm], ?_, ?_⟩
  · simp only [Expand.mem_setMem]
    refine HmacSt.of_write32_empty hx.hmac_64 hx.t_cache ht_len
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm]
  · rw [Expand.mem_setMem]
    refine okm_of_agreesOutside_esp 0#64 8 dstOff hpre ⟨by decide, by decide⟩ hdst
      (by rw [BitVec.add_zero]
          exact (AgreesOutside.rfl' _ (esp s₀) 8).write64 (by bv_omega) (by decide)) ?_
    exact okm_of_agreesOutside_esp 64#64 64 dstOff hpre ⟨by decide, by decide⟩ hdst
      (by prove_agrees_esp) hx.okm_pre

theorem iter_b1_96_tail_x_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s₁ : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀) (hdst : dstOff ≤ 96)
    (hpc₁ : s₁.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 892))
    (hc1 : ExpandCommonX infoPtr info.length 96 s₀ s₁)
    (hx19 : s₁.readReg64 .x19 = BitVec.ofNat 64 i)
    (hx22 : s₁.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
    (hx23 : s₁.readReg64 .x23 = 32#64) (hx26 : s₁.readReg64 .x26 = BitVec.ofNat 64 rem)
    (hx28 : s₁.readReg64 .x28 = 14#64) (hm0 : s₁.mem.read64 (esp s₀) = infoPtr + 32#64)
    (hblk : s₁.mem.readBytes (esp s₀ + 64#64) 64 = tPrev ++ info.take 32)
    (hist : s₁.mem.readBytes (esp s₀ + 128#64) 32 = shaStateBytes (hmacInnerInit F prk))
    (hcnt1 : s₁.mem.read64 (esp s₀ + 160#64) = 1#64)
    (host : s₁.mem.readBytes (esp s₀ + 168#64) 32 = shaStateBytes (hmacOuterInit F prk))
    (hcnt2 : s₁.mem.read64 (esp s₀ + 200#64) = 1#64)
    (hokm : s₁.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar) :
    RunsTo (tripleRatchetProgAtExt b ext) s₁
      (StateLoopB1_96X b F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  have hrun := hc1.status; have hsp := hc1.sp_eq; have hx29 := hc1.x29_eq
  have hx27 := hc1.x27_eq; have hx20 := hc1.x20_eq
  have hesp := esp_aligned hpre.sp_aligned; have hrw_wb := hpre.rw_esp hc1.frame
  have hx27_96 : esp s₀ + 64#64 + 96#64 = esp s₀ + 160#64 := by bv_lin
  have hx27_64 : esp s₀ + 64#64 + 64#64 = esp s₀ + 128#64 := by bv_lin
  iterate 7 s2_step
  have hA2 : AgreesOutside s₁.mem (s₁.mem.write64 (esp s₀ + 160#64) 2#64) (esp s₀ + 160#64) 8 :=
    agreesOutside_esp_write64 (AgreesOutside.rfl' _ _ _) (by decide)
  have hokm_m2 :
      (s₁.mem.write64 (esp s₀ + 160#64) 2#64).readBytes (s₀.readReg64 .x2) dstOff = okmSoFar :=
    okm_of_agreesOutside_esp 160#64 8 dstOff hpre ⟨by decide, by decide⟩ hdst hA2 hokm
  refine RunsTo.refl ⟨by simp (config := { decide := true }) only [arm64_norm, hpc₁],
    ExpandCommonX.of_agreesOutside_low32 (off := 160#64) (sz := 8) hc1
      (by simp only [arm64_norm, hrun])
      (by simp (config := { decide := true }) only [arm64_norm, hsp])
      (by simp (config := { decide := true }) only [arm64_norm, hx29])
      (by simp (config := { decide := true }) only [arm64_norm, hx27])
      (by simp (config := { decide := true }) only [arm64_norm, hx20])
      (by simp only [arm64_norm]; exact hA2) (by decide),
    by simp (config := { decide := true }) only [arm64_norm, hpc₁],
    by simp (config := { decide := true }) only [arm64_norm, hx27_64],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hx19],
    by simp (config := { decide := true }) only [arm64_norm, hx22],
    by simp (config := { decide := true }) only [arm64_norm, hx23],
    by simp (config := { decide := true }) only [arm64_norm, hx26],
    by simp (config := { decide := true }) only [arm64_norm, hx28],
    by simpa only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, Expand.mem_setMem]
       using (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans hm0,
    by simpa only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, Expand.mem_setMem]
       using (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans hblk,
    by simpa only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, Expand.mem_setMem]
       using (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans hist,
    by simp (config := { decide := true }) only [State.mem_setPC, State.mem_advancePC,
       State.mem_writeReg64, Expand.mem_setMem, arm64_norm],
    by simpa only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, Expand.mem_setMem]
       using (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans host,
    by simpa only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, Expand.mem_setMem]
       using (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans hcnt2,
    by simpa only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, Expand.mem_setMem]
       using hokm_m2⟩

theorem iter_b1_96_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32) (hdst : dstOff ≤ 96)
    (hx : StateLoopA2_96X b F prk info tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s
      (StateLoopB1_96X b F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  have hlen46 := hpre.info_len_eq; have hrw_esp := hpre.rw_esp hx.common.frame
  have hread_info := hpre.readable_info hx.common.frame
  have htake_len : (info.take 32).length = 32 := by simp [hlen46]
  have hread_info32 : s.mem.readBytes infoPtr 32 = info.take 32 := by
    simpa using Bytes.readBytes_slice_of_readBytes_eq s.mem infoPtr info
      (hpre.info_bytes_eq hx.common.frame) 0 32 (by rw [hlen46]; decide)
  have hin_sub : ∀ a, InRegion infoPtr 32 a → InRegion infoPtr info.length a := by
    intro a ha; simp only [InRegion] at ha ⊢; bv_omega
  refine (memcpyRO_stub_runsTo hS.memcpyRO (bs := info.take 32)
    hx.pc_eq hx.common.status hx.x0_eq hx.x1_eq
    (by rw [hx.x2_eq, htake_len]; rfl) (by rw [htake_len]; decide)
    (by rw [htake_len]; exact hread_info32) (by rw [htake_len]; exact hrw_esp.sub (by bv_omega))
    (by rw [htake_len]; exact readable_sub hread_info (by bv_omega))
    (hpre.rw_extStack hx.common.frame hx.common.sp_eq)
    (by rw [htake_len]; exact ExpandPre96_46X.disj_esp_extStack hx.common.sp_eq ⟨by decide, by decide⟩)
    (fun a ha => hpre.out_info_esp_off (by rw [htake_len]; decide) a (hin_sub a (htake_len ▸ ha)))
    (by rw [hx.common.sp_eq]; exact fun a ha => hpre.out_info_extStack a (hin_sub a (htake_len ▸ ha)))
    (by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned)).trans
    fun s₁ ⟨hpc₁, hstat₁, hcc₁, _, hdst₁, _, hfr_mc⟩ => ?_
  rw [hx.common.sp_eq, htake_len] at hfr_mc; rw [htake_len] at hdst₁
  have hfr_ro : S2FrameRO infoPtr info.length s.mem s₁.mem
      [(esp s₀ + 96#64, 32), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    S2FrameRO_widen_ro hfr_mc (fun a ha => by simp only [OutsideRegion] at ha ⊢; bv_omega)
  have hd_mc : ∀ (off : BitVec 64) (sz : ℕ), 0 < sz → off.toNat + sz ≤ 496 →
      (off.toNat + sz ≤ 96 ∨ 128 ≤ off.toNat) →
      ∀ r ∈ [(esp s₀ + 96#64, 32), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
        DisjointRegions r.1 r.2 (esp s₀ + off) sz := by
    intro off sz hsz0 hoff496 hsep r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold DisjointRegions; bv_omega
    · change DisjointRegions (esp s₀ - 16384#64) 16384 (esp s₀ + off) sz
      unfold DisjointRegions; bv_omega
  have hm0_1 : s₁.mem.read64 (esp s₀) = infoPtr + 32#64 := by
    have h := hfr_ro.read64_eq (hrw_esp.sub (by bv_omega))
      (hd_mc 0#64 8 (by decide) (by decide) (Or.inl (by decide)))
    rw [BitVec.add_zero] at h; exact h.trans hx.m0_eq
  have htprev_1 : s₁.mem.readBytes (esp s₀ + 64#64) 32 = tPrev :=
    (hfr_ro.readBytes_eq (hrw_esp.sub (by bv_omega))
      (hd_mc 64#64 32 (by decide) (by decide) (Or.inl (by decide))) (by decide)).trans
      (by have h := hx.hmac_64.2.1; rwa [ht_len] at h)
  have hblk_1 : s₁.mem.readBytes (esp s₀ + 64#64) 64 = tPrev ++ info.take 32 := by
    rw [Bytes.readBytes_add s₁.mem (esp s₀ + 64#64) 32 32,
        show esp s₀ + 64#64 + BitVec.ofNat 64 32 = esp s₀ + 96#64 by bv_lin, htprev_1, hdst₁]
  have hist_1 : s₁.mem.readBytes (esp s₀ + 128#64) 32 = shaStateBytes (hmacInnerInit F prk) :=
    (hfr_ro.readBytes_eq (hrw_esp.sub (by bv_omega))
      (hd_mc 128#64 32 (by decide) (by decide) (Or.inr (by decide))) (by decide)).trans
      (by have h := hx.hmac_64.2.2.2.1
          rwa [show esp s₀ + 64#64 + 0x40#64 = esp s₀ + 128#64 by bv_lin] at h)
  have hcnt1_1 : s₁.mem.read64 (esp s₀ + 160#64) = 1#64 :=
    (hfr_ro.read64_eq (hrw_esp.sub (by bv_omega))
      (hd_mc 160#64 8 (by decide) (by decide) (Or.inr (by decide)))).trans
      (by have h := hx.hmac_64.2.2.2.2.1
          rwa [show esp s₀ + 64#64 + 0x60#64 = esp s₀ + 160#64 by bv_lin] at h)
  have host_1 : s₁.mem.readBytes (esp s₀ + 168#64) 32 = shaStateBytes (hmacOuterInit F prk) :=
    (hfr_ro.readBytes_eq (hrw_esp.sub (by bv_omega))
      (hd_mc 168#64 32 (by decide) (by decide) (Or.inr (by decide))) (by decide)).trans
      (by have h := hx.hmac_64.2.2.2.2.2.1
          rwa [show esp s₀ + 64#64 + 0x68#64 = esp s₀ + 168#64 by bv_lin] at h)
  have hcnt2_1 : s₁.mem.read64 (esp s₀ + 200#64) = 1#64 :=
    (hfr_ro.read64_eq (hrw_esp.sub (by bv_omega))
      (hd_mc 200#64 8 (by decide) (by decide) (Or.inr (by decide)))).trans
      (by have h := hx.hmac_64.2.2.2.2.2.2
          rwa [show esp s₀ + 64#64 + 0x88#64 = esp s₀ + 200#64 by bv_lin] at h)
  exact runsTo_toE (iter_b1_96_tail_x_runsTo hpre hdst (hpc₁.trans hx.lr_eq)
    (hpre.common_of_s2frameRO_esp hx.common ⟨by decide, by decide⟩ hstat₁ hcc₁ hfr_ro)
    ((Extract.CallingConventionPreserved.x19 hcc₁).trans hx.x19_eq)
    ((Extract.CallingConventionPreserved.x22 hcc₁).trans hx.x22_eq)
    ((CallingConventionPreserved.x23 hcc₁).trans hx.x23_eq)
    ((CallingConventionPreserved.x26 hcc₁).trans hx.x26_eq)
    ((CallingConventionPreserved.x28 hcc₁).trans hx.x28_eq)
    hm0_1 hblk_1 hist_1 hcnt1_1 host_1 hcnt2_1
    (hpre.okm_of_s2frameRO_esp hx.common.frame ⟨by decide, by decide⟩ hdst hfr_ro hx.okm_pre))

theorem iter_b2_96_tail_x_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s₁ : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀) (hdst : dstOff ≤ 96)
    (hpc₁ : s₁.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 920))
    (hc1 : ExpandCommonX infoPtr info.length 96 s₀ s₁)
    (hx19 : s₁.readReg64 .x19 = BitVec.ofNat 64 i)
    (hx22 : s₁.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
    (hx23 : s₁.readReg64 .x23 = 32#64) (hx26 : s₁.readReg64 .x26 = BitVec.ofNat 64 rem)
    (hx28 : s₁.readReg64 .x28 = 14#64) (hm0 : s₁.mem.read64 (esp s₀) = infoPtr + 32#64)
    (hist : s₁.mem.readBytes (esp s₀ + 128#64) 32 =
              shaStateBytes (F (hmacInnerInit F prk) (tPrev ++ info.take 32)))
    (hcnt1 : s₁.mem.read64 (esp s₀ + 160#64) = 2#64)
    (host : s₁.mem.readBytes (esp s₀ + 168#64) 32 = shaStateBytes (hmacOuterInit F prk))
    (hcnt2 : s₁.mem.read64 (esp s₀ + 200#64) = 1#64)
    (hokm : s₁.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar) :
    RunsTo (tripleRatchetProgAtExt b ext) s₁
      (StateLoopB2_96X b F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  have hrun := hc1.status; have hsp := hc1.sp_eq; have hx29 := hc1.x29_eq
  have hx27 := hc1.x27_eq; have hx20 := hc1.x20_eq
  have hesp := esp_aligned hpre.sp_aligned; have hrw_wb := hpre.rw_esp hc1.frame
  iterate 11 s2_step
  have hA2 : AgreesOutside s₁.mem
      ((s₁.mem.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8)
      (esp s₀ + 127#64) 1 :=
    agreesOutside_esp_write8 (agreesOutside_esp_write8 (AgreesOutside.rfl' _ _ _) (by decide))
      (by decide)
  have hokm_m2 : ((s₁.mem.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).readBytes
      (s₀.readReg64 .x2) dstOff = okmSoFar :=
    okm_of_agreesOutside_esp 127#64 1 dstOff hpre ⟨by decide, by decide⟩ hdst hA2 hokm
  refine RunsTo.refl ⟨by simp (config := { decide := true }) only [arm64_norm, hpc₁],
    ExpandCommonX.of_agreesOutside_low32 (off := 127#64) (sz := 1) hc1
      (by simp only [arm64_norm, hrun])
      (by simp (config := { decide := true }) only [arm64_norm, hsp])
      (by simp (config := { decide := true }) only [arm64_norm, hx29])
      (by simp (config := { decide := true }) only [arm64_norm, hx27])
      (by simp (config := { decide := true }) only [arm64_norm, hx20])
      (by simp only [arm64_norm]; exact hA2) (by decide),
    by simp (config := { decide := true }) only [arm64_norm, hpc₁],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hx19],
    by simp (config := { decide := true }) only [arm64_norm, hx22],
    by simp (config := { decide := true }) only [arm64_norm, hx23],
    by simp (config := { decide := true }) only [arm64_norm, hx26],
    by simpa only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, Expand.mem_setMem]
       using Memory.read8_write8_same _ _ _,
    by simpa only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, Expand.mem_setMem]
       using (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans hist,
    by simpa only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, Expand.mem_setMem]
       using (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans hcnt1,
    by simpa only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, Expand.mem_setMem]
       using (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans host,
    by simpa only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, Expand.mem_setMem]
       using (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans hcnt2,
    by simpa only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, Expand.mem_setMem]
       using hokm_m2⟩

theorem iter_b2_96_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32) (hdst : dstOff ≤ 96)
    (hx : StateLoopB1_96X b F prk info tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s
      (StateLoopB2_96X b F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  have hrw_esp := hpre.rw_esp hx.common.frame
  refine (compress256_one_stub_runsTo hS.compress256 (by decide)
    hx.pc_eq hx.common.status hx.x0_eq hx.x1_eq hx.x2_eq
    hx.ist_128 hx.blk_64 (hrw_esp.sub (by bv_omega)) (hrw_esp.sub (by bv_omega))
    (hpre.rw_extStack hx.common.frame hx.common.sp_eq)
    (by unfold DisjointRegions; bv_omega)
    (ExpandPre96_46X.disj_esp_extStack hx.common.sp_eq ⟨by decide, by decide⟩)
    (ExpandPre96_46X.disj_esp_extStack hx.common.sp_eq ⟨by decide, by decide⟩)
    (by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned)).trans
    fun s₁ ⟨hpc₁, hstat₁, hcc₁, hist₁, _, hfr_cp⟩ => ?_
  rw [hx.common.sp_eq] at hfr_cp
  have hd_cp : ∀ (off : BitVec 64) (sz : ℕ), 0 < sz → off.toNat + sz ≤ 496 →
      (off.toNat + sz ≤ 128 ∨ 160 ≤ off.toNat) →
      ∀ r ∈ [(esp s₀ + 128#64, 32), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
        DisjointRegions r.1 r.2 (esp s₀ + off) sz := by
    intro off sz hsz0 hoff496 hsep r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold DisjointRegions; bv_omega
    · change DisjointRegions (esp s₀ - 16384#64) 16384 (esp s₀ + off) sz
      unfold DisjointRegions; bv_omega
  have hm0_1 : s₁.mem.read64 (esp s₀) = infoPtr + 32#64 := by
    have h := hfr_cp.read64_eq (hrw_esp.sub (by bv_omega))
      (hd_cp 0#64 8 (by decide) (by decide) (Or.inl (by decide)))
    rw [BitVec.add_zero] at h; exact h.trans hx.m0_eq
  exact runsTo_toE (iter_b2_96_tail_x_runsTo hpre hdst (hpc₁.trans hx.lr_eq)
    (hpre.common_of_s2frame_esp hx.common ⟨by decide, by decide⟩ hstat₁ hcc₁ hfr_cp)
    ((Extract.CallingConventionPreserved.x19 hcc₁).trans hx.x19_eq)
    ((Extract.CallingConventionPreserved.x22 hcc₁).trans hx.x22_eq)
    ((CallingConventionPreserved.x23 hcc₁).trans hx.x23_eq)
    ((CallingConventionPreserved.x26 hcc₁).trans hx.x26_eq)
    ((CallingConventionPreserved.x28 hcc₁).trans hx.x28_eq)
    hm0_1 hist₁
    ((hfr_cp.read64_eq (hrw_esp.sub (by bv_omega))
      (hd_cp 160#64 8 (by decide) (by decide) (Or.inr (by decide)))).trans hx.cnt1_160)
    ((hfr_cp.readBytes_eq (hrw_esp.sub (by bv_omega))
      (hd_cp 168#64 32 (by decide) (by decide) (Or.inr (by decide))) (by decide)).trans hx.ost_168)
    ((hfr_cp.read64_eq (hrw_esp.sub (by bv_omega))
      (hd_cp 200#64 8 (by decide) (by decide) (Or.inr (by decide)))).trans hx.cnt2_200)
    (hpre.okm_of_s2frameRO_esp hx.common.frame ⟨by decide, by decide⟩ hdst
      (S2FrameRO.of_s2frame hfr_cp) hx.okm_pre))

theorem iter_b3_96_tail_x_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s₁ : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32) (hi : i = 1 ∨ i = 2) (hdst : dstOff ≤ 96)
    (hpc₁ : s₁.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 988))
    (hc1 : ExpandCommonX infoPtr info.length 96 s₀ s₁)
    (hx19 : s₁.readReg64 .x19 = BitVec.ofNat 64 i)
    (hx22 : s₁.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
    (hx23 : s₁.readReg64 .x23 = 32#64) (hx26 : s₁.readReg64 .x26 = BitVec.ofNat 64 rem)
    (hdrop : s₁.mem.readBytes (esp s₀ + 64#64) 14 = info.drop 32)
    (hpos : s₁.mem.read8 (esp s₀ + 127#64) = 14#8)
    (hist : s₁.mem.readBytes (esp s₀ + 128#64) 32 =
              shaStateBytes (F (hmacInnerInit F prk) (tPrev ++ info.take 32)))
    (hcnt1 : s₁.mem.read64 (esp s₀ + 160#64) = 2#64)
    (host : s₁.mem.readBytes (esp s₀ + 168#64) 32 = shaStateBytes (hmacOuterInit F prk))
    (hcnt2 : s₁.mem.read64 (esp s₀ + 200#64) = 1#64)
    (hokm : s₁.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar) :
    RunsTo (tripleRatchetProgAtExt b ext) s₁
      (StateLoopB_96X b F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  have hrun := hc1.status; have hsp := hc1.sp_eq; have hx29 := hc1.x29_eq
  have hx27 := hc1.x27_eq; have hx20 := hc1.x20_eq
  have hesp := esp_aligned hpre.sp_aligned; have hrw_wb := hpre.rw_esp hc1.frame
  have hi_eq : (BitVec.ofNat 64 i == 255#64) = false := by rcases hi with rfl | rfl <;> rfl
  have hi_ne : (BitVec.ofNat 64 i != 255#64) = true := by rcases hi with rfl | rfl <;> rfl
  have hi_cmp : (AddWithCarry64 (BitVec.ofNat 64 i) (bv% (2 ^ 64 - 256)) true).2.z = false := by
    rcases hi with rfl | rfl <;> rfl
  have hi_add1 : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 i) + 1#32) =
      BitVec.ofNat 64 (i + 1) := by rcases hi with rfl | rfl <;> rfl
  iterate 14 s2_step
  let c := BitVec.ofNat 8 (i + 1)
  have hA2 : AgreesOutside s₁.mem
      (((s₁.mem.write8 (esp s₀ + 240#64) c).write8 (esp s₀ + 78#64) c).write8 (esp s₀ + 127#64) 15#8)
      (esp s₀ + 64#64) 177 :=
    agreesOutside_esp_write8 (agreesOutside_esp_write8
      (agreesOutside_esp_write8 (AgreesOutside.rfl' _ _ _) (by decide)) (by decide)) (by decide)
  refine RunsTo.refl ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc₁],
    ExpandCommonX.of_agreesOutside_low32 (off := 64#64) (sz := 177) hc1
      (by rw [State.status_setMem]; simp only [arm64_norm, hrun])
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by simp only [arm64_norm]; exact hA2) (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx19],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ?_, ?_⟩
  · rw [Expand.mem_setMem]
    exact hmacStGen_of_counter_writes_14 ht_len hpre.info_len_eq hdrop hist hcnt1 host hcnt2
  · rw [Expand.mem_setMem]
    exact okm_of_agreesOutside_esp 64#64 177 dstOff hpre ⟨by decide, by decide⟩ hdst hA2 hokm

theorem iter_b3_96_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32) (hi : i = 1 ∨ i = 2) (hdst : dstOff ≤ 96)
    (hx : StateLoopB2_96X b F prk info tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s
      (StateLoopB_96X b F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  have hlen46 := hpre.info_len_eq; have hrw_esp := hpre.rw_esp hx.common.frame
  have hread_info := hpre.readable_info hx.common.frame
  have hdrop_len : (info.drop 32).length = 14 := by simp [hlen46]
  have hread_info14 : s.mem.readBytes (infoPtr + 32#64) 14 = info.drop 32 :=
    (Bytes.readBytes_slice_of_readBytes_eq s.mem infoPtr info
      (hpre.info_bytes_eq hx.common.frame) 32 14 (by rw [hlen46])).trans
      (List.take_of_length_le (by rw [hdrop_len]))
  have hin_sub : ∀ a, InRegion (infoPtr + 32#64) 14 a → InRegion infoPtr info.length a := by
    intro a ha; simp only [InRegion] at ha ⊢; bv_omega
  refine (memcpyRO_stub_runsTo hS.memcpyRO (bs := info.drop 32)
    hx.pc_eq hx.common.status hx.x0_eq hx.x1_eq
    (by rw [hx.x2_eq, hdrop_len]; rfl) (by rw [hdrop_len]; decide)
    (by rw [hdrop_len]; exact hread_info14) (by rw [hdrop_len]; exact hrw_esp.sub (by bv_omega))
    (by rw [hdrop_len]; exact readable_sub hread_info (by bv_omega))
    (hpre.rw_extStack hx.common.frame hx.common.sp_eq)
    (by rw [hdrop_len]; exact ExpandPre96_46X.disj_esp_extStack hx.common.sp_eq ⟨by decide, by decide⟩)
    (fun a ha => hpre.out_info_esp_off (by rw [hdrop_len]; decide) a (hin_sub a (hdrop_len ▸ ha)))
    (by rw [hx.common.sp_eq]; exact fun a ha => hpre.out_info_extStack a (hin_sub a (hdrop_len ▸ ha)))
    (by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned)).trans
    fun s₁ ⟨hpc₁, hstat₁, hcc₁, _, hdst₁, _, hfr_mc⟩ => ?_
  rw [hx.common.sp_eq, hdrop_len] at hfr_mc; rw [hdrop_len] at hdst₁
  have hfr_ro : S2FrameRO infoPtr info.length s.mem s₁.mem
      [(esp s₀ + 64#64, 14), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] :=
    S2FrameRO_widen_ro hfr_mc (fun a ha => by simp only [OutsideRegion] at ha ⊢; bv_omega)
  have hd_mc : ∀ (off : BitVec 64) (sz : ℕ), 0 < sz → 127 ≤ off.toNat → off.toNat + sz ≤ 496 →
      ∀ r ∈ [(esp s₀ + 64#64, 14), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
        DisjointRegions r.1 r.2 (esp s₀ + off) sz := by
    intro off sz hsz0 h127 hoff496 r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold DisjointRegions; bv_omega
    · change DisjointRegions (esp s₀ - 16384#64) 16384 (esp s₀ + off) sz
      unfold DisjointRegions; bv_omega
  have hpos_1 : s₁.mem.read8 (esp s₀ + 127#64) = 14#8 := by
    refine (hfr_ro.1 (esp s₀ + 127#64) (hrw_esp.readable _ (by unfold InRegion; bv_omega)).1
      (hrw_esp.readable _ (by unfold InRegion; bv_omega)).2
      (fun r hr => ?_)).trans hx.pos_127
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl
    · unfold OutsideRegion; bv_omega
    · change OutsideRegion (esp s₀ - 16384#64) 16384 (esp s₀ + 127#64)
      unfold OutsideRegion; bv_omega
  exact runsTo_toE (iter_b3_96_tail_x_runsTo hpre ht_len hi hdst (hpc₁.trans hx.lr_eq)
    (hpre.common_of_s2frameRO_esp hx.common ⟨by decide, by decide⟩ hstat₁ hcc₁ hfr_ro)
    ((Extract.CallingConventionPreserved.x19 hcc₁).trans hx.x19_eq)
    ((Extract.CallingConventionPreserved.x22 hcc₁).trans hx.x22_eq)
    ((CallingConventionPreserved.x23 hcc₁).trans hx.x23_eq)
    ((CallingConventionPreserved.x26 hcc₁).trans hx.x26_eq)
    hdst₁ hpos_1
    ((hfr_ro.readBytes_eq (hrw_esp.sub (by bv_omega))
      (hd_mc 128#64 32 (by decide) (by decide) (by decide)) (by decide)).trans hx.ist_128)
    ((hfr_ro.read64_eq (hrw_esp.sub (by bv_omega))
      (hd_mc 160#64 8 (by decide) (by decide) (by decide))).trans hx.cnt1_160)
    ((hfr_ro.readBytes_eq (hrw_esp.sub (by bv_omega))
      (hd_mc 168#64 32 (by decide) (by decide) (by decide)) (by decide)).trans hx.ost_168)
    ((hfr_ro.read64_eq (hrw_esp.sub (by bv_omega))
      (hd_mc 200#64 8 (by decide) (by decide) (by decide))).trans hx.cnt2_200)
    (hpre.okm_of_s2frameRO_esp hx.common.frame ⟨by decide, by decide⟩ hdst hfr_ro hx.okm_pre))

theorem iter_c_96_x_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hrem : rem = 64 ∨ rem = 32) (hdst : dstOff ≤ 96)
    (hx : StateLoopB_96X b F prk info tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopC_96X b F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq; have hx27 := hx.common.x27_eq; have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq; have hx22 := hx.x22_eq; have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq; have hx26 := hx.x26_eq; have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned; have hrw := hpre.rw_esp hx.common.frame
  iterate 17 s2_step
  refine RunsTo.refl ⟨rfl,
    ExpandCommonX.of_agreesOutside_low32 (off := 240#64) (sz := 0x90) hx.common
      hrun hsp hx29 hx27 hx20 (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl, hx19, by rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl, hx22, hx23, hx24,
    by rcases hrem with rfl | rfl <;> rfl, hx28, ?_, ?_⟩
  · simp only [Expand.mem_setMem]
    refine HmacStGen.of_copy_esp_64_240 hx.hmac_64
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm]
  · rw [Expand.mem_setMem]
    exact okm_of_agreesOutside_esp 240#64 0x90 dstOff hpre ⟨by decide, by decide⟩ hdst
      (by prove_agrees_esp) hx.okm_pre

theorem iter_fin_96_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hrem : rem = 64 ∨ rem = 32) (hdst : dstOff ≤ 96)
    (hx : StateLoopC_96X b F prk info tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s
      (StateLoopFinX b F prk info tPrev okmSoFar infoPtr 96 i rem dstOff s₀) := by
  have hmin : min rem 32 = 32 := by rcases hrem with rfl | rfl <;> rfl
  rcases hpre.fin_side_conditions_x hx.common.frame with
    ⟨hrw_out, hrw_hm, hrw_sp, hd_out_hm, hd_out_sp, hd_hm_sp⟩
  have hrw_x2 := hpre.rw_x2_frame hx.common.frame
  refine (finalize_fixed_gen_runsToE_base
    (memsetStep_of_stubs hS) (compressOneStep_of_stubs hS)
    hx.pc_eq hx.common.status hx.x0_eq hx.x1_eq hpre.prk_le (by simp [hpre.info_len_eq])
    hx.hmac_240 hrw_out hrw_hm (by rw [hx.common.sp_eq]; exact hrw_sp) hd_out_hm
    (by rw [hx.common.sp_eq]; exact hd_out_sp) (by rw [hx.common.sp_eq]; exact hd_hm_sp)
    (by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned)).mono
    fun s' ⟨hpc', hstat', hcc, ht, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.common.sp_eq] at hfr
  rw [List.append_assoc, ← List.append_assoc (info.take 32),
      List.take_append_drop, ← List.append_assoc] at ht
  have hokm' : s'.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · refine (hfr.readBytes_eq (hrw_x2.sub (by bv_omega)) (fun r hr => ?_) (by omega)).trans hx.okm_pre
      have hd_stk : DisjointRegions (s₀.sp - 17024#64) 17024 (s₀.readReg64 .x2) dstOff :=
        hpre.disj_x2_stack.symm.sub_right (s₀.readReg64 .x2) ⟨by omega, by bv_omega⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact hd_stk.sub_left _ ⟨by simp, by unfold esp; bv_omega⟩
  exact ⟨hpc', hpre.common_of_fin_frame_x hx.common hstat' hcc hfr,
    (Extract.CallingConventionPreserved.x19 hcc).trans hx.x19_eq,
    (Extract.CallingConventionPreserved.x21 hcc).trans (by rw [hmin]; exact hx.x21_eq),
    (Extract.CallingConventionPreserved.x22 hcc).trans hx.x22_eq,
    (CallingConventionPreserved.x23 hcc).trans (by rw [hmin]; exact hx.x23_eq),
    (CallingConventionPreserved.x24 hcc).trans hx.x24_eq,
    (CallingConventionPreserved.x26 hcc).trans (by rw [hmin]; exact hx.x26_eq),
    (CallingConventionPreserved.x28 hcc).trans hx.x28_eq, ht, hokm'⟩

theorem iter_d_96_head_x_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hx : StateLoopFinX b F prk info tPrev okmSoFar infoPtr 96 i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s_mc =>
      s_mc.pc = b + bv% (ls_off% "memcpy") ∧
      ExpandCommonX infoPtr info.length 96 s₀ s_mc ∧
      s_mc.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 688) ∧
      s_mc.readReg64 .x0 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff ∧
      s_mc.readReg64 .x1 = esp s₀ + 208#64 ∧
      s_mc.readReg64 .x2 = BitVec.ofNat 64 (min rem 32) ∧
      s_mc.readReg64 .x19 = BitVec.ofNat 64 i ∧
      s_mc.readReg64 .x21 = s₀.readReg64 .x2 + BitVec.ofNat 64 (dstOff + min rem 32) ∧
      s_mc.readReg64 .x24 = 64#64 ∧
      s_mc.readReg64 .x26 = BitVec.ofNat 64 (rem - min rem 32) ∧
      s_mc.readReg64 .x28 = esp s₀ + 64#64 ∧ s_mc.mem = s.mem) := by
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq; have hx27 := hx.common.x27_eq; have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq; have hx21 := hx.x21_eq; have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq; have hx24 := hx.x24_eq; have hx26 := hx.x26_eq; have hx28 := hx.x28_eq
  iterate 4 s2_step
  exact RunsTo.refl ⟨rfl, ⟨hrun, hsp, hx29, hx27, hx20, hx.common.m8_eq, hx.common.m16_eq,
    hx.common.saved, hx.common.frame⟩, rfl, rfl, rfl, rfl, hx19, hx21, hx24, hx26, hx28, rfl⟩

theorem iter_d_continue_96_tail_x_runsTo
    {prk info okmSoFar tNext : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s₁ : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hpc₁ : s₁.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 688))
    (hc1 : ExpandCommonX infoPtr info.length 96 s₀ s₁)
    (hx19 : s₁.readReg64 .x19 = 1#64) (hx21 : s₁.readReg64 .x21 = s₀.readReg64 .x2 + 64#64)
    (hx24 : s₁.readReg64 .x24 = 64#64) (hx26 : s₁.readReg64 .x26 = 32#64)
    (hx28 : s₁.readReg64 .x28 = esp s₀ + 64#64)
    (ht_208 : s₁.mem.readBytes (esp s₀ + 208#64) 32 = tNext)
    (hokm_next : s₁.mem.readBytes (s₀.readReg64 .x2) 64 = okmSoFar ++ tNext) :
    RunsTo (tripleRatchetProgAtExt b ext) s₁
      (StateLoopX b infoPtr info.length 96 tNext (okmSoFar ++ tNext) 2 32 64 s₀) := by
  have hrun := hc1.status; have hsp := hc1.sp_eq; have hx29 := hc1.x29_eq
  have hx27 := hc1.x27_eq; have hx20 := hc1.x20_eq; have hm16_1 := hc1.m16_eq
  have hesp := esp_aligned hpre.sp_aligned; have hrw1_esp := hpre.rw_esp hc1.frame
  iterate 6 s2_step
  refine RunsTo.refl ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc₁],
    ExpandCommonX.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx21],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx24],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_⟩
  · simp only [Expand.mem_setMem]
    refine readBytes_32_esp_32_of_208 ht_208 ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm]
  · rw [Expand.mem_setMem]
    exact okm_of_agreesOutside_esp 32#64 32 64 hpre ⟨by decide, by decide⟩ (by decide)
      (by prove_agrees_esp) hokm_next

theorem iter_d_continue_96_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info tPrev okmSoFar tNext : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (htNext : tNext = hmacWith F prk (tPrev ++ info ++ [2#8]))
    (hx : StateLoopFinX b F prk info tPrev okmSoFar infoPtr 96 1 64 32 s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s
      (StateLoopX b infoPtr info.length 96 tNext (okmSoFar ++ tNext) 2 32 64 s₀) := by
  have ht_208 : s.mem.readBytes (esp s₀ + 208#64) 32 = tNext := htNext ▸ hx.t_208
  have ht_len : tNext.length = 32 := by rw [htNext, length_hmacWith]
  clear htNext
  refine (runsTo_toE (iter_d_96_head_x_runsTo hx)).trans fun s_mc
    ⟨hpc_mc, hc_mc, hlr_mc, hx0_mc, hx1_mc, hx2_mc, hx19_mc, hx21_mc, hx24_mc, hx26_mc, hx28_mc, hmem_mc⟩ => ?_
  refine (memcpy_208_to_x2_runsTo hS hpre (dstOff := 32) (okmSoFar := okmSoFar) (bs := tNext)
    (by decide) ht_len hpc_mc hc_mc hx0_mc hx1_mc hx2_mc
    (by rw [hmem_mc]; exact ht_208) (by rw [hmem_mc]; exact hx.okm_pre)).trans
    fun s₁ ⟨hpc₁, hc1, hcc₁, hsrc₁, hokm_next⟩ => ?_
  exact runsTo_toE (iter_d_continue_96_tail_x_runsTo hpre (hpc₁.trans hlr_mc) hc1
    ((Extract.CallingConventionPreserved.x19 hcc₁).trans hx19_mc)
    ((Extract.CallingConventionPreserved.x21 hcc₁).trans hx21_mc)
    ((CallingConventionPreserved.x24 hcc₁).trans hx24_mc)
    ((CallingConventionPreserved.x26 hcc₁).trans hx26_mc)
    ((CallingConventionPreserved.x28 hcc₁).trans hx28_mc) hsrc₁ hokm_next)

theorem iter_d_done_96_tail_x_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s₁ : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hpc₁ : s₁.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 688))
    (hc1 : ExpandCommonX infoPtr info.length 96 s₀ s₁)
    (hx19 : s₁.readReg64 .x19 = 2#64) (hx21 : s₁.readReg64 .x21 = s₀.readReg64 .x2 + 96#64)
    (hx26 : s₁.readReg64 .x26 = 0#64)
    (hokm_done : s₁.mem.readBytes (s₀.readReg64 .x2) 96 = hkdfExpand F prk info 96) :
    RunsTo (tripleRatchetProgAtExt b ext) s₁ (StateDoneX b F prk info infoPtr 96 s₀) := by
  have hrun := hc1.status; have hsp := hc1.sp_eq; have hx29 := hc1.x29_eq
  have hx27 := hc1.x27_eq; have hx20 := hc1.x20_eq; have hm16_1 := hc1.m16_eq
  have hesp := esp_aligned hpre.sp_aligned; have hrw1_esp := hpre.rw_esp hc1.frame
  iterate 6 s2_step
  refine RunsTo.refl ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc₁],
    ExpandCommonX.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide), ?_⟩
  rw [Expand.mem_setMem]
  exact okm_of_agreesOutside_esp 32#64 32 96 hpre ⟨by decide, by decide⟩ (by decide)
    (by prove_agrees_esp) hokm_done

theorem iter_d_done_96_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hokm : okmSoFar ++ hmacWith F prk (tPrev ++ info ++ [3#8]) = hkdfExpand F prk info 96)
    (hx : StateLoopFinX b F prk info tPrev okmSoFar infoPtr 96 2 32 64 s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s (StateDoneX b F prk info infoPtr 96 s₀) := by
  generalize htNext : hmacWith F prk (tPrev ++ info ++ [3#8]) = tNext
  have ht_208 : s.mem.readBytes (esp s₀ + 208#64) 32 = tNext := htNext ▸ hx.t_208
  have ht_len : tNext.length = 32 := by rw [← htNext, length_hmacWith]
  rw [htNext] at hokm; clear htNext
  refine (runsTo_toE (iter_d_96_head_x_runsTo hx)).trans fun s_mc
    ⟨hpc_mc, hc_mc, hlr_mc, hx0_mc, hx1_mc, hx2_mc, hx19_mc, hx21_mc, _, hx26_mc, _, hmem_mc⟩ => ?_
  refine (memcpy_208_to_x2_runsTo hS hpre (dstOff := 64) (okmSoFar := okmSoFar) (bs := tNext)
    (by decide) ht_len hpc_mc hc_mc hx0_mc hx1_mc hx2_mc
    (by rw [hmem_mc]; exact ht_208) (by rw [hmem_mc]; exact hx.okm_pre)).trans
    fun s₁ ⟨hpc₁, hc1, hcc₁, _, hokm_done⟩ => ?_
  exact runsTo_toE (iter_d_done_96_tail_x_runsTo hpre (hpc₁.trans hlr_mc) hc1
    ((Extract.CallingConventionPreserved.x19 hcc₁).trans hx19_mc)
    ((Extract.CallingConventionPreserved.x21 hcc₁).trans hx21_mc)
    ((CallingConventionPreserved.x26 hcc₁).trans hx26_mc) (hokm_done.trans hokm))

theorem epilogue_96_x_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hx : StateDoneX b F prk info infoPtr 96 s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (ExpandPostX F prk info infoPtr 96 s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  rcases hx.common.saved with ⟨m400, m408, m416, m424, m432, m440, m448, m456, m464, m472, m480, m488⟩
  iterate 8 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl, hrun, ⟨(esp_eq_add s₀).symm, ?_⟩, hx.okm_all, hx.common.frame⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem iter_to_fin_96_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopX b infoPtr info.length 96 tPrev okmSoFar i rem dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s
      (StateLoopFinX b F prk info tPrev okmSoFar infoPtr 96 i rem dstOff s₀) := by
  refine (runsTo_toE (iter_a1_96_x_runsTo hpre hrem hdst hx)).trans fun s1 hs1 => ?_
  refine (runsTo_toE (iter_a2_96_x_runsTo hpre ht_len hrem hdst hs1)).trans fun s2 hs2 => ?_
  refine (iter_b1_96_x_runsTo hS hpre ht_len hdst hs2).trans fun s3 hs3 => ?_
  refine (iter_b2_96_x_runsTo hS hpre ht_len hdst hs3).trans fun s4 hs4 => ?_
  refine (iter_b3_96_x_runsTo hS hpre ht_len hi hdst hs4).trans fun s5 hs5 => ?_
  refine (runsTo_toE (iter_c_96_x_runsTo hpre hrem hdst hs5)).trans fun s6 hs6 => ?_
  exact iter_fin_96_x_runsTo hS hpre hrem hdst hs6

/-- Full `.inImage`-free `RunsToE` assembly for `expand_multi_info` (`okmLen = 96`,
`info.length = 46`, `expandMultiInfoStackExt = 17024` B) on `tripleRatchetProgAtExt b ext`. -/
theorem expand_multi_info_96_46_runsToE_ext (hS : HkdfStubsExt b F ext)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀) :
    RunsToE (tripleRatchetProgAtExt b ext) s₀
      (ExpandPostX F prk info infoPtr 96 s₀) := by
  refine (runsTo_toE (seg0_96_x_runsTo hpre)).trans fun s1 hs1 => ?_
  refine (runsTo_toE (seg1_96_x_runsTo hpre hs1)).trans fun s2 hs2 => ?_
  refine (seg2a_96_x_runsTo hS hpre hs2).trans fun s3 hs3 => ?_
  refine (runsTo_toE (seg2b_96_x_runsTo hpre hs3)).trans fun s4 hs4 => ?_
  refine (fin1_96_x_runsTo hS hpre hs4).trans fun s5 hs5 => ?_
  refine (seg3_96_x_runsTo hS hpre hs5).trans fun s6 hs6 => ?_
  refine (iter_to_fin_96_x_runsTo hS hpre (t1_length F prk info)
    (Or.inl rfl) (Or.inl rfl) (by decide) hs6).trans fun s7 hs7 => ?_
  refine (iter_d_continue_96_x_runsTo hS hpre (tNext := t2 F prk info) rfl hs7).trans fun s8 hs8 => ?_
  refine (iter_to_fin_96_x_runsTo hS hpre (t2_length F prk info)
    (Or.inr rfl) (Or.inr rfl) (by decide) hs8).trans fun s9 hs9 => ?_
  have hokm96 : (t1 F prk info ++ t2 F prk info) ++
      hmacWith F prk (t2 F prk info ++ info ++ [3#8]) =
      hkdfExpand F prk info 96 := by
    rw [show hmacWith F prk (t2 F prk info ++ info ++ [3#8]) = t3 F prk info from rfl,
        hkdfExpand_96_eq]
  refine (iter_d_done_96_x_runsTo hS hpre hokm96 hs9).trans fun s10 hs10 => ?_
  exact runsTo_toE (epilogue_96_x_runsTo hpre hs10)

end Loop

end HkdfLongExt

/-! ## Top-Level `subroutine_ok` Contract -/

open HkdfLongExt

/-- `.inImage`-free `subroutine_ok` for `expand_multi_info` at `okmLen = 96`, `info.length = 46`,
and `expandMultiInfoStackExt = 17024` B on `tripleRatchetProgAtExt b ext` from `HkdfStubsExt`. -/
theorem expand_multi_info_96_46_ok_ext {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hS : HkdfStubsExt b F ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr hkdfExpandMultiInfoSym)
      (expandMultiInfo96_46SpecExt F) := by
  change subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr expandMultiInfoName)
    (expandMultiInfo96_46SpecExt F)
  rw [trExt_fnAddr_expandMultiInfo]
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [expandMultiInfo96_46SpecExt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_len, hokm_len⟩, hsep⟩
  change s0.mem ⊨ (hmacCoreAt F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
      (x.infoA ↦ᵣ x.info) ∗ memRegion x.okmA 96 ∗
      memRegion (s0.sp - 17024#64) 17024) ∗ R at hsep
  have hb_hm := isBlock_hmacCoreAt F x.hkdfA x.prk [] (by decide)
  have hb_hdr0 := IsBlock.pointsTo64 x.infoHdrA x.infoA
  have hb_hdr8 := IsBlock.pointsTo64 (x.infoHdrA + 8#64) 46#64
  have hb_hdr : IsBlock ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64))
      x.infoHdrA 16
      (fun m => m.read64 x.infoHdrA = x.infoA ∧
        m.read64 (x.infoHdrA + 8#64) = 46#64) :=
    hb_hdr0.sepConj hb_hdr8 rfl (by decide)
  have hro_info := IsBlockRO.pointsToBytesRO x.infoA x.info (by omega)
  have hb_okm := IsBlock.memRegion x.okmA 96
  have hb_stk := IsBlock.memRegion (s0.sp - 17024#64) 17024
  let R_inv : SepProp :=
    hmacCoreAt F x.hkdfA x.prk [] ∗
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗ R
  have hsep_okm_stk_ro : s0.mem ⊨ memRegion x.okmA 96 ∗
      (memRegion (s0.sp - 17024#64) 17024 ∗ ((x.infoA ↦ᵣ x.info) ∗ R_inv)) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 17024#64) 17024 ∗
      (memRegion x.okmA 96 ∗ ((x.infoA ↦ᵣ x.info) ∗ R_inv)) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_hm_stk : s0.mem ⊨ hmacCoreAt F x.hkdfA x.prk [] ∗
      (memRegion (s0.sp - 17024#64) 17024 ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA 96 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hm_okm : s0.mem ⊨ hmacCoreAt F x.hkdfA x.prk [] ∗
      (memRegion x.okmA 96 ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 17024#64) 17024 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_stk : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
      (memRegion (s0.sp - 17024#64) 17024 ∗
        (hmacCoreAt F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA 96 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_okm : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
      (memRegion x.okmA 96 ∗
        (hmacCoreAt F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 17024#64) 17024 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion (s0.sp - 17024#64) 17024 ∗
        (hmacCoreAt F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
            (memRegion x.okmA 96 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion x.okmA 96 ∗
        (hmacCoreAt F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
            (memRegion (s0.sp - 17024#64) 17024 ∗ R)))) := by
    ac_nf at hsep ⊢
  have h_exp_pre : ExpandPre96_46X b F x.prk x.info x.infoA s0 :=
    { pc_eq := hpc
      status := hrun
      x3_eq := hx3
      prk_le := hprk_le
      info_len_eq := hinfo_len
      hmac_st := by rw [hx0]; exact hb_hm.read hsep_hm_stk
      info_ptr := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).1
      info_len := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).2
      info_bytes := hro_info.read hsep_info_stk
      read_info := fun a ha => ⟨hro_info.perm_r hsep_info_stk ha, hro_info.isLazyFree_false hsep_info_stk ha⟩
      read_x0 := by rw [hx0]; exact Memory.RW.readable (fun a ha => hb_hm.permNoLazy_rw hsep_hm_stk ha)
      read_x1 := by rw [hx1]; exact Memory.RW.readable (fun a ha => hb_hdr.permNoLazy_rw hsep_hdr_stk ha)
      rw_x2 := by rw [hx2]; exact fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk_ro ha
      rw_stack := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
      disj_x2_stack := by rw [hx2]; exact hb_okm.disjoint hb_stk (by decide) (by decide) hsep_okm_stk_ro
      disj_x0_stack := by rw [hx0]; exact hb_hm.disjoint hb_stk (by decide) (by decide) hsep_hm_stk
      disj_x0_x2 := by rw [hx0, hx2]; exact hb_hm.disjoint hb_okm (by decide) (by decide) hsep_hm_okm
      disj_x1_stack := by rw [hx1]; exact hb_hdr.disjoint hb_stk (by decide) (by decide) hsep_hdr_stk
      disj_x1_x2 := by rw [hx1, hx2]; exact hb_hdr.disjoint hb_okm (by decide) (by decide) hsep_hdr_okm
      out_info_stk := ro_outside_rw_shared_lb hro_info hb_stk hsep_info_stk
      out_info_x2 := by rw [hx2]; exact ro_outside_rw_shared_lb hro_info hb_okm hsep_info_okm
      sp_aligned := by simpa [State.spAligned] using hsp }
  refine (expand_multi_info_96_46_runsToE_ext hS h_exp_pre).to_reaches_pc
    fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_,
    LibsignalTripleRatchet.CallingConventionPreserved_of_calleeSaved hcallee htr⟩
  dsimp only [expandMultiInfo96_46SpecExt]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExpandFrameX at hframe_sf
  rw [hx2] at hokm_sf hframe_sf
  have h_exp_len : (hkdfExpand F x.prk x.info 96).length = 96 := by
    rw [hkdfExpand_96_eq]
    simp [t1_length, t2_length, t3_length]
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ hkdfExpand F x.prk x.info 96) ∗
      (memRegion (s0.sp - 17024#64) 17024 ∗ ((x.infoA ↦ᵣ x.info) ∗ R_inv)) :=
    S2FrameRO.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hro_info hsep_okm_stk_ro hframe_sf
      ⟨by rw [h_exp_len]; decide, by rwa [h_exp_len]⟩ trivial
  change sf.mem ⊨ (hmacCoreAt F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
      (x.infoA ↦ᵣ x.info) ∗ (x.okmA ↦ₛ hkdfExpand F x.prk x.info 96) ∗
      memRegion (s0.sp - 17024#64) 17024) ∗ R
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

end CryptoVerification.E2E.Pqxdh.ResponderCore
