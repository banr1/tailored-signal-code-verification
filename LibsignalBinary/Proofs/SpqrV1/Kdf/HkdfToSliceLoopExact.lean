/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractExact -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon

/-!
# `HookSatExactMemcpy` Siblings of `SpqrV1.Kdf.HkdfToSlice` Loop (`HkdfToSliceLoopExact`, Block `379`)

- **Role:** `Role::Proof` (untrusted proof module outside the TCB; #1255 mc2 Cone 3).
- **Overview:**
  Replaces `h_memcpy : H lsMemcpySym = some memcpyHook` on the 4 Expand-loop `memcpy` segments of
  Block `379` (`iter_a2_placed_runsTo`, `iter_b_placed_runsTo`, `iter_d_continue_placed_runsTo`,
  `iter_d_done_placed_runsTo`) with `(h_mc : HookSatExactMemcpy H lsMemcpySym)` via
  `s2_memcpy_step_placed_429_exact`, keeping all loop cut predicates (`StateLoop`, `StateLoopA1`,
  `StateLoopA2`, `StateLoopC`, `StateLoopFin`, `StateDone`) **100% unchanged**.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceLoopExact

open Arm64 ProofLib
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.HMAC (hmacWith)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPC_379 blkPl_379 blkPl_425 lsmpl lsρ)
open CryptoVerification.LibsignalAesCbc.Run.Bytes
  (readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalSpqrV1 (hkdfExtractBytes)
open CryptoVerification.LibsignalTripleRatchet
  (Frame RunsTo TraceEq TraceEq.advancePC_step TraceEq.refl TraceEq.setMem_step
   TraceEq.setPC_step TraceEq.setPState_step TraceEq.writeReg32_step TraceEq.writeReg64_step
   TraceEq.writeVReg128_step hmacInnerInit hmacOuterInit length_hmacWith lsCompress256Sym lsMemcpySym
   shaStateBytes_length zeroExtend64_truncate32_ofNat64)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (agreesOutside_writeBytes_le and64_255_ofNat64 and_0xffffffffff_ofNat64 cmp32_lt63_lemmas
   cmp_lt64_lemmas mem_setMem writeBytes_readBytes_disj zeroExtend32_ofNat8_eq_truncate32
   zeroExtend64_add1_truncate32_ofNat64 zeroExtend64_and255_truncate32_ofNat64
   zeroExtend64_ofNat8)
open CryptoVerification.SpqrV1.Kdf (HmacStN)
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
  (HCommon HExpCommon HFrame HPre StateDone StateLoop StateLoopA1 StateLoopA2 StateLoopC
   StateLoopFin agreesOutside_hsp_write64 bv_sub_add_lit_ge canWrite_hsp_352_add hkdfCodeFakeB
   hsp hsp_aligned info_sub32_lemmas iter_counter_lemmas okmLen_lt_8161_lemmas
   readBytes_32_hsp_508_of_540 s2_compress256_step_placed_429)
open scoped CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
open LibsignalBinary.Heap.MuslMemOpsRunsTo (applyMemcpyClobber)
open scoped LibsignalBinary.Heap.MuslMemOpsRunsToPlaced
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractExact
  (disjointRegions_of_outside inRegion_sub_slice readable_of_rw s2_memcpy_step_placed_429_exact)

attribute [local simp, local arm64_norm] bv_sub_add_lit hkdfCodeFakeB bv_sub_add_lit_ge

@[local simp, local arm64_norm]
private theorem lsmpl_base_425 [LibsignalPlacement] : lsmpl.base 425 = (blkPl_425).base := rfl

section LoopExactSegments

variable {b_iv : BitVec 64} {C : Crypto}

set_option maxHeartbeats 1600000 in
theorem iter_a2_placed_runsTo_exact [LibsignalPlacement] {H : LibsignalHooks} {aligned : Prop}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hread_info₀ : s₀.mem.Readable infoA info.length)
    (ht_len : tPrev.length = 32) (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA1 hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s (lsρ lsMemcpySym)) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateLoopA2 hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status
  have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hlr := hx.lr_eq
  have hx0 := hx.x0_eq; have hx1 := hx.x1_eq; have hx2 := hx.x2_eq
  have hx19 := hx.x19_eq; have hx21 := hx.x21_eq; have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq; have hx24 := hx.x24_eq; have hx25 := hx.x25_eq
  have hx26 := hx.x26_eq; have hx27 := hx.x27_eq; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.exp.common.frame
  have hrw_384 : s.mem.RW (hsp s₀ + 384#64) 32 := hrw_hsp.sub (by bv_omega)
  have hinfo_all : s.mem.readBytes infoA info.length = info := HFrame.info_bytes hpre hx.exp.common.frame
  have hinfo_take : s.mem.readBytes infoA 32 = info.take 32 := by
    simpa using readBytes_slice_of_readBytes_eq s.mem infoA info hinfo_all 0 32 (by have := hpre.info_ge; omega)
  have htake_len : (info.take 32).length = 32 := List.length_take_of_le hpre.info_ge
  have hx2_nat : (s.readReg64 .x2).toNat = 32 := by rw [hx2]; rfl
  have hrd_take : s.mem.Readable infoA 32 := by
    have hrd_all : s.mem.Readable infoA info.length :=
      (Frame.readable_iff hx.exp.common.frame _ _).mpr hread_info₀
    exact fun a ha =>
      hrd_all a (inRegion_sub_slice (off := 0) (len := 32) (by have := hpre.info_ge; omega)
        (by have := hpre.info_lt; omega) (by simpa using ha))
  have hdisj_take : 32 = 0 ∨ DisjointRegions (hsp s₀ + 384#64) 32 infoA 32 := by
    have hout_take : ∀ a, InRegion infoA 32 a → OutsideRegion (hsp s₀ - 544#64) 1232 a := fun a ha =>
      hpre.out_info_stk a (inRegion_sub_slice (off := 0) (len := 32) (by have := hpre.info_ge; omega)
        (by have := hpre.info_lt; omega) (by simpa using ha))
    exact Or.inr ((disjointRegions_of_outside (by decide) (by decide) hout_take).symm.sub_left
      (hsp s₀ + 384#64) ⟨by decide, by bv_omega⟩)
  refine s2_memcpy_step_placed_429_exact h_mc hrun hpc
    (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, *])
    hx0 hx1 hx2_nat hlr hinfo_take hrw_384 hrd_take hdisj_take fun c => ?_
  dsimp only [applyMemcpyClobber]
  let prk := hkdfExtractBytes C.F salt ikm
  let m₁ := s.mem.writeBytes (hsp s₀ + 384#64) (info.take 32)
  have hA1 : AgreesOutside s.mem m₁ (hsp s₀ + 384#64) 32 :=
    agreesOutside_writeBytes_le s.mem (hsp s₀ + 384#64) (info.take 32) 32 (by omega)
  have hc1 : HExpCommon C.F prk info infoA okmLen s₀ (s.setMem m₁) :=
    HExpCommon.of_agreesOutside_352_592 (off := 384#64) (sz := 32) hx.exp hrun hsp_eq hx29 hA1 (by decide)
  have hcnt1_m1 : m₁.read64 (hsp s₀ + 448#64) = 1#64 := by
    rw [hA1.read64_eq (by unfold DisjointRegions; bv_omega),
        show hsp s₀ + 448#64 = (hsp s₀ + 352#64) + 0x60#64 by bv_lin]
    exact hx.hmac_352.2.2.2.2.1
  have hrw1 : m₁.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc1.common.frame
  dsimp only [m₁] at hcnt1_m1 hrw1
  iterate 7 kdf_step
  let m₂ := m₁.write64 (hsp s₀ + 448#64) 2#64
  have hA2 : AgreesOutside m₁ m₂ (hsp s₀ + 448#64) 8 :=
    agreesOutside_hsp_write64 (AgreesOutside.rfl' m₁ (hsp s₀ + 448#64) 8) (by decide)
  have hc2 : HExpCommon C.F prk info infoA okmLen s₀ (s.setMem m₂) :=
    HExpCommon.of_agreesOutside_352_592 (off := 448#64) (sz := 8) hc1 hrun hsp_eq hx29 hA2 (by decide)
  have hin_416 : m₂.readBytes (hsp s₀ + 416#64) 32 = shaStateBytes (hmacInnerInit C.F prk) := by
    rw [hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        show hsp s₀ + 416#64 = (hsp s₀ + 352#64) + 0x40#64 by bv_lin]
    exact hx.hmac_352.2.2.2.1
  have hblk_352 : m₂.readBytes (hsp s₀ + 352#64) 64 = tPrev ++ info.take 32 := by
    change m₂.readBytes (hsp s₀ + 352#64) (32 + 32) = tPrev ++ info.take 32
    rw [ProofLib.readBytes_add m₂ (hsp s₀ + 352#64) 32 32,
        show (hsp s₀ + 352#64) + BitVec.ofNat 64 32 = hsp s₀ + 384#64 by bv_lin]
    have ht_m2 : m₂.readBytes (hsp s₀ + 352#64) 32 = tPrev := by
      rw [hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
          hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide), ← ht_len]
      exact hx.hmac_352.2.1
    have hi_m2 : m₂.readBytes (hsp s₀ + 384#64) 32 = info.take 32 := by
      rw [hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)]
      have h := readBytes_writeBytes_same s.mem (hsp s₀ + 384#64) (info.take 32)
        (by rw [htake_len]; decide)
      rwa [htake_len] at h
    rw [ht_m2, hi_m2]
  have hblk_len : (tPrev ++ info.take 32).length = 64 := by rw [List.length_append, ht_len, htake_len]
  have hrw_416 : m₂.RW (hsp s₀ + 416#64) 32 :=
    (HFrame.rw_hsp hpre hc2.common.frame).sub (by bv_omega)
  refine s2_compress256_step_placed_429 h_compress
    (stPtr := hsp s₀ + 416#64) (blkPtr := hsp s₀ + 352#64) (lr := (blkPl_379).base + 1544#64)
    (st := hmacInnerInit C.F prk) (blk := tPrev ++ info.take 32)
    (by kdf_reg) (by kdf_reg) (by kdf_reg) (by kdf_reg) (by kdf_reg) (by kdf_reg)
    (by rw [mem_setMem]; exact hin_416) (by rw [mem_setMem]; exact hblk_352) hblk_len
    (by rw [mem_setMem]; exact hrw_416) ?_
  let stBytes := shaStateBytes (C.F (hmacInnerInit C.F prk) (tPrev ++ info.take 32))
  let m₃ := m₂.writeBytes (hsp s₀ + 416#64) stBytes
  have hA3 : AgreesOutside m₂ m₃ (hsp s₀ + 416#64) 32 :=
    agreesOutside_writeBytes_le m₂ (hsp s₀ + 416#64) stBytes 32 (by simp [stBytes, shaStateBytes_length])
  have hc3 : HExpCommon C.F prk info infoA okmLen s₀ (s.setMem m₃) :=
    HExpCommon.of_agreesOutside_352_592 (off := 416#64) (sz := 32) hc2 hrun hsp_eq hx29 hA3 (by decide)
  refine RunsTo.refl ⟨by kdf_reg,
    ⟨⟨by kdf_reg, by kdf_reg, by kdf_reg,
      by rw [mem_setMem]; exact hc3.common.saved,
      by rw [mem_setMem]; exact hc3.common.frame⟩,
     by rw [mem_setMem]; exact hc3.m0_eq, by rw [mem_setMem]; exact hc3.m8_eq,
     by rw [mem_setMem]; exact hc3.m16_eq, by rw [mem_setMem]; exact hc3.m24_eq,
     by rw [mem_setMem]; exact hc3.hmac_208⟩,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    ?_, ?_, ?_, ?_, ?_⟩
  · show m₃.readBytes (hsp s₀ + 416#64) 32 = stBytes
    have hlen : stBytes.length = 32 := shaStateBytes_length _
    have h := readBytes_writeBytes_same m₂ (hsp s₀ + 416#64) stBytes (by rw [hlen]; decide)
    rwa [hlen] at h
  · show m₃.read64 (hsp s₀ + 448#64) = 2#64
    rw [hA3.read64_eq (by unfold DisjointRegions; bv_omega)]
    simp (config := { decide := true }) only [m₂, arm64_norm]
  · show m₃.readBytes (hsp s₀ + 456#64) 32 = shaStateBytes (hmacOuterInit C.F prk)
    rw [hA3.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        show hsp s₀ + 456#64 = (hsp s₀ + 352#64) + 0x68#64 by bv_lin]
    exact hx.hmac_352.2.2.2.2.2.1
  · show m₃.read64 (hsp s₀ + 488#64) = 1#64
    rw [hA3.read64_eq (by unfold DisjointRegions; bv_omega),
        hA2.read64_eq (by unfold DisjointRegions; bv_omega),
        hA1.read64_eq (by unfold DisjointRegions; bv_omega),
        show hsp s₀ + 488#64 = (hsp s₀ + 352#64) + 0x88#64 by bv_lin]
    exact hx.hmac_352.2.2.2.2.2.2
  · show m₃.readBytes okmA dstOff = okmSoFar
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd3 : DisjointRegions (hsp s₀ + 416#64) 32 okmA dstOff :=
        (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 416#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      have hd2 : DisjointRegions (hsp s₀ + 448#64) 8 okmA dstOff :=
        (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 448#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      have hd1 : DisjointRegions (hsp s₀ + 384#64) 32 okmA dstOff :=
        (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 384#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      have hlen : dstOff ≤ 2 ^ 64 := by have := hpre.okm_len; omega
      rw [hA3.readBytes_eq hd3 hlen, hA2.readBytes_eq hd2 hlen, hA1.readBytes_eq hd1 hlen]
      exact hx.okm_pre

set_option maxHeartbeats 4000000 in
theorem iter_b_placed_runsTo_exact [LibsignalPlacement] {H : LibsignalHooks} {aligned : Prop}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hread_info₀ : s₀.mem.Readable infoA info.length)
    (ht_len : tPrev.length = 32) (hi : i = 1 ∨ i = 2) (hrem : rem = 32 ∨ rem = 64)
    (hdst : dstOff + 32 ≤ okmLen)
    (hx : StateLoopA2 hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateLoopC hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ · (blkPl_425).base) := by
  have hpc := hx.pc_eq
  have hrun := hx.exp.common.status; have hsp_eq := hx.exp.common.sp_eq
  have hx29 := hx.exp.common.x29_eq; have hx19 := hx.x19_eq; have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq; have hx23 := hx.x23_eq; have hx24 := hx.x24_eq
  have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.exp.common.frame
  have hk_lt : info.length - 32 < 23 := by have := hpre.info_lt; omega
  rcases info_sub32_lemmas (by omega : info.length - 32 < 64) with
    ⟨hlsr6_nat, hlsr6, hand_hi, hand_lo, hlsr6_nat_eq, hlsr6_eq⟩
  rcases cmp_lt64_lemmas (by omega : info.length - 32 < 64) with ⟨h_k_ule, h_k_ult, h_k_cmp⟩
  iterate 11 kdf_step
  let prk := hkdfExtractBytes C.F salt ikm
  let k := info.length - 32
  let m₀ := (s.mem.write8 (hsp s₀ + 415#64) 0#8).write8 (hsp s₀ + 415#64) (BitVec.ofNat 8 k)
  have hA0 : AgreesOutside s.mem m₀ (hsp s₀ + 415#64) 1 := by dsimp only [m₀]; prove_agrees_hsp
  have hc0 : HExpCommon C.F prk info infoA okmLen s₀ (s.setMem m₀) :=
    HExpCommon.of_agreesOutside_352_592 (off := 415#64) (sz := 1) hx.exp hrun hsp_eq hx29 hA0 (by decide)
  have hinfo_all : m₀.readBytes infoA info.length = info := HFrame.info_bytes hpre hc0.common.frame
  have hinfo_drop : m₀.readBytes (infoA + 32#64) k = info.drop 32 := by
    have h := readBytes_slice_of_readBytes_eq m₀ infoA info hinfo_all 32 k (by have := hpre.info_ge; omega)
    simpa [k, List.take_of_length_le (by simp : (info.drop 32).length ≤ info.length - 32)] using h
  have hdrop_len : (info.drop 32).length = k := by simp [k]
  have hrw_352 : m₀.RW (hsp s₀ + 352#64) k :=
    (HFrame.rw_hsp hpre hc0.common.frame).sub
      (by dsimp only [k]; generalize info.length - 32 = k' at hk_lt ⊢; clear * - hk_lt; bv_omega)
  have hx2_nat : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrd_drop : m₀.Readable (infoA + 32#64) k := by
    have hrd_all : m₀.Readable infoA info.length :=
      (Frame.readable_iff hc0.common.frame _ _).mpr hread_info₀
    exact fun a ha =>
      hrd_all a (inRegion_sub_slice (off := 32) (by have := hpre.info_ge; omega)
        (by have := hpre.info_lt; omega) ha)
  have hdisj_drop : k = 0 ∨ DisjointRegions (hsp s₀ + 352#64) k (infoA + 32#64) k := by
    by_cases hk0 : k = 0
    · exact Or.inl hk0
    · have hout_drop : ∀ a, InRegion (infoA + 32#64) k a → OutsideRegion (hsp s₀ - 544#64) 1232 a := fun a ha =>
        hpre.out_info_stk a (inRegion_sub_slice (off := 32) (by have := hpre.info_ge; omega)
          (by have := hpre.info_lt; omega) ha)
      exact Or.inr ((disjointRegions_of_outside (by omega) (by decide) hout_drop).symm.sub_left
        (hsp s₀ + 352#64) ⟨by omega, by dsimp only [k]; generalize info.length - 32 = k' at hk_lt ⊢; clear * - hk_lt; bv_omega⟩)
  refine s2_memcpy_step_placed_429_exact h_mc
    (dst := hsp s₀ + 352#64) (src := infoA + 32#64) (lr := (blkPl_379).base + 1612#64)
    (len := k) (bs := info.drop 32)
    (by kdf_reg) (by kdf_reg)
    (by rw [State.spAligned, State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, *])
    (by kdf_reg)
    (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, BitVec.add_zero])
    hx2_nat (by kdf_reg) (by rw [mem_setMem]; exact hinfo_drop)
    (by rw [mem_setMem]; exact hrw_352)
    (by rw [mem_setMem]; exact hrd_drop)
    hdisj_drop fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₁ := m₀.writeBytes (hsp s₀ + 352#64) (info.drop 32)
  have hA1 : AgreesOutside m₀ m₁ (hsp s₀ + 352#64) 23 :=
    agreesOutside_writeBytes_le m₀ (hsp s₀ + 352#64) (info.drop 32) 23 (by omega)
  refine RunsTo.trans (RunsTo.refl (P := fun s₁ : State =>
      s₁.pc = (blkPl_379).base + 1612#64 ∧ s₁.status = .Running ∧ s₁.sp = hsp s₀ ∧
      s₁.readReg64 .x29 = hsp s₀ + 592#64 ∧ s₁.readReg64 .x19 = hsp s₀ + 352#64 ∧
      s₁.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff ∧ s₁.readReg64 .x23 = hsp s₀ + 352#64 ∧
      s₁.readReg64 .x24 = 32#64 ∧ s₁.readReg64 .x26 = BitVec.ofNat 64 rem ∧
      s₁.readReg64 .x27 = BitVec.ofNat 64 i ∧ s₁.readReg64 .x28 = hsp s₀ + 352#64 ∧
      (∃ _ : Unit, s₁.mem = m₁))
    ⟨by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
     by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
     ⟨(), by rw [State.mem_setPC, mem_setMem, mem_setMem]⟩⟩) ?_
  rintro s₁ ⟨hpc₁, hrun₁, hsp₁, hx29_1, hx19_1, hx22_1, hx23_1, hx24_1, hx26_1, hx27_1, hx28_1, hm₁_box⟩
  clear hpc hrun hsp_eq hx29 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hrw_hsp
    hlsr6_nat hlsr6 hand_hi hand_lo hlsr6_nat_eq hlsr6_eq h_k_ule h_k_ult h_k_cmp
    hinfo_all hinfo_drop hrw_352 hx2_nat hrd_drop hdisj_drop c
  have hc1 : HExpCommon C.F prk info infoA okmLen s₀ s₁ :=
    HExpCommon.of_agreesOutside_352_592 (off := 352#64) (sz := 23) hc0
      hrun₁ hsp₁ hx29_1 (by rcases hm₁_box with ⟨_, h⟩; rw [h]; exact hA1) (by decide)
  have hm16_1 : s₁.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := hc1.m16_eq
  have hpos_415 : s₁.mem.read8 (hsp s₀ + 415#64) = BitVec.ofNat 8 k := by
    rcases hm₁_box with ⟨_, hm₁_save⟩; rw [hm₁_save]
    have hd : ∀ (_ : 0 < (info.drop 32).length),
        DisjointRegions (hsp s₀ + 352#64) (info.drop 32).length (hsp s₀ + 415#64) 1 := by
      intro _; unfold DisjointRegions; bv_omega
    have h1 := writeBytes_readBytes_disj m₀ (hsp s₀ + 352#64) (info.drop 32)
      (hsp s₀ + 415#64) 1 (fun h0 _ => hd h0) (by decide)
    dsimp only [Memory.readBytes, BitVec.add_zero] at h1
    rw [List.cons.inj h1 |>.1]; exact Memory.read8_write8_same _ _ _
  have hrw1 : s₁.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc1.common.frame
  rcases canWrite_hsp_352_add hrw1 (by omega : k < 64) with ⟨hcw_pos1, hcw_pos2⟩
  have hze32 := zeroExtend32_ofNat8_eq_truncate32 (by omega : k < 64)
  have hze64 := zeroExtend64_ofNat8 (by omega : k < 64)
  have hze64_32 := zeroExtend64_truncate32_ofNat64 (by omega : k < 64)
  have hand255 := zeroExtend64_and255_truncate32_ofNat64 (by omega : k < 64)
  have hand64_255 := and64_255_ofNat64 (by omega : k < 64)
  have hand40 := and_0xffffffffff_ofNat64 (by omega : k < 64)
  rcases cmp32_lt63_lemmas (by omega : k < 63) with ⟨hcmp63_eq, hcmp63_ne, hcmp63_z⟩
  have hadd1_k := zeroExtend64_add1_truncate32_ofNat64 (by omega : k < 63)
  rcases iter_counter_lemmas hi with ⟨hi_eq, hi_ne, hi_z, hi_add1, hi1_ze⟩
  have hdst_add : (okmA + BitVec.ofNat 64 dstOff) + 32#64 = okmA + BitVec.ofNat 64 (dstOff + 32) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hrem_sub : BitVec.ofNat 64 rem - 32#64 = BitVec.ofNat 64 (rem - 32) := by
    rcases hrem with rfl | rfl <;> rfl
  dsimp only [k] at hpos_415 hcw_pos1 hcw_pos2 hze32 hze64 hze64_32 hand255 hand64_255
  dsimp only [k] at hand40 hcmp63_eq hcmp63_ne hcmp63_z hadd1_k
  iterate 31 kdf_step
  refine RunsTo.refl ?_
  rcases hm₁_box with ⟨_, hm₁_save⟩
  have hhm_352 : HmacStN
      ((((s₁.mem.write8 (hsp s₀ + 32#64) (BitVec.ofNat 8 (i + 1))).write8
        (hsp s₀ + 352#64 + BitVec.ofNat 64 k) (BitVec.ofNat 8 (i + 1))).write8
        (hsp s₀ + 415#64) (BitVec.ofNat 8 (k + 1))))
      (hsp s₀ + 352#64) C.F prk (tPrev ++ info.take 32)
      (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) := by
    rw [hm₁_save]
    have htake_len : (info.take 32).length = 32 := List.length_take_of_le hpre.info_ge
    have hblk_len : (tPrev ++ info.take 32).length = 64 := by rw [List.length_append, ht_len, htake_len]
    simpa only [hdrop_len] using CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.HmacStN.of_tail_counter_352
      (b0 := 0#8) (b1 := BitVec.ofNat 8 k)
      (c := BitVec.ofNat 8 (i + 1)) hblk_len (by rw [hdrop_len]; omega : (info.drop 32).length < 55)
      hx.in_416 hx.cnt_448 hx.out_456 hx.cnt_488
  refine ⟨by kdf_reg,
    HExpCommon.of_agreesOutside_32_560 (off := 32#64) (sz := 464) hc1
      (by kdf_reg) (by kdf_reg) (by kdf_reg)
      (by prove_agrees_hsp) (by decide) (by prove_hmac_208 hc1.hmac_208),
    by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hdst_add],
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hrem_sub],
    by kdf_reg, by kdf_reg, ?_, ?_⟩
  · simp only [mem_setMem]
    refine CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.HmacStN.of_copy_352_32 hhm_352 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [k, arm64_norm]
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hlen : dstOff ≤ 2 ^ 64 := by have := hpre.okm_len; omega
      have hd2 : DisjointRegions (hsp s₀ + 32#64) 464 okmA dstOff :=
        (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 32#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      have hd1 : DisjointRegions (hsp s₀ + 352#64) 23 okmA dstOff :=
        (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 352#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      have hd0 : DisjointRegions (hsp s₀ + 415#64) 1 okmA dstOff :=
        (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 415#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      refine Eq.trans (AgreesOutside.readBytes_eq (m₁ := s₁.mem) ?_ hd2 hlen) ?_
      · prove_agrees_hsp
      · rw [hm₁_save, hA1.readBytes_eq hd1 hlen, hA0.readBytes_eq hd0 hlen]
        exact hx.okm_pre

set_option maxHeartbeats 1600000 in
theorem iter_d_continue_placed_runsTo_exact [LibsignalPlacement] {H : LibsignalHooks} {aligned : Prop}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hokm96 : okmLen = 96)
    (hx : StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen 1 64 32 s₀ s) :
    let tNext := hmacWith C.F (hkdfExtractBytes C.F salt ikm) (tPrev ++ info ++ [2#8])
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tNext (okmSoFar ++ tNext) okmLen 2 32 64 s₀) := by
  intro tNext; subst hokm96
  have ht_540 : s.mem.readBytes (hsp s₀ + 540#64) 32 = tNext := hx.t_540
  have htNext_len : tNext.length = 32 := length_hmacWith _ _ _
  generalize tNext = tN at ht_540 htNext_len ⊢
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status
  have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hx20 : s.readReg64 .x20 = okmA + 64#64 := hx.x20_eq
  have hx21 := hx.x21_eq; have hx22 : s.readReg64 .x22 = okmA + 32#64 := hx.x22_eq
  have hx24 := hx.x24_eq; have hx25 := hx.x25_eq
  have hx26 : s.readReg64 .x26 = 32#64 := hx.x26_eq
  have hx27 : s.readReg64 .x27 = 1#64 := hx.x27_eq
  have hx28 := hx.x28_eq; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_okm : s.mem.RW okmA 96 := HFrame.rw_okm hpre hx.exp.common.frame
  have hrw_dst : s.mem.RW (okmA + 32#64) 32 := hrw_okm.sub (by bv_omega)
  have hrd_src : s.mem.Readable (hsp s₀ + 540#64) 32 :=
    readable_of_rw ((HFrame.rw_hsp hpre hx.exp.common.frame).sub (by bv_omega))
  have hdisj_dst : 32 = 0 ∨ DisjointRegions (okmA + 32#64) 32 (hsp s₀ + 540#64) 32 :=
    Or.inr ((hpre.disj_okm_stk.sub_left (okmA + 32#64) ⟨by decide, by bv_omega⟩).sub_right
      (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩)
  iterate 4 kdf_step
  refine s2_memcpy_step_placed_429_exact h_mc hrun rfl
    (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, *])
    rfl rfl rfl rfl ht_540 hrw_dst hrd_src hdisj_dst fun c => ?_
  dsimp only [applyMemcpyClobber]
  let prk := hkdfExtractBytes C.F salt ikm
  let m₁ := s.mem.writeBytes (okmA + 32#64) tN
  have hA1 : AgreesOutside s.mem m₁ (okmA + 32#64) 32 :=
    agreesOutside_writeBytes_le s.mem (okmA + 32#64) tN 32 (by omega)
  have hc1 : HExpCommon C.F prk info infoA 96 s₀ (s.setMem m₁) :=
    HExpCommon.of_agreesOutside_okm hpre hx.exp hrun hsp_eq hx29 hA1 ⟨by decide, by decide⟩
  have hm24_1 : m₁.read64 (hsp s₀ + 24#64) = hsp s₀ + 508#64 := hc1.m24_eq
  have hrw1_hsp : m₁.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc1.common.frame
  dsimp only [m₁] at hm24_1 hrw1_hsp
  iterate 9 kdf_step
  refine RunsTo.refl ?_
  have hA2 : AgreesOutside m₁
      ((((m₁.write64 (hsp s₀ + 508#64) (m₁.read64 (hsp s₀ + 540#64))).write64
        (hsp s₀ + 516#64) (m₁.read64 (hsp s₀ + 548#64))).write64
        (hsp s₀ + 524#64) (m₁.read64 (hsp s₀ + 556#64))).write64
        (hsp s₀ + 532#64) (m₁.read64 (hsp s₀ + 564#64)))
      (hsp s₀ + 508#64) 32 := by prove_agrees_hsp
  refine ⟨by kdf_reg,
    HExpCommon.of_agreesOutside_352_592 (off := 508#64) (sz := 32) hc1
      (by kdf_reg) (by kdf_reg) (by kdf_reg) hA2 (by decide),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, ?_, ?_⟩
  · simp only [mem_setMem]
    have ht_m1 : m₁.readBytes (hsp s₀ + 540#64) 32 = tN := by
      have hd : DisjointRegions (okmA + 32#64) 32 (hsp s₀ + 540#64) 32 :=
        (hpre.disj_okm_stk.sub_left (okmA + 32#64) ⟨by decide, by bv_omega⟩).sub_right
          (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩
      exact (hA1.readBytes_eq hd (by decide)).trans ht_540
    exact readBytes_32_hsp_508_of_540 ht_m1
      (by simp (config := { decide := true }) only [m₁, arm64_norm])
      (by simp (config := { decide := true }) only [m₁, arm64_norm])
      (by simp (config := { decide := true }) only [m₁, arm64_norm])
      (by simp (config := { decide := true }) only [m₁, arm64_norm])
  · have hd2 : DisjointRegions (hsp s₀ + 508#64) 32 okmA 64 :=
      (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 508#64) ⟨by decide, by bv_omega⟩).sub_right
        okmA ⟨by decide, by bv_omega⟩
    dsimp only [mem_setMem]
    rw [hA2.readBytes_eq hd2 (by decide), show (64 : ℕ) = 32 + 32 from rfl,
        ProofLib.readBytes_add m₁ okmA 32 32]
    have hpre_m1 : m₁.readBytes okmA 32 = okmSoFar := by
      have hd1 : DisjointRegions (okmA + 32#64) 32 okmA 32 := by unfold DisjointRegions; bv_omega
      exact (hA1.readBytes_eq hd1 (by decide)).trans hx.okm_pre
    have hnext_m1 : m₁.readBytes (okmA + BitVec.ofNat 64 32) 32 = tN := by
      have h := readBytes_writeBytes_same s.mem (okmA + 32#64) tN (by rw [htNext_len]; decide)
      rwa [htNext_len] at h
    rw [hpre_m1, hnext_m1]

set_option maxHeartbeats 1600000 in
theorem iter_d_done_placed_runsTo_exact [LibsignalPlacement] {H : LibsignalHooks} {aligned : Prop}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i dstOff : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hdst_pos : 0 < dstOff) (hdst_eq : dstOff + 32 = okmLen)
    (hokm_eq : okmSoFar ++ hmacWith C.F (hkdfExtractBytes C.F salt ikm)
        (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) =
      hkdfExpand C.F (hkdfExtractBytes C.F salt ikm) info okmLen)
    (hx : StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i 32 dstOff s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateDone hkdfCodeFakeB C.F salt ikm info okmA okmLen s₀) := by
  let prk := hkdfExtractBytes C.F salt ikm
  have ht_540 : s.mem.readBytes (hsp s₀ + 540#64) 32 =
      hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) := hx.t_540
  have htNext_len : (hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])).length = 32 := length_hmacWith _ _ _
  generalize hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) = tN at ht_540 htNext_len hokm_eq
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status; have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hx20 := hx.x20_eq; have hx21 := hx.x21_eq; have hx22 := hx.x22_eq; have hx24 := hx.x24_eq; have hx25 := hx.x25_eq
  have hx26 : s.readReg64 .x26 = 0#64 := hx.x26_eq; have hx27 := hx.x27_eq; have hx28 := hx.x28_eq; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_okm : s.mem.RW okmA okmLen := HFrame.rw_okm hpre hx.exp.common.frame
  have hrw_dst : s.mem.RW (okmA + BitVec.ofNat 64 dstOff) 32 := hrw_okm.sub (by have := hpre.okm_len; bv_omega)
  have hrd_src : s.mem.Readable (hsp s₀ + 540#64) 32 :=
    readable_of_rw ((HFrame.rw_hsp hpre hx.exp.common.frame).sub (by bv_omega))
  have hdisj_dst : 32 = 0 ∨ DisjointRegions (okmA + BitVec.ofNat 64 dstOff) 32 (hsp s₀ + 540#64) 32 :=
    Or.inr ((hpre.disj_okm_stk.sub_left (okmA + BitVec.ofNat 64 dstOff)
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right
      (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩)
  iterate 4 kdf_step
  refine s2_memcpy_step_placed_429_exact h_mc hrun rfl
    (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, *])
    rfl rfl rfl rfl ht_540 hrw_dst hrd_src hdisj_dst fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₁ := s.mem.writeBytes (okmA + BitVec.ofNat 64 dstOff) tN
  have hA1 : AgreesOutside s.mem m₁ (okmA + BitVec.ofNat 64 dstOff) 32 :=
    agreesOutside_writeBytes_le s.mem (okmA + BitVec.ofNat 64 dstOff) tN 32 (by omega)
  have hc1 : HExpCommon C.F prk info infoA okmLen s₀ (s.setMem m₁) :=
    HExpCommon.of_agreesOutside_okm hpre hx.exp hrun hsp_eq hx29 hA1
      ⟨by decide, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hpre.okm_len; omega)]; omega⟩
  have hm0_1 : m₁.read64 (hsp s₀) = BitVec.ofNat 64 okmLen := by
    simpa [mem_setMem, BitVec.add_zero] using hc1.m0_eq
  have hm0_1' : m₁.read64 (hsp s₀ + 0#64) = BitVec.ofNat 64 okmLen := hc1.m0_eq
  have hm24_1 : m₁.read64 (hsp s₀ + 24#64) = hsp s₀ + 508#64 := hc1.m24_eq
  have hrw1_hsp : m₁.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc1.common.frame
  rcases okmLen_lt_8161_lemmas hpre.okm_len with ⟨hokm_c, hokm_ule, hokm_ult⟩
  dsimp only [m₁] at hm0_1 hm0_1' hm24_1 hrw1_hsp
  iterate 13 kdf_step
  refine RunsTo.refl ?_
  have hA2 : AgreesOutside m₁
      ((((m₁.write64 (hsp s₀ + 508#64) (m₁.read64 (hsp s₀ + 540#64))).write64
        (hsp s₀ + 516#64) (m₁.read64 (hsp s₀ + 548#64))).write64
        (hsp s₀ + 524#64) (m₁.read64 (hsp s₀ + 556#64))).write64
        (hsp s₀ + 532#64) (m₁.read64 (hsp s₀ + 564#64)))
      (hsp s₀ + 508#64) 32 := by prove_agrees_hsp
  refine ⟨by kdf_reg,
    HCommon.of_agreesOutside_hsp (off := 508#64) (sz := 32) hc1.common
      (by kdf_reg) (by kdf_reg) (by kdf_reg) hA2 (by decide), ?_⟩
  have hd2 : DisjointRegions (hsp s₀ + 508#64) 32 okmA okmLen :=
    hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 508#64) ⟨by decide, by bv_omega⟩
  dsimp only [mem_setMem]
  rw [hA2.readBytes_eq hd2 (by have := hpre.okm_len; omega), ← hdst_eq,
      ProofLib.readBytes_add m₁ okmA dstOff 32]
  have hpre_m1 : m₁.readBytes okmA dstOff = okmSoFar := by
    have hd1 : DisjointRegions (okmA + BitVec.ofNat 64 dstOff) 32 okmA dstOff := by
      have := hpre.okm_len; unfold DisjointRegions; bv_omega
    exact (hA1.readBytes_eq hd1 (by have := hpre.okm_len; omega)).trans hx.okm_pre
  have hnext_m1 : m₁.readBytes (okmA + BitVec.ofNat 64 dstOff) 32 = tN := by
    have h := readBytes_writeBytes_same s.mem (okmA + BitVec.ofNat 64 dstOff) tN
      (by rw [htNext_len]; decide)
    rwa [htNext_len] at h
  rw [hpre_m1, hnext_m1, hokm_eq, hdst_eq]

end LoopExactSegments

end LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceLoopExact
