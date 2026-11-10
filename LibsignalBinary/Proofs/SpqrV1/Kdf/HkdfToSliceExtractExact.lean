/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon

/-!
# `HookSatExactMemcpy` Siblings of `SpqrV1.Kdf.HkdfToSliceExtract` (`HkdfToSliceExtractExact`, Block `379`)

- **Role:** `Role::Proof` (untrusted proof module outside the TCB; #1255 mc2 Cone 3).
- **Overview:**
  Replaces `h_memcpy : H lsMemcpySym = some memcpyHook` on the Extract-phase `memcpy` segments of
  Block `379` (`spqr::kdf::hkdf_to_slice`) with `(h_mc : HookSatExactMemcpy H lsMemcpySym)` via
  `s2_memcpy_step_placed_of_exact`, keeping all cut predicates (`StateERet1`, `StateE3cc`, `HCommon`,
  `HFrame`) **100% unchanged**.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractExact

open Arm64 ProofLib
open CryptoGames.HMAC (chunks64)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPC_379 blkPl_379 lsρ)
open CryptoVerification.LibsignalAesCbc.Run.Bytes
  (readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet
  (Frame HmacSt RunsTo RunsToFrom TraceEq TraceEq.advancePC_step TraceEq.refl TraceEq.setMem_step
   TraceEq.setPC_step TraceEq.setPState_step TraceEq.writeReg32_step TraceEq.writeReg64_step
   TraceEq.writeVReg128_step hmacInnerInit lsCompress256Sym lsMemcpySym
   readBytes_32_eq_of_read64_eq shaStateBytes_length)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (agreesOutside_writeBytes_le cmp_lt64_lemmas mem_setMem)
open CryptoVerification.SpqrV1.Kdf
  (HmacStN cmp_ge64_lemmas effectiveHmacKey ikm_split_lemmas)
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
  (HCommon HFrame HPre StateE3cc StateERet1 agreesOutside_hsp_write8 bv_sub_add_lit_ge
   hkdfCodeFakeB hsp hsp_aligned s2_compress256_multi_step_placed_429)
open scoped CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
open LibsignalBinary.Heap.MuslMemOpsRunsTo (MemcpyClobber applyMemcpyClobber)
open scoped LibsignalBinary.Heap.MuslMemOpsRunsToPlaced
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (HookSatExactMemcpy s2_memcpy_step_placed_of_exact)

attribute [local simp, local arm64_norm] bv_sub_add_lit hkdfCodeFakeB bv_sub_add_lit_ge

/-! ## Shared `Readable` / `DisjointRegions` & `s2_memcpy_step_placed_429_exact` Helpers -/

theorem readable_of_rw {m : Memory} {p : BitVec 64} {n : ℕ} (hrw : m.RW p n) :
    m.Readable p n := fun a ha => by
  obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw a ha)
  exact ⟨by rw [hp]; rfl, hlf⟩

theorem inRegion_sub_slice {base : BitVec 64} {off len total : ℕ} {a : BitVec 64}
    (htot : off + len ≤ total) (hle : total < 2 ^ 64)
    (ha : InRegion (base + BitVec.ofNat 64 off) len a) :
    InRegion base total a := by
  unfold InRegion at ha ⊢
  bv_omega

theorem disjointRegions_of_outside {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hout : ∀ a, InRegion b₁ n₁ a → OutsideRegion b₂ n₂ a) :
    DisjointRegions b₁ n₁ b₂ n₂ := by
  have hdisj : ∀ a, ¬ (InRegion b₁ n₁ a ∧ InRegion b₂ n₂ a) := by
    intro a ⟨h1, h2⟩
    have h_out := hout a h1
    rw [outsideRegion_iff_not_inRegion] at h_out
    exact h_out h2
  constructor
  · apply Classical.byContradiction; intro hlt
    exact hdisj b₂ ⟨by simp only [InRegion]; omega,
      by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
  · apply Classical.byContradiction; intro hlt
    exact hdisj b₁ ⟨by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega,
      by simp only [InRegion]; omega⟩

theorem s2_memcpy_step_placed_429_exact [LibsignalPlacement] {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    {s₀ s : State} {Q : State → Prop}
    {dst src lr : BitVec 64} {len : ℕ} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemcpySym)
    (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hbs : s.mem.readBytes src len = bs)
    (hrw : s.mem.RW dst len)
    (hread_src : s.mem.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len)
    (h : ∀ c : MemcpyClobber,
      RunsToFrom ((blkPC_379).rebase (blkPl_379).base H) s₀
        (applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c) Q) :
    RunsToFrom ((blkPC_379).rebase (blkPl_379).base H) s₀ s Q :=
  s2_memcpy_step_placed_of_exact H h_mc
    hrun hsp_al hpc hx0 hx1 hx2 hlr hbs hrw hread_src hdisj h

/-! ## Extract-Phase Exact Segment Proofs (Block `379`) -/

section ExtractExactSegments

variable {C : Crypto}

theorem seg_e1_lt56_placed_runsTo_exact [LibsignalPlacement] {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    {b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hread_ikm : s₀.mem.Readable ikmA ikm.length)
    (hikm : ikm.length < 64)
    (hx : StateERet1 hkdfCodeFakeB C.F salt ikm info ikmA infoA okmA okmLen s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateE3cc hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp_eq := hx.common.sp_eq
  have hx29 := hx.common.x29_eq; have hx22 := hx.x22_eq; have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq; have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  have htag := hx.tag_32; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.common.frame
  have hpos : s.mem.read8 (hsp s₀ + 103#64) = 0#8 := by
    have heq : hsp s₀ + 103#64 = (hsp s₀ + 40#64) + 0x3f#64 := by bv_lin
    rw [heq]; exact hx.hmac_40.2.2.1
  rcases cmp_lt64_lemmas hikm with ⟨h_ikm_ule, h_ikm_ult, h_ikm_cmp⟩
  iterate 29 kdf_step
  let m₀ := (((((((s.mem.write64 (hsp s₀ + 16#64) (BitVec.ofNat 64 info.length)).write64
        (hsp s₀ + 304#64) (s.mem.read64 (hsp s₀ + 136#64))).write64
        (hsp s₀ + 312#64) (s.mem.read64 (hsp s₀ + 144#64))).write64
        (hsp s₀ + 320#64) (s.mem.read64 (hsp s₀ + 152#64))).write64
        (hsp s₀ + 328#64) (s.mem.read64 (hsp s₀ + 160#64))).write64
        (hsp s₀ + 240#64) (s.mem.read64 (hsp s₀ + 72#64))).write64
        (hsp s₀ + 248#64) (s.mem.read64 (hsp s₀ + 80#64))
        |>.write64 (hsp s₀ + 256#64) (s.mem.read64 (hsp s₀ + 88#64))
        |>.write64 (hsp s₀ + 264#64) (s.mem.read64 (hsp s₀ + 96#64))
        |>.write64 (hsp s₀ + 336#64) (s.mem.read64 (hsp s₀ + 168#64))
        |>.write64 (hsp s₀ + 344#64) (s.mem.read64 (hsp s₀ + 176#64))
        |>.write64 (hsp s₀ + 208#64) (s.mem.read64 (hsp s₀ + 40#64))
        |>.write64 (hsp s₀ + 216#64) (s.mem.read64 (hsp s₀ + 48#64))
        |>.write64 (hsp s₀ + 224#64) (s.mem.read64 (hsp s₀ + 56#64))
        |>.write64 (hsp s₀ + 232#64) (s.mem.read64 (hsp s₀ + 64#64))
        |>.write64 (hsp s₀ + 272#64) (s.mem.read64 (hsp s₀ + 104#64))
        |>.write64 (hsp s₀ + 280#64) (s.mem.read64 (hsp s₀ + 112#64))
        |>.write64 (hsp s₀ + 288#64) (s.mem.read64 (hsp s₀ + 120#64))
        |>.write64 (hsp s₀ + 296#64) (s.mem.read64 (hsp s₀ + 128#64)))
  have hA0 : AgreesOutside s.mem m₀ (hsp s₀ + 16#64) 336 := by dsimp only [m₀]; prove_agrees_hsp
  have hc0 : HCommon okmLen s₀ (s.setMem m₀) :=
    HCommon.of_agreesOutside_hsp (off := 16#64) (sz := 336) hx.common hrun hsp_eq hx29 hA0 (by decide)
  have hhm0 : HmacSt m₀ (hsp s₀ + 208#64) C.F (effectiveHmacKey C.F salt) [] := by
    refine HmacSt.of_copy_empty hx.hmac_40 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [m₀, arm64_norm]
  have hm16_0 : m₀.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    simp (config := { decide := true }) only [m₀, arm64_norm]
  have hx2_nat : (BitVec.ofNat 64 ikm.length).toNat = ikm.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hikm_s : m₀.readBytes ikmA ikm.length = ikm := HFrame.ikm_bytes hpre hc0.frame
  have hrw_dst : m₀.RW (hsp s₀ + 208#64) ikm.length := (HFrame.rw_hsp hpre hc0.frame).sub (by bv_omega)
  have hread_m0 : m₀.Readable ikmA ikm.length :=
    (Frame.readable_iff hc0.frame _ _).mpr hread_ikm
  have hdisj_ikm : ikm.length = 0 ∨ DisjointRegions (hsp s₀ + 208#64) ikm.length ikmA ikm.length := by
    by_cases h0 : ikm.length = 0
    · exact Or.inl h0
    · exact Or.inr ((disjointRegions_of_outside (by omega) (by decide) hpre.out_ikm_stk).symm.sub_left
        (hsp s₀ + 208#64) ⟨by omega, by bv_omega⟩)
  refine s2_memcpy_step_placed_429_exact h_mc
    hrun rfl (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, *])
    (by kdf_reg) (by kdf_reg) (by simp (config := { decide := true }) only [arm64_norm, *])
    ((by kdf_reg) : _ = (blkPl_379).base + 188#64) hikm_s hrw_dst hread_m0 hdisj_ikm fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₁ := m₀.writeBytes (hsp s₀ + 208#64) ikm
  have hA1 : AgreesOutside m₀ m₁ (hsp s₀ + 208#64) 63 :=
    agreesOutside_writeBytes_le m₀ (hsp s₀ + 208#64) ikm 63 (by omega)
  have hc1 : HCommon okmLen s₀ (s.setMem m₁) :=
    HCommon.of_agreesOutside_hsp (off := 208#64) (sz := 63) hc0 hrun hsp_eq hx29 hA1 (by decide)
  have hrw1 : m₁.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc1.frame
  dsimp only [m₁, m₀] at hrw1
  iterate 3 kdf_step
  refine RunsTo.refl ?_
  have hA2 : AgreesOutside m₁ (m₁.write8 (hsp s₀ + 271#64) (BitVec.ofNat 8 ikm.length)) (hsp s₀ + 271#64) 1 :=
    agreesOutside_hsp_write8 (AgreesOutside.rfl' m₁ (hsp s₀ + 271#64) 1) (by decide)
  refine ⟨by kdf_reg,
    HCommon.of_agreesOutside_hsp (off := 271#64) (sz := 1) hc1 (by kdf_reg) (by kdf_reg) (by kdf_reg) hA2 (by decide),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, ?_, ?_⟩
  · show (m₁.write8 (hsp s₀ + 271#64) (BitVec.ofNat 8 ikm.length)).read64 (hsp s₀ + 16#64) =
      BitVec.ofNat 64 info.length
    rw [hA2.read64_eq (by unfold DisjointRegions; bv_omega),
        hA1.read64_eq (by unfold DisjointRegions; bv_omega)]
    exact hm16_0
  · refine ⟨[], ikm, rfl, by decide, hikm, ?_⟩
    have h271 : hsp s₀ + 271#64 = (hsp s₀ + 208#64) + 63#64 := by bv_lin
    show HmacStN (m₁.write8 (hsp s₀ + 271#64) (BitVec.ofNat 8 ikm.length))
      (hsp s₀ + 208#64) C.F (effectiveHmacKey C.F salt) [] ikm
    rw [h271]; exact HmacStN.of_hmacSt (CryptoVerification.SpqrV1.Kdf.HmacSt.of_writeBytes_lt63_write8_pos hhm0 hikm)

set_option maxHeartbeats 800000 in
theorem seg_e1_eq64_placed_runsTo_exact [LibsignalPlacement] {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hread_ikm : s₀.mem.Readable ikmA ikm.length)
    (hikm : 64 ≤ ikm.length)
    (hx : StateERet1 hkdfCodeFakeB C.F salt ikm info ikmA infoA okmA okmLen s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateE3cc hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp_eq := hx.common.sp_eq
  have hx29 := hx.common.x29_eq; have hx22 := hx.x22_eq; have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq; have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  have htag := hx.tag_32; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.common.frame
  have hpos : s.mem.read8 (hsp s₀ + 103#64) = 0#8 := by
    have heq : hsp s₀ + 103#64 = (hsp s₀ + 40#64) + 0x3f#64 := by bv_lin
    rw [heq]; exact hx.hmac_40.2.2.1
  have hcnt_136 : s.mem.read64 (hsp s₀ + 136#64) = 1#64 := by
    have heq : hsp s₀ + 136#64 = (hsp s₀ + 40#64) + 0x60#64 := by bv_lin
    rw [heq]; exact hx.hmac_40.2.2.2.2.1
  rcases cmp_ge64_lemmas hikm hpre.ikm_len with ⟨h_ikm_ule, h_ikm_ult, h_ikm_cmp, h_ikm_cbz⟩
  iterate 35 kdf_step
  let m₁ := (((((((s.mem.write64 (hsp s₀ + 16#64) (BitVec.ofNat 64 info.length)).write64
        (hsp s₀ + 304#64) 1#64).write64
        (hsp s₀ + 312#64) (s.mem.read64 (hsp s₀ + 144#64))).write64
        (hsp s₀ + 320#64) (s.mem.read64 (hsp s₀ + 152#64))).write64
        (hsp s₀ + 328#64) (s.mem.read64 (hsp s₀ + 160#64))).write64
        (hsp s₀ + 240#64) (s.mem.read64 (hsp s₀ + 72#64))).write64
        (hsp s₀ + 248#64) (s.mem.read64 (hsp s₀ + 80#64))
        |>.write64 (hsp s₀ + 256#64) (s.mem.read64 (hsp s₀ + 88#64))
        |>.write64 (hsp s₀ + 264#64) (s.mem.read64 (hsp s₀ + 96#64))
        |>.write64 (hsp s₀ + 336#64) (s.mem.read64 (hsp s₀ + 168#64))
        |>.write64 (hsp s₀ + 344#64) (s.mem.read64 (hsp s₀ + 176#64))
        |>.write64 (hsp s₀ + 208#64) (s.mem.read64 (hsp s₀ + 40#64))
        |>.write64 (hsp s₀ + 216#64) (s.mem.read64 (hsp s₀ + 48#64))
        |>.write64 (hsp s₀ + 224#64) (s.mem.read64 (hsp s₀ + 56#64))
        |>.write64 (hsp s₀ + 232#64) (s.mem.read64 (hsp s₀ + 64#64))
        |>.write64 (hsp s₀ + 272#64) (s.mem.read64 (hsp s₀ + 104#64))
        |>.write64 (hsp s₀ + 280#64) (s.mem.read64 (hsp s₀ + 112#64))
        |>.write64 (hsp s₀ + 288#64) (s.mem.read64 (hsp s₀ + 120#64))
        |>.write64 (hsp s₀ + 296#64) (s.mem.read64 (hsp s₀ + 128#64))
        |>.write64 (hsp s₀ + 304#64) (1#64 + (BitVec.ofNat 64 ikm.length >>> 6)))
  have hA1 : AgreesOutside s.mem m₁ (hsp s₀ + 16#64) 336 := by dsimp only [m₁]; prove_agrees_hsp
  have hc1 : HCommon okmLen s₀ (s.setMem m₁) :=
    HCommon.of_agreesOutside_hsp (off := 16#64) (sz := 336) hx.common hrun hsp_eq hx29 hA1 (by decide)
  have hist_272 : m₁.readBytes (hsp s₀ + 272#64) 32 = shaStateBytes (hmacInnerInit C.F (effectiveHmacKey C.F salt)) := by
    have h40 : s.mem.readBytes (hsp s₀ + 104#64) 32 = shaStateBytes (hmacInnerInit C.F (effectiveHmacKey C.F salt)) := by
      have heq : hsp s₀ + 104#64 = (hsp s₀ + 40#64) + 0x40#64 := by bv_lin
      rw [heq]; exact hx.hmac_40.2.2.2.1
    rw [readBytes_32_eq_of_read64_eq (m₂ := s.mem) (a₁ := hsp s₀ + 272#64) (a₂ := hsp s₀ + 104#64)
          (by simp (config := { decide := true }) only [m₁, arm64_norm])
          (by simp (config := { decide := true }) only [m₁, arm64_norm])
          (by simp (config := { decide := true }) only [m₁, arm64_norm])
          (by simp (config := { decide := true }) only [m₁, arm64_norm]), h40]
  obtain ⟨nBlocks, hnBlocks⟩ : ∃ nBlocks, ikm.length / 64 = nBlocks := ⟨_, rfl⟩
  obtain ⟨pfx, hpfx_def⟩ : ∃ pfx, ikm.take (64 * nBlocks) = pfx := ⟨_, rfl⟩
  obtain ⟨tail, htail_def⟩ : ∃ tail, ikm.drop (64 * nBlocks) = tail := ⟨_, rfl⟩
  obtain ⟨st', hst'_def⟩ : ∃ st', (chunks64 pfx).foldl C.F (hmacInnerInit C.F (effectiveHmacKey C.F salt)) = st' := ⟨_, rfl⟩
  have hpfx_len : pfx.length = 64 * nBlocks := by rw [← hpfx_def, List.length_take]; omega
  have htail_len : tail.length = ikm.length - 64 * nBlocks := by rw [← htail_def, List.length_drop]
  have htail_lt : tail.length < 64 := by rw [htail_len, ← hnBlocks]; omega
  have hpfx_m1 : m₁.readBytes ikmA (64 * nBlocks) = pfx := by
    have hikm_all : m₁.readBytes ikmA ikm.length = ikm := HFrame.ikm_bytes hpre hc1.frame
    simpa [hpfx_def] using readBytes_slice_of_readBytes_eq m₁ ikmA ikm hikm_all 0 (64 * nBlocks) (by omega)
  have hrw_272 : m₁.RW (hsp s₀ + 272#64) 32 := (HFrame.rw_hsp hpre hc1.frame).sub (by bv_omega)
  refine s2_compress256_multi_step_placed_429 h_compress
    hrun rfl (by kdf_reg) (by kdf_reg)
    (by have h1 := (ikm_split_lemmas hpre.ikm_len).1; simp (config := { decide := true }) only [arm64_norm, *])
    ((by kdf_reg) : _ = (blkPl_379).base + 304#64) hist_272 hpfx_m1 hst'_def hrw_272 ?_
  let m₂ := m₁.writeBytes (hsp s₀ + 272#64) (shaStateBytes st')
  have hA2 : AgreesOutside m₁ m₂ (hsp s₀ + 272#64) 32 :=
    agreesOutside_writeBytes_le m₁ (hsp s₀ + 272#64) (shaStateBytes st') 32 (by rw [shaStateBytes_length])
  have hc2 : HCommon okmLen s₀ (s.setMem m₂) :=
    HCommon.of_agreesOutside_hsp (off := 272#64) (sz := 32) hc1 hrun hsp_eq hx29 hA2 (by decide)
  have hrw2 : m₂.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc2.frame
  dsimp only [m₂, m₁] at hrw2
  iterate 5 kdf_step
  let m₃ := m₂.write8 (hsp s₀ + 271#64) (BitVec.truncate 8 (BitVec.ofNat 64 ikm.length &&& 63#64))
  have hA3 : AgreesOutside m₂ m₃ (hsp s₀ + 271#64) 1 :=
    agreesOutside_hsp_write8 (AgreesOutside.rfl' m₂ (hsp s₀ + 271#64) 1) (by decide)
  have hc3 : HCommon okmLen s₀ (s.setMem m₃) :=
    HCommon.of_agreesOutside_hsp (off := 271#64) (sz := 1) hc2 hrun hsp_eq hx29 hA3 (by decide)
  have htail_off_eq : (BitVec.ofNat 64 ikm.length &&& 9223372036854775744#64) =
      BitVec.ofNat 64 (64 * nBlocks) := by
    rw [(ikm_split_lemmas hpre.ikm_len).2.2.1, hnBlocks]
  have htail_m3 : m₃.readBytes (ikmA + (BitVec.ofNat 64 ikm.length &&& 9223372036854775744#64)) tail.length = tail := by
    have hikm_all : m₃.readBytes ikmA ikm.length = ikm := HFrame.ikm_bytes hpre hc3.frame
    have hslice := readBytes_slice_of_readBytes_eq m₃ ikmA ikm hikm_all (64 * nBlocks) tail.length (by omega)
    rw [htail_off_eq]
    have htake : List.take tail.length (List.drop (64 * nBlocks) ikm) = tail := by rw [htail_def, List.take_length]
    simpa [htake] using hslice
  have hrw_tail : m₃.RW (hsp s₀ + 208#64) tail.length :=
    (HFrame.rw_hsp hpre hc3.frame).sub (by clear * - htail_lt; bv_omega)
  have hread_tail : m₃.Readable (ikmA + (BitVec.ofNat 64 ikm.length &&& 9223372036854775744#64)) tail.length := by
    have hrd_all : m₃.Readable ikmA ikm.length :=
      (Frame.readable_iff hc3.frame _ _).mpr hread_ikm
    rw [htail_off_eq]
    exact fun a ha => hrd_all a (inRegion_sub_slice (by omega) (by have := hpre.ikm_len; omega) ha)
  have hdisj_tail : tail.length = 0 ∨
      DisjointRegions (hsp s₀ + 208#64) tail.length
        (ikmA + (BitVec.ofNat 64 ikm.length &&& 9223372036854775744#64)) tail.length := by
    by_cases h0 : tail.length = 0
    · exact Or.inl h0
    · rw [htail_off_eq]
      have hout_tail : ∀ a, InRegion (ikmA + BitVec.ofNat 64 (64 * nBlocks)) tail.length a →
          OutsideRegion (hsp s₀ - 544#64) 1232 a := fun a ha =>
        hpre.out_ikm_stk a (inRegion_sub_slice (by omega) (by have := hpre.ikm_len; omega) ha)
      exact Or.inr ((disjointRegions_of_outside (by omega) (by decide) hout_tail).symm.sub_left
        (hsp s₀ + 208#64) ⟨by omega, by clear * - htail_lt; bv_omega⟩)
  refine s2_memcpy_step_placed_429_exact h_mc
    hrun rfl (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, *])
    (by kdf_reg) (by kdf_reg)
    (by have h4 := (ikm_split_lemmas hpre.ikm_len).2.2.2.1; simp (config := { decide := true }) only [arm64_norm, *])
    ((by kdf_reg) : _ = (blkPl_379).base + 324#64) htail_m3 hrw_tail hread_tail hdisj_tail fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₄ := m₃.writeBytes (hsp s₀ + 208#64) tail
  have hA4 : AgreesOutside m₃ m₄ (hsp s₀ + 208#64) 63 :=
    agreesOutside_writeBytes_le m₃ (hsp s₀ + 208#64) tail 63 (by omega)
  have hc4 : HCommon okmLen s₀ (s.setMem m₄) :=
    HCommon.of_agreesOutside_hsp (off := 208#64) (sz := 63) hc3 hrun hsp_eq hx29 hA4 (by decide)
  have hrw4 : m₄.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc4.frame
  have hm16_2 : m₂.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    rw [hA2.read64_eq (by unfold DisjointRegions; bv_omega)]; simp (config := { decide := true }) only [m₁, arm64_norm]
  have hm16_3 : m₃.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    rw [hA3.read64_eq (by unfold DisjointRegions; bv_omega)]; exact hm16_2
  have hm16_4 : m₄.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    rw [hA4.read64_eq (by unfold DisjointRegions; bv_omega)]; exact hm16_3
  have hm16_4_raw := hm16_4
  dsimp only [m₄, m₃, m₂, m₁] at hrw4 hm16_4_raw
  iterate 1 kdf_step
  rcases ikm_split_lemmas hpre.ikm_len with ⟨h_shr_nat, h_cnt_add, h_and_hi, h_and_lo_nat, h_and_lo_tr8⟩
  refine RunsTo.refl ?_
  refine ⟨by kdf_reg, ⟨by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [mem_setMem]; exact hc4.saved, by rw [mem_setMem]; exact hc4.frame⟩,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [mem_setMem]; exact hm16_4, ?_⟩
  rw [mem_setMem]
  have hikm_app : pfx ++ tail = ikm := by rw [← hpfx_def, ← htail_def, List.take_append_drop]
  refine ⟨pfx, tail, hikm_app, by omega, htail_lt, by omega, htail_lt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact readBytes_writeBytes_same m₃ (hsp s₀ + 208#64) tail (by omega)
  · have h271 : (hsp s₀ + 208#64) + 0x3f#64 = hsp s₀ + 271#64 := by bv_lin
    have hout : OutsideRegion (hsp s₀ + 208#64) 63 (hsp s₀ + 271#64) := by simp only [OutsideRegion]; bv_omega
    rw [h271, hA4.1 _ hout, Memory.read8_write8_same, h_and_lo_tr8, hnBlocks, ← htail_len]
  · have h272 : (hsp s₀ + 208#64) + 0x40#64 = hsp s₀ + 272#64 := by bv_lin
    rw [h272, hA4.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hA3.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide), hst'_def]
    have hlen : (shaStateBytes st').length = 32 := shaStateBytes_length _
    conv_lhs => rw [← hlen]
    exact readBytes_writeBytes_same m₁ (hsp s₀ + 272#64) (shaStateBytes st') (by rw [hlen]; decide)
  · have h304 : (hsp s₀ + 208#64) + 0x60#64 = hsp s₀ + 304#64 := by bv_lin
    rw [h304, hA4.read64_eq (by unfold DisjointRegions; bv_omega),
        hA3.read64_eq (by unfold DisjointRegions; bv_omega),
        hA2.read64_eq (by unfold DisjointRegions; bv_omega)]
    have hm1_304 : m₁.read64 (hsp s₀ + 304#64) = 1#64 + (BitVec.ofNat 64 ikm.length >>> 6) := by
      simp (config := { decide := true }) only [m₁, arm64_norm]
    have hpfx_div : pfx.length / 64 = nBlocks := by omega
    rw [hm1_304, h_cnt_add, hnBlocks, hpfx_div]
  · have h312 : (hsp s₀ + 208#64) + 0x68#64 = hsp s₀ + 312#64 := by bv_lin
    rw [h312, hA4.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hA3.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        readBytes_32_eq_of_read64_eq (m₂ := s.mem) (a₁ := hsp s₀ + 312#64) (a₂ := (hsp s₀ + 40#64) + 0x68#64)
          (by simp (config := { decide := true }) only [m₁, arm64_norm])
          (by simp (config := { decide := true }) only [m₁, arm64_norm])
          (by simp (config := { decide := true }) only [m₁, arm64_norm])
          (by simp (config := { decide := true }) only [m₁, arm64_norm])]
    exact hx.hmac_40.2.2.2.2.2.1
  · have h344 : (hsp s₀ + 208#64) + 0x88#64 = hsp s₀ + 344#64 := by bv_lin
    have h176 : hsp s₀ + 176#64 = (hsp s₀ + 40#64) + 0x88#64 := by bv_lin
    rw [h344, hA4.read64_eq (by unfold DisjointRegions; bv_omega),
        hA3.read64_eq (by unfold DisjointRegions; bv_omega),
        hA2.read64_eq (by unfold DisjointRegions; bv_omega)]
    have hm1_344 : m₁.read64 (hsp s₀ + 344#64) = s.mem.read64 (hsp s₀ + 176#64) := by
      simp (config := { decide := true }) only [m₁, arm64_norm]
    rw [hm1_344, h176]; exact hx.hmac_40.2.2.2.2.2.2

theorem seg_e1_placed_runsTo_exact [LibsignalPlacement] {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hread_ikm : s₀.mem.Readable ikmA ikm.length)
    (hx : StateERet1 hkdfCodeFakeB C.F salt ikm info ikmA infoA okmA okmLen s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateE3cc hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) := by
  by_cases hikm : ikm.length < 64
  · exact seg_e1_lt56_placed_runsTo_exact h_mc hpre hread_ikm hikm hx
  · exact seg_e1_eq64_placed_runsTo_exact h_mc h_compress hpre hread_ikm (by omega) hx

end ExtractExactSegments

end LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractExact
