/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpand -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractExact -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon

/-!
# `HookSatExactMemcpy` Siblings of `SpqrV1.Kdf.HkdfToSliceExpand` (`HkdfToSliceExpandExact`, Block `379`)

- **Role:** `Role::Proof` (untrusted proof module outside the TCB; #1255 mc2 Cone 3).
- **Overview:**
  Replaces `h_memcpy : H lsMemcpySym = some memcpyHook` on Expand Block-1 `memcpy` segments
  (`seg_b1b_placed_runsTo` and `seg_b1d_placed_runsTo`) of Block `379` (`spqr::kdf::hkdf_to_slice`)
  with `(h_mc : HookSatExactMemcpy H lsMemcpySym)` via `s2_memcpy_step_placed_429_exact`, keeping all
  cut predicates (`StateB1Memcpy`, `StateB1Fin`, `StateB1RetFin`, `StateB1Done`) **100% unchanged**.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpandExact

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPC_379 blkPl_379 blkPl_425 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (hkdfExtractBytes)
open CryptoVerification.LibsignalTripleRatchet
  (Frame HmacSt RunsTo TraceEq TraceEq.advancePC_step TraceEq.refl TraceEq.setMem_step
   TraceEq.setPC_step TraceEq.setPState_step TraceEq.writeReg32_step TraceEq.writeReg64_step
   TraceEq.writeVReg128_step lsMemcpySym rw_of_perm_eq zeroExtend64_truncate32_ofNat64)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (agreesOutside_writeBytes_le and64_255_ofNat64 and_0xffffffffff_ofNat64 cmp32_lt63_lemmas
   mem_setMem t1 t1_length zeroExtend64_add1_truncate32_ofNat64
   zeroExtend64_and255_truncate32_ofNat64)
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
  (HExpCommon HFrame HPre StateB1Done StateB1Fin StateB1Memcpy StateB1RetFin bv_sub_add_lit_ge
   canWrite_hsp_352_add hkdfCodeFakeB hsp hsp_aligned readBytes_32_hsp_508_of_540)
open scoped CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
open LibsignalBinary.Heap.MuslMemOpsRunsTo (applyMemcpyClobber)
open scoped LibsignalBinary.Heap.MuslMemOpsRunsToPlaced
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractExact
  (disjointRegions_of_outside readable_of_rw s2_memcpy_step_placed_429_exact)

attribute [local simp, local arm64_norm] bv_sub_add_lit hkdfCodeFakeB bv_sub_add_lit_ge

@[local simp, local arm64_norm]
private theorem lsmpl_base_425 [LibsignalPlacement] : lsmpl.base 425 = (blkPl_425).base := rfl

section ExpandExactSegments

variable {C : Crypto}

theorem seg_b1b_placed_runsTo_exact [LibsignalPlacement] {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    {b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hread_info₀ : s₀.mem.Readable infoA info.length)
    (hx : StateB1Memcpy hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ s (lsρ lsMemcpySym)) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateB1Fin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ · (blkPl_425).base) := by
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status
  have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hlr := hx.lr_eq
  have hx0 := hx.x0_eq; have hx1 := hx.x1_eq; have hx2 := hx.x2_eq
  have hx20 := hx.x20_eq; have hx21 := hx.x21_eq; have hx22 := hx.x22_eq
  have hx24 := hx.x24_eq; have hx25 := hx.x25_eq; have hx28 := hx.x28_eq
  have hhsp := hsp_aligned hpre.sp_aligned; have hinfo_lt := hpre.info_lt
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.exp.common.frame
  have hrw_dst : s.mem.RW (hsp s₀ + 352#64) info.length := hrw_hsp.sub (by bv_omega)
  have hread_info : s.mem.readBytes infoA info.length = info := HFrame.info_bytes hpre hx.exp.common.frame
  have hx2_nat : (s.readReg64 .x2).toNat = info.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrd_src : s.mem.Readable infoA info.length :=
    (Frame.readable_iff hx.exp.common.frame _ _).mpr hread_info₀
  have hdisj_info : info.length = 0 ∨ DisjointRegions (hsp s₀ + 352#64) info.length infoA info.length :=
    Or.inr ((disjointRegions_of_outside (by have := hpre.info_ge; omega) (by decide) hpre.out_info_stk).symm.sub_left
      (hsp s₀ + 352#64) ⟨by have := hpre.info_ge; omega, by bv_omega⟩)
  refine s2_memcpy_step_placed_429_exact h_mc hrun hpc
    (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, *])
    hx0 hx1 hx2_nat hlr hread_info hrw_dst hrd_src hdisj_info fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₁ := s.mem.writeBytes (hsp s₀ + 352#64) info
  have hA1 : AgreesOutside s.mem m₁ (hsp s₀ + 352#64) 55 :=
    agreesOutside_writeBytes_le s.mem (hsp s₀ + 352#64) info 55 (by omega)
  have hrw_wb : m₁.RW (hsp s₀) 688 := rw_of_perm_eq hA1.2 hrw_hsp
  rcases canWrite_hsp_352_add hrw_wb (by omega : info.length < 64) with ⟨hcw_pos1, hcw_pos2⟩
  dsimp only [m₁] at hrw_wb hcw_pos1 hcw_pos2
  have hze32 := zeroExtend64_truncate32_ofNat64 (by omega : info.length < 64)
  have hand255 := zeroExtend64_and255_truncate32_ofNat64 (by omega : info.length < 64)
  have hand64_255 := and64_255_ofNat64 (by omega : info.length < 64)
  have hand40 := and_0xffffffffff_ofNat64 (by omega : info.length < 64)
  rcases cmp32_lt63_lemmas (by omega : info.length < 63) with ⟨hcmp63_eq, hcmp63_ne, hcmp63_z⟩
  have hadd1 := zeroExtend64_add1_truncate32_ofNat64 (by omega : info.length < 63)
  iterate 26 kdf_step
  refine RunsTo.refl ?_
  have hc1 : HExpCommon C.F (hkdfExtractBytes C.F salt ikm) info infoA okmLen s₀ (s.setMem m₁) :=
    HExpCommon.of_agreesOutside_352_592 (off := 352#64) (sz := 55) hx.exp
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp_eq)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [mem_setMem]; exact hA1) (by decide)
  have hhm_m2 : HmacSt
      ((((m₁.write8 (hsp s₀ + 415#64) (BitVec.ofNat 8 info.length)).write8
        (hsp s₀ + 32#64) 1#8).write8
        (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) 1#8).write8
        (hsp s₀ + 415#64) (BitVec.ofNat 8 (info.length + 1)))
      (hsp s₀ + 352#64) C.F (hkdfExtractBytes C.F salt ikm) (info ++ [1#8]) :=
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.HmacSt.of_memcpy_counter_352 hx.hmac_352 hinfo_lt
  refine ⟨by kdf_reg,
    HExpCommon.of_agreesOutside_32_560 (off := 32#64) (sz := 560) hc1
      (by kdf_reg) (by kdf_reg) (by kdf_reg) (by prove_agrees_hsp) (by decide)
      (by prove_hmac_208 hc1.hmac_208),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg,
    by
      rw [State.readReg64_setMem]
      simp (config := { decide := true }) only [arm64_norm]
      rcases hpre.okm_len with rfl | rfl | rfl <;> rfl,
    by kdf_reg, ?_⟩
  simp only [mem_setMem]
  exact CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.HmacSt.of_copy_352_32 hhm_m2
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])
    (by simp (config := { decide := true }) only [m₁, arm64_norm])

theorem seg_b1d_placed_runsTo_exact [LibsignalPlacement] {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    {b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hx : StateB1RetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateB1Done hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status
  have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hx21 := hx.x21_eq; have hx22 := hx.x22_eq; have hx24 := hx.x24_eq
  have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx28 := hx.x28_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_okm : s.mem.RW okmA okmLen := HFrame.rw_okm hpre hx.exp.common.frame
  have hrw_dst : s.mem.RW okmA 32 := hrw_okm.sub (by have := hpre.okm_len; bv_omega)
  have hrd_src : s.mem.Readable (hsp s₀ + 540#64) 32 :=
    readable_of_rw ((HFrame.rw_hsp hpre hx.exp.common.frame).sub (by bv_omega))
  have hdisj_dst : 32 = 0 ∨ DisjointRegions okmA 32 (hsp s₀ + 540#64) 32 :=
    Or.inr ((hpre.disj_okm_stk.sub_left okmA
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right
      (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩)
  iterate 4 kdf_step
  refine s2_memcpy_step_placed_429_exact h_mc hrun rfl
    (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, *])
    rfl rfl rfl rfl hx.t1_540 hrw_dst hrd_src hdisj_dst fun c => ?_
  dsimp only [applyMemcpyClobber]
  let prk := hkdfExtractBytes C.F salt ikm
  let m₁ := s.mem.writeBytes okmA (t1 C.F prk info)
  have hA1 : AgreesOutside s.mem m₁ (okmA + 0#64) 32 := by
    rw [BitVec.add_zero]
    exact agreesOutside_writeBytes_le s.mem okmA (t1 C.F prk info) 32
      (by rw [t1_length])
  have hc1 : HExpCommon C.F prk info infoA okmLen s₀ (s.setMem m₁) :=
    HExpCommon.of_agreesOutside_okm hpre hx.exp hrun hsp_eq hx29 hA1
      ⟨by decide, by have := hpre.okm_len; rw [BitVec.toNat_zero, Nat.zero_add]; omega⟩
  have hm24_1 : m₁.read64 (hsp s₀ + 24#64) = hsp s₀ + 508#64 := hc1.m24_eq
  have hrw1_hsp : m₁.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc1.common.frame
  dsimp only [m₁, prk] at hm24_1 hrw1_hsp
  iterate 5 kdf_step
  refine RunsTo.refl ?_
  refine ⟨by kdf_reg,
    HExpCommon.of_agreesOutside_352_592 (off := 508#64) (sz := 32) hc1
      (by kdf_reg) (by kdf_reg) (by kdf_reg) (by prove_agrees_hsp) (by decide),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, ?_, ?_⟩
  · simp only [mem_setMem]
    have ht1_m1 : m₁.readBytes (hsp s₀ + 540#64) 32 = t1 C.F prk info := by
      have hd : DisjointRegions (okmA + 0#64) 32 (hsp s₀ + 540#64) 32 := by
        rw [BitVec.add_zero]
        exact (hpre.disj_okm_stk.sub_left okmA
          ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (hsp s₀ + 540#64)
          ⟨by decide, by bv_omega⟩
      exact (hA1.readBytes_eq hd (by decide)).trans hx.t1_540
    exact readBytes_32_hsp_508_of_540 ht1_m1
      (by simp (config := { decide := true }) only [m₁, prk, arm64_norm])
      (by simp (config := { decide := true }) only [m₁, prk, arm64_norm])
      (by simp (config := { decide := true }) only [m₁, prk, arm64_norm])
      (by simp (config := { decide := true }) only [m₁, prk, arm64_norm])
  · have hd : DisjointRegions (hsp s₀ + 508#64) 32 okmA 32 :=
      (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 508#64)
        ⟨by decide, by bv_omega⟩).sub_right okmA
        ⟨by decide, by have := hpre.okm_len; bv_omega⟩
    have hA2 : AgreesOutside m₁
        ((((m₁.write64 (hsp s₀ + 508#64) (m₁.read64 (hsp s₀ + 540#64))).write64
          (hsp s₀ + 516#64) (m₁.read64 (hsp s₀ + 548#64))).write64
          (hsp s₀ + 524#64) (m₁.read64 (hsp s₀ + 556#64))).write64
          (hsp s₀ + 532#64) (m₁.read64 (hsp s₀ + 564#64)))
        (hsp s₀ + 508#64) 32 := by
      prove_agrees_hsp
    dsimp only [mem_setMem]
    refine (hA2.readBytes_eq hd (by decide)).trans ?_
    dsimp only [m₁, prk]
    conv_lhs => rw [← t1_length C.F (hkdfExtractBytes C.F salt ikm) info]
    exact readBytes_writeBytes_same s.mem okmA
      (t1 C.F (hkdfExtractBytes C.F salt ikm) info)
      (by rw [t1_length]; decide)

end ExpandExactSegments

end LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpandExact
