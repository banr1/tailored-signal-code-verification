/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceFirstHalf
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGen
import ProofLib.SepLogic.WPp

/-!
# `spqr::kdf::hkdf_to_slice`: Extract Completion and Expand Block 1

Proves the final HKDF-Extract segments (`0x633cc → 0x634fc`) and the first HKDF-Expand block `T(1)`
(`0x634fc → 0x636f0`) of `spqr::kdf::hkdf_to_slice`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.FinalizeFixed3Proof
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof

@[local simp, local arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [(ls_off% hkdfToSliceName + 328) → (ls_off% hkdfToSliceName + 1148)]

attribute [local simp, local arm64_norm] bv_sub_add_lit hkdfCodeFakeB bv_sub_add_lit_ge

@[local simp, local arm64_norm]
private theorem lsmpl_base_452 [LibsignalPlacement] : lsmpl.base 402 = (blkPl_402).base := rfl

@[local simp, local arm64_norm]
private theorem lsmpl_base_475 [LibsignalPlacement] : lsmpl.base 425 = (blkPl_425).base := rfl

/-! ## Extract Phase Completion (`0x633cc → 0x634fc`) -/

variable {b : BitVec 64} {C : Crypto} {ext : String → Option (State → State)}

theorem HmacStN.of_copy_208_32 {m₀ m : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key pfx tail : List (BitVec 8)}
    (hsrc : HmacStN m₀ (hsp s₀ + 208#64) F key pfx tail)
    (h0   : m.read64 (hsp s₀ + 32#64)  = m₀.read64 (hsp s₀ + 208#64))
    (h8   : m.read64 (hsp s₀ + 40#64)  = m₀.read64 (hsp s₀ + 216#64))
    (h16  : m.read64 (hsp s₀ + 48#64)  = m₀.read64 (hsp s₀ + 224#64))
    (h24  : m.read64 (hsp s₀ + 56#64)  = m₀.read64 (hsp s₀ + 232#64))
    (h32  : m.read64 (hsp s₀ + 64#64)  = m₀.read64 (hsp s₀ + 240#64))
    (h40  : m.read64 (hsp s₀ + 72#64)  = m₀.read64 (hsp s₀ + 248#64))
    (h48  : m.read64 (hsp s₀ + 80#64)  = m₀.read64 (hsp s₀ + 256#64))
    (h56  : m.read64 (hsp s₀ + 88#64)  = m₀.read64 (hsp s₀ + 264#64))
    (h64  : m.read64 (hsp s₀ + 96#64)  = m₀.read64 (hsp s₀ + 272#64))
    (h72  : m.read64 (hsp s₀ + 104#64) = m₀.read64 (hsp s₀ + 280#64))
    (h80  : m.read64 (hsp s₀ + 112#64) = m₀.read64 (hsp s₀ + 288#64))
    (h88  : m.read64 (hsp s₀ + 120#64) = m₀.read64 (hsp s₀ + 296#64))
    (h96  : m.read64 (hsp s₀ + 128#64) = m₀.read64 (hsp s₀ + 304#64))
    (h104 : m.read64 (hsp s₀ + 136#64) = m₀.read64 (hsp s₀ + 312#64))
    (h112 : m.read64 (hsp s₀ + 144#64) = m₀.read64 (hsp s₀ + 320#64))
    (h120 : m.read64 (hsp s₀ + 152#64) = m₀.read64 (hsp s₀ + 328#64))
    (h128 : m.read64 (hsp s₀ + 160#64) = m₀.read64 (hsp s₀ + 336#64))
    (h136 : m.read64 (hsp s₀ + 168#64) = m₀.read64 (hsp s₀ + 344#64)) :
    HmacStN m (hsp s₀ + 32#64) F key pfx tail :=
  HmacStN.of_copy_19 hsrc h0
    (Expand.read64_add_off h8) (Expand.read64_add_off h16) (Expand.read64_add_off h24)
    (Expand.read64_add_off h32) (Expand.read64_add_off h40) (Expand.read64_add_off h48)
    (Expand.read64_add_off h56) (Expand.read64_add_off h64) (Expand.read64_add_off h72)
    (Expand.read64_add_off h80) (Expand.read64_add_off h88) (Expand.read64_add_off h96)
    (Expand.read64_add_off h104) (Expand.read64_add_off h112) (Expand.read64_add_off h120)
    (Expand.read64_add_off h128) (Expand.read64_add_off h136)

set_option hygiene false in
local macro "hkdf_seg_e1d_body" : tactic => `(tactic| (
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp_eq := hx.common.sp_eq; have hx29 := hx.common.x29_eq
  have hx19 := hx.x19_eq; have hx22 := hx.x22_eq; have hx25 := hx.x25_eq
  have hx26 := hx.x26_eq; have hx27 := hx.x27_eq; have hm16 := hx.m16_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.common.frame
  iterate 13 kdf_step
  refine RunsTo.refl ?_
  refine ⟨by kdf_reg,
    HCommon.of_agreesOutside_hsp (off := 32#64) (sz := 0x90) hx.common
      (by kdf_reg) (by kdf_reg) (by kdf_reg) (by prove_agrees_hsp) (by decide),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by simp (config := { decide := true }) only [arm64_norm, hm16], ?_⟩
  rcases hx.hmac_208 with ⟨pfx, tail, hpt, hmod, hlt, hhm⟩
  refine ⟨pfx, tail, hpt, hmod, hlt, ?_⟩
  simp only [Expand.mem_setMem]
  refine HmacStN.of_copy_208_32 hhm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := { decide := true }) only [arm64_norm]))

/-- Segment `E1d` (`b + 0x633cc` → `b + 0x6ce50`, 13 steps): copies `Hmac` from `hsp s₀ + 208#64`
to `hsp s₀ + 32#64` and calls `finalize_fixed(hsp s₀ + 507#64, hsp s₀ + 32#64)`. -/
theorem seg_e1d_runsTo [HkdfHooks C.F ext] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateE3cc b C.F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateEFin b C.F salt ikm info infoA okmA okmLen s₀) := by
  hkdf_seg_e1d_body

theorem seg_e1d_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    {b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hx : StateE3cc hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateEFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ · (blkPl_425).base) := by
  hkdf_seg_e1d_body

/-- `finalize_fixed` in Extract (`b + 0x6ce50` → `b + 0x63400`): produces
`PRK = hkdfExtractBytes C.F salt ikm` at `hsp s₀ + 507#64`. -/
theorem fin_extract_runsTo [HkdfHooks C.F ext] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateEFin b C.F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateERetFin b C.F salt ikm info infoA okmA okmLen s₀) := by
  rcases hx.hmac_32 with ⟨pfx, tail, hpt, hmod, hlt, hhm⟩
  have hrw_hsp := HFrame.rw_hsp hpre hx.common.frame
  have hrw_sub := HFrame.rw_sub_544 hpre hx.common.frame
  have hfin_pre : FinPre3PfxGen b C.F (effectiveHmacKey C.F salt) pfx tail s :=
    { pc_eq := hx.pc_eq, status := hx.common.status, key_le := effectiveHmacKey_length_le C.F salt,
      tail_lt := hlt, hmac_st := by rw [hx.x1_eq]; exact hhm,
      rw_out := by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega),
      rw_hm := by rw [hx.x1_eq]; exact hrw_hsp.sub (by bv_omega),
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sub.sub (by bv_omega),
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; unfold DisjointRegions; bv_omega,
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; unfold DisjointRegions; bv_omega,
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; unfold DisjointRegions; bv_omega,
      sp_aligned := by rw [hx.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1 }
  refine (FinalizeFixed3GenProof.finalize_fixed3_pfx_lt64_runsTo_ext (ext := ext) hfin_pre).mono
    fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, hpt, hmacWith_effectiveHmacKey] at hout
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq] at hfr
  have hm16' : s'.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    refine (Expand.Frame.read64_eq hfr fun r hr => ?_).trans hx.m16_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  exact ⟨hpc', HCommon.of_fin_frame (outOff := 507#64) hx.common hrun' hcs hfr (by decide),
    (CalleeSaved.x19 hcs).trans hx.x19_eq, (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x25 hcs).trans hx.x25_eq, (CalleeSaved.x26 hcs).trans hx.x26_eq,
    (CalleeSaved.x27 hcs).trans hx.x27_eq, hm16', hout⟩

theorem fin_extract_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {b_iv : BitVec 64} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv
      (LibsignalCodeLoaded lsmpl s₀.mem))
    (hx : StateEFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ s (blkPl_425).base) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateERetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) := by
  have : HkdfPlacedHooks C.F H :=
    { memset := h_memset, memcpy := h_memcpy, compress256 := h_compress }
  rcases hx.hmac_32 with ⟨pfx, tail, hpt, hmod, hlt, hhm⟩
  have hrw_hsp := HFrame.rw_hsp hpre hx.common.frame
  have hrw_sub := HFrame.rw_sub_544 hpre hx.common.frame
  have hfin_pre : FinPre3PfxGen fin3PlacedFakeB C.F (effectiveHmacKey C.F salt) pfx tail s :=
    { pc_eq := by rw [fin3PlacedFakeB_off_0]; exact hx.pc_eq, status := hx.common.status,
      key_le := effectiveHmacKey_length_le C.F salt, tail_lt := hlt,
      hmac_st := by rw [hx.x1_eq]; exact hhm,
      rw_out := by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega),
      rw_hm := by rw [hx.x1_eq]; exact hrw_hsp.sub (by bv_omega),
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sub.sub (by bv_omega),
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; unfold DisjointRegions; bv_omega,
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; unfold DisjointRegions; bv_omega,
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; unfold DisjointRegions; bv_omega,
      sp_aligned := by rw [hx.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1 }
  have hcl_s : LibsignalCodeLoaded lsmpl s.mem :=
    CryptoVerification.LibsignalCodeLoaded.of_keepsFrozenNoAnon hpre.base_al (HFrame.keepsFrozen hpre hx.common.frame)
  refine (RunsTo.of_other_block hcl_s
    (FinalizeFixed3GenProof.finalize_fixed3_pfx_lt64_placed_runsTo hfin_pre)
    (by decide) (by decide) (by decide)).mono fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, hpt, hmacWith_effectiveHmacKey] at hout
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq] at hfr
  have hm16' : s'.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    refine (Expand.Frame.read64_eq hfr fun r hr => ?_).trans hx.m16_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  exact ⟨hpc', HCommon.of_fin_frame (outOff := 507#64) hx.common hrun' hcs hfr (by decide),
    (CalleeSaved.x19 hcs).trans hx.x19_eq, (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x25 hcs).trans hx.x25_eq, (CalleeSaved.x26 hcs).trans hx.x26_eq,
    (CalleeSaved.x27 hcs).trans hx.x27_eq, hm16', hout⟩

set_option hygiene false in
local macro "hkdf_seg_e2_body" : tactic => `(tactic| (
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp_eq := hx.common.sp_eq; have hx29 := hx.common.x29_eq
  have hx19 := hx.x19_eq; have hx22 := hx.x22_eq; have hx25 := hx.x25_eq
  have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  iterate 4 kdf_step
  refine RunsTo.refl ?_
  exact ⟨by kdf_reg, ⟨by kdf_reg, by kdf_reg, by kdf_reg, hx.common.saved, hx.common.frame⟩,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, hx.m16_eq, hx.prk_507⟩))

/-- Segment `E2` (`b + 0x63400` → `b + 0x66fa0`, 4 steps): sets up `new_from_slice` #2 with
`x0 = hsp s₀ + 352#64`, `x1 = hsp s₀ + 507#64`, `x2 = 32#64`. -/
theorem seg_e2_runsTo [HkdfHooks C.F ext] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateERetFin b C.F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateENfs2 b C.F salt ikm info infoA okmA okmLen s₀) := by
  hkdf_seg_e2_body

theorem seg_e2_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    {b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hx : StateERetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateENfs2 hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ · (blkPl_402).base) := by
  hkdf_seg_e2_body

/-- `new_from_slice` #2 (`pc_nfs` → `b + 0x63410`): initializes
`Hmac(hkdfExtractBytes C.F salt ikm, [])` at `hsp s₀ + 360#64`. -/
theorem nfs2_runsTo {P : Program} {b_iv pc_nfs : BitVec 64}
    {aligned : Prop} {alignedM : Memory → Prop}
    (hNfs : Nfs3GenRunsToProg P b_iv pc_nfs alignedM C.F)
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hx : StateENfs2 b C.F salt ikm info infoA okmA okmLen s₀ s pc_nfs)
    (hal : ∀ {m}, Expand.KeepsFrozenNoAnon s₀.mem m → alignedM m := by intro _; exact hpre.base_al) :
    RunsTo P s
      (StateERet2 b C.F salt ikm info infoA okmA okmLen s₀) := by
  have hx2_nat : (s.readReg64 .x2).toNat = 32 := by rw [hx.x2_eq]; rfl
  have hrw_hsp := HFrame.rw_hsp hpre hx.common.frame
  have hrun := hNfs hx.pc_eq hx.common.status
    (by rw [hx2_nat]; decide)
    (HFrame.ro_iv_bytes hpre hx.common.frame)
    (hal (HFrame.keepsFrozen hpre hx.common.frame))
    (HFrame.ro_iv_read hpre hx.common.frame)
    (by rw [hx.common.sp_eq]
        exact hpre.disj_iv_stk.sub_right (hsp s₀ - 544#64) ⟨by decide, by bv_omega⟩)
    (by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega))
    (by rw [hx.common.sp_eq]; exact HFrame.rw_sub_544 hpre hx.common.frame)
    (by rw [hx.x0_eq, hx.common.sp_eq]; unfold DisjointRegions; bv_omega)
    (by rw [hx.x1_eq, hx2_nat, hx.common.sp_eq]
        exact Or.inr (by unfold DisjointRegions; bv_omega))
    (by rw [hx.x1_eq, hx2_nat, hx.x0_eq]
        exact Or.inr (by unfold DisjointRegions; bv_omega))
    (by rw [hx.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1)
  refine hrun.mono fun s' ⟨hpc', hrun', hcs, htag, hhm, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'
  rw [hx.x0_eq] at htag
  have hx0_8 : s.readReg64 .x0 + 8#64 = hsp s₀ + 360#64 := by rw [hx.x0_eq]; bv_lin
  have hprk_s : s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat =
      hkdfExtractBytes C.F salt ikm := by
    rw [hx.x1_eq, hx2_nat]
    exact hx.prk_507
  rw [hx0_8, hprk_s, effectiveHmacKey_of_le C.F (by simp [hkdfExtractBytes, hmacWith])] at hhm
  rw [hx.x0_eq, hx.common.sp_eq] at hfr
  have hm16' : s'.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    refine (Expand.Frame.read64_eq hfr fun r hr => ?_).trans hx.m16_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  exact ⟨hpc',
    HCommon.of_nfs_frame (retOff := 352#64) hx.common hrun' hcs hfr (by decide),
    (CalleeSaved.x19 hcs).trans hx.x19_eq,
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x25 hcs).trans hx.x25_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq,
    (CalleeSaved.x27 hcs).trans hx.x27_eq,
    hm16', htag, hhm⟩

private theorem okmLen_cmp_lemmas {okmLen : ℕ}
    (hokm : okmLen = 32 ∨ okmLen = 64 ∨ okmLen = 96) :
    (AddWithCarry64 (BitVec.ofNat 64 okmLen + 18446744073709543455#64) 8159#64 true).2.c = true ∧
    BitVec.ule 18446744073709543456#64 (BitVec.ofNat 64 okmLen + 18446744073709543455#64) = true ∧
    BitVec.ult (BitVec.ofNat 64 okmLen + 18446744073709543455#64) 18446744073709543456#64 = false := by
  rcases hokm with rfl | rfl | rfl <;> decide

theorem agreesOutside_hsp_write64_zero {m₁ m₂ : Memory} {s₀ : State} {off v : BitVec 64} {sz : ℕ}
    (h : AgreesOutside m₁ m₂ (hsp s₀ + off) sz)
    (hw : decide (off.toNat = 0 ∧ 8 ≤ sz ∧ sz ≤ 688) = true) :
    AgreesOutside m₁ (m₂.write64 (hsp s₀) v) (hsp s₀ + off) sz := by
  have ⟨h1, h2, h3⟩ := of_decide_eq_true hw
  exact h.write64 (by bv_omega) (by omega)

theorem HmacSt.of_copy_empty_360_208 {m₀ m : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key : List (BitVec 8)}
    (hsrc : HmacSt m₀ (hsp s₀ + 360#64) F key [])
    (h56  : m.read64 (hsp s₀ + 264#64) = m₀.read64 (hsp s₀ + 416#64))
    (h64  : m.read64 (hsp s₀ + 272#64) = m₀.read64 (hsp s₀ + 424#64))
    (h72  : m.read64 (hsp s₀ + 280#64) = m₀.read64 (hsp s₀ + 432#64))
    (h80  : m.read64 (hsp s₀ + 288#64) = m₀.read64 (hsp s₀ + 440#64))
    (h88  : m.read64 (hsp s₀ + 296#64) = m₀.read64 (hsp s₀ + 448#64))
    (h96  : m.read64 (hsp s₀ + 304#64) = m₀.read64 (hsp s₀ + 456#64))
    (h104 : m.read64 (hsp s₀ + 312#64) = m₀.read64 (hsp s₀ + 464#64))
    (h112 : m.read64 (hsp s₀ + 320#64) = m₀.read64 (hsp s₀ + 472#64))
    (h120 : m.read64 (hsp s₀ + 328#64) = m₀.read64 (hsp s₀ + 480#64))
    (h128 : m.read64 (hsp s₀ + 336#64) = m₀.read64 (hsp s₀ + 488#64))
    (h136 : m.read64 (hsp s₀ + 344#64) = m₀.read64 (hsp s₀ + 496#64)) :
    HmacSt m (hsp s₀ + 208#64) F key [] :=
  HmacSt.of_copy_empty hsrc
    (Expand.read64_add_off h56) (Expand.read64_add_off h64) (Expand.read64_add_off h72)
    (Expand.read64_add_off h80) (Expand.read64_add_off h88) (Expand.read64_add_off h96)
    (Expand.read64_add_off h104) (Expand.read64_add_off h112) (Expand.read64_add_off h120)
    (Expand.read64_add_off h128) (Expand.read64_add_off h136)

set_option hygiene false in
local macro "hkdf_seg_e3_body" : tactic => `(tactic| (
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp_eq := hx.common.sp_eq; have hx29 := hx.common.x29_eq
  have hx19 := hx.x19_eq; have hx22 := hx.x22_eq; have hx25 := hx.x25_eq
  have hx26 := hx.x26_eq; have hx27 := hx.x27_eq; have hm16 := hx.m16_eq; have htag := hx.tag_352
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.common.frame
  rcases okmLen_cmp_lemmas hpre.okm_len with ⟨hokm_c, hokm_ule, hokm_ult⟩
  iterate 34 kdf_step
  refine RunsTo.refl ?_
  refine ⟨by kdf_reg,
    HCommon.of_agreesOutside_hsp (off := 0#64) (sz := 352) hx.common
      (by kdf_reg) (by kdf_reg) (by kdf_reg)
      (by
        repeat' rw [Expand.mem_setMem]
        repeat' (first
          | ((with_reducible refine agreesOutside_hsp_write64 ?_ ?hw); case hw => decide)
          | ((with_reducible refine agreesOutside_hsp_write64_zero ?_ ?hw); case hw => decide))
        exact AgreesOutside.rfl' _ _ _)
      (by decide),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by simp (config := { decide := true }) only [arm64_norm, hx26],
    by simp (config := { decide := true }) only [arm64_norm, hx27],
    by simp (config := { decide := true }) only [arm64_norm, hm16], ?_⟩
  simp only [Expand.mem_setMem]
  refine HmacSt.of_copy_empty_360_208 hx.hmac_360 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := { decide := true }) only [arm64_norm]))

/-- Segment `E3` (`b + 0x63410` → `b + 0x5e020`, 34 steps): checks `tag_352 = 0`, copies
`Hmac(PRK, [])` from `hsp s₀ + 360#64` to `hsp s₀ + 208#64`, stores `[sp + 0] = okmLen` and
`[sp + 8] = infoA`, checks `okmLen ≤ 8160`, and branches to `0x5e020`. -/
theorem seg_e3_runsTo [HkdfHooks C.F ext] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateERet2 b C.F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateExtractDone b C.F salt ikm info infoA okmA okmLen s₀) := by
  hkdf_seg_e3_body

theorem seg_e3_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    {b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hx : StateERet2 hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateExtractDone hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) := by
  hkdf_seg_e3_body

/-- Full Extract phase (`b + 0x63284` → `b + 0x634fc`) of `spqr::kdf::hkdf_to_slice`. -/
theorem extract_phase_runsTo [HkdfHooks C.F ext]
    (hNfs : Nfs3GenRunsToExt b C.F ext)
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀) :
    RunsTo (tripleRatchetProgAtExt b ext) s₀
      (StateExtractDone b C.F salt ikm info infoA okmA okmLen s₀) :=
  (seg_e0_runsTo (C := C) hpre).trans fun _ hs0 =>
  (nfs1_runsTo (alignedM := fun _ => (b &&& 0xfff#64) = 0#64) hNfs hpre hs0
    (fun _ => hpre.base_al)).trans fun _ hs1 =>
  (seg_e1_runsTo hpre hs1).trans fun _ hs2 =>
  (seg_e1d_runsTo hpre hs2).trans fun _ hs3 =>
  (fin_extract_runsTo hpre hs3).trans fun _ hs4 =>
  (seg_e2_runsTo hpre hs4).trans fun _ hs5 =>
  (nfs2_runsTo (alignedM := fun _ => (b &&& 0xfff#64) = 0#64) hNfs hpre hs5
    (fun _ => hpre.base_al)).trans fun _ hs6 =>
  seg_e3_runsTo hpre hs6

theorem extract_phase_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    (hNfs : Nfs3GenRunsToProg ((blkPC_379).rebase (blkPl_379).base H)
      nfs3PlacedFakeB (blkPl_402).base (LibsignalCodeLoaded lsmpl) C.F)
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀
      nfs3PlacedFakeB (LibsignalCodeLoaded lsmpl s₀.mem)) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s₀
      (StateExtractDone hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) :=
  (seg_e0_placed_runsTo hpre).trans fun _ hs0 =>
  (nfs1_runsTo hNfs hpre hs0 (fun hkf => CryptoVerification.LibsignalCodeLoaded.of_keepsFrozenNoAnon hpre.base_al hkf)).trans fun _ hs1 =>
  (seg_e1_placed_runsTo h_memcpy h_compress hpre hs1).trans fun _ hs2 =>
  (seg_e1d_placed_runsTo hpre hs2).trans fun _ hs3 =>
  (fin_extract_placed_runsTo h_memcpy h_memset h_compress hpre hs3).trans fun _ hs4 =>
  (seg_e2_placed_runsTo hpre hs4).trans fun _ hs5 =>
  (nfs2_runsTo hNfs hpre hs5 (fun hkf => CryptoVerification.LibsignalCodeLoaded.of_keepsFrozenNoAnon hpre.base_al hkf)).trans fun _ hs6 =>
  seg_e3_placed_runsTo hpre hs6

/-! ## Expand Phase Common Invariant & Block 1 (`0x634fc → 0x636f0`) -/

/-- Common state invariant across the Expand phase (`0x63588 .. 0x63990`) of `hkdf_to_slice`:
- `HCommon okmLen s₀ s`
- `[sp + 0] = okmLen`, `[sp + 8] = infoA`, `[sp + 16] = info.length`, `[sp + 24] = hsp s₀ + 508#64`
- `Hmac(PRK, [])` template preserved at `hsp s₀ + 208#64`. -/
structure HExpCommon (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  common   : HCommon okmLen s₀ s
  m0_eq    : s.mem.read64 (hsp s₀ + 0#64) = BitVec.ofNat 64 okmLen
  m8_eq    : s.mem.read64 (hsp s₀ + 8#64) = infoA
  m16_eq   : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  m24_eq   : s.mem.read64 (hsp s₀ + 24#64) = hsp s₀ + 508#64
  hmac_208 : HmacSt s.mem (hsp s₀ + 208#64) F prk []

theorem HExpCommon.of_agreesOutside_32_208 {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoA : BitVec 64} {okmLen : ℕ}
    {s₀ s s' : State} {off : BitVec 64} {sz : ℕ}
    (hc : HExpCommon F prk info infoA okmLen s₀ s)
    (hstat : s'.status = .Running)
    (hsp_eq : s'.sp = hsp s₀)
    (hx29 : s'.readReg64 .x29 = hsp s₀ + 592#64)
    (hA : AgreesOutside s.mem s'.mem (hsp s₀ + off) sz)
    (hoff : decide (32 ≤ off.toNat ∧ 0 < sz ∧ off.toNat + sz ≤ 208) = true) :
    HExpCommon F prk info infoA okmLen s₀ s' := by
  have ⟨h1, h2, h3⟩ := of_decide_eq_true hoff
  refine
    { common := HCommon.of_agreesOutside_hsp hc.common hstat hsp_eq hx29 hA
        (decide_eq_true (by omega))
      m0_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m0_eq
      m8_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m8_eq
      m16_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m16_eq
      m24_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m24_eq
      hmac_208 := HmacSt.of_agreesOutside hc.hmac_208 hA (by unfold DisjointRegions; bv_omega) }

theorem HExpCommon.of_agreesOutside_352_592 {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoA : BitVec 64} {okmLen : ℕ}
    {s₀ s s' : State} {off : BitVec 64} {sz : ℕ}
    (hc : HExpCommon F prk info infoA okmLen s₀ s)
    (hstat : s'.status = .Running)
    (hsp_eq : s'.sp = hsp s₀)
    (hx29 : s'.readReg64 .x29 = hsp s₀ + 592#64)
    (hA : AgreesOutside s.mem s'.mem (hsp s₀ + off) sz)
    (hoff : decide (352 ≤ off.toNat ∧ 0 < sz ∧ off.toNat + sz ≤ 592) = true) :
    HExpCommon F prk info infoA okmLen s₀ s' := by
  have ⟨h1, h2, h3⟩ := of_decide_eq_true hoff
  refine
    { common := HCommon.of_agreesOutside_hsp hc.common hstat hsp_eq hx29 hA
        (decide_eq_true (by omega))
      m0_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m0_eq
      m8_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m8_eq
      m16_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m16_eq
      m24_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m24_eq
      hmac_208 := HmacSt.of_agreesOutside hc.hmac_208 hA (by unfold DisjointRegions; bv_omega) }

theorem HExpCommon.of_fin_frame {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoA : BitVec 64} {okmLen : ℕ}
    {s₀ s s' : State}
    (hc : HExpCommon F prk info infoA okmLen s₀ s)
    (hstat : s'.status = .Running)
    (hcs : CalleeSaved s s')
    (hfr : Frame s.mem s'.mem [(hsp s₀ + 540#64, 32), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 144#64, 144)]) :
    HExpCommon F prk info infoA okmLen s₀ s' := by
  have hd_low : ∀ r ∈ [(hsp s₀ + 540#64, (32 : ℕ)), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 144#64, 144)],
      DisjointRegions r.1 r.2 (hsp s₀) 32 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  have hd_208 : ∀ r ∈ [(hsp s₀ + 540#64, (32 : ℕ)), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 144#64, 144)],
      DisjointRegions r.1 r.2 (hsp s₀ + 208#64) 0x90 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  rcases hc.hmac_208 with ⟨hlen, _, hpos, hin, hcnt1, hout, hcnt2⟩
  have hhm' : HmacSt s'.mem (hsp s₀ + 208#64) F prk [] := by
    refine ⟨hlen, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · refine (hfr.1 _ fun r hr => ?_).trans hpos
      exact (hd_208 r hr).outside (by unfold InRegion; bv_omega) (by decide)
    · refine (Expand.Frame.readBytes_eq hfr (fun r hr => ?_) (by decide)).trans hin
      exact (hd_208 r hr).sub_right _ ⟨by decide, by bv_omega⟩
    · refine (Expand.Frame.read64_eq hfr fun r hr => ?_).trans hcnt1
      exact (hd_208 r hr).sub_right _ ⟨by decide, by bv_omega⟩
    · refine (Expand.Frame.readBytes_eq hfr (fun r hr => ?_) (by decide)).trans hout
      exact (hd_208 r hr).sub_right _ ⟨by decide, by bv_omega⟩
    · refine (Expand.Frame.read64_eq hfr fun r hr => ?_).trans hcnt2
      exact (hd_208 r hr).sub_right _ ⟨by decide, by bv_omega⟩
  exact
    { common := HCommon.of_fin_frame (outOff := 540#64) hc.common hstat hcs hfr (by decide)
      m0_eq := (Expand.Frame.read64_eq hfr fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 0#64) ⟨by decide, by bv_omega⟩).trans hc.m0_eq
      m8_eq := (Expand.Frame.read64_eq hfr fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 8#64) ⟨by decide, by bv_omega⟩).trans hc.m8_eq
      m16_eq := (Expand.Frame.read64_eq hfr fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 16#64) ⟨by decide, by bv_omega⟩).trans hc.m16_eq
      m24_eq := (Expand.Frame.read64_eq hfr fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 24#64) ⟨by decide, by bv_omega⟩).trans hc.m24_eq
      hmac_208 := hhm' }

theorem HExpCommon.of_agreesOutside_okm {b b_iv : BitVec 64} {aligned : Prop}
    {F : ShaState → List (BitVec 8) → ShaState}
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s s' : State} {off : BitVec 64} {sz : ℕ}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hc : HExpCommon F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s)
    (hstat : s'.status = .Running)
    (hsp_eq : s'.sp = hsp s₀)
    (hx29 : s'.readReg64 .x29 = hsp s₀ + 592#64)
    (hA : AgreesOutside s.mem s'.mem (okmA + off) sz)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ okmLen) :
    HExpCommon F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s' := by
  have hd_stk : DisjointRegions (okmA + off) sz (hsp s₀) 592 := by
    have hd1 := hpre.disj_okm_stk.sub_left (okmA + off)
      ⟨hoff.1, by have := hoff.2; have := hpre.okm_len; bv_omega⟩
    exact hd1.sub_right (hsp s₀) ⟨by decide, by bv_omega⟩
  refine
    { common := HCommon.of_agreesOutside_okm hpre hc.common hstat hsp_eq hx29 hA hoff
      m0_eq := (hA.read64_eq (hd_stk.sub_right (hsp s₀ + 0#64) ⟨by decide, by bv_omega⟩)).trans hc.m0_eq
      m8_eq := (hA.read64_eq (hd_stk.sub_right (hsp s₀ + 8#64) ⟨by decide, by bv_omega⟩)).trans hc.m8_eq
      m16_eq := (hA.read64_eq (hd_stk.sub_right (hsp s₀ + 16#64) ⟨by decide, by bv_omega⟩)).trans hc.m16_eq
      m24_eq := (hA.read64_eq (hd_stk.sub_right (hsp s₀ + 24#64) ⟨by decide, by bv_omega⟩)).trans hc.m24_eq
      hmac_208 := HmacSt.of_agreesOutside hc.hmac_208 hA
        (hd_stk.sub_right (hsp s₀ + 208#64) ⟨by decide, by bv_omega⟩) }

theorem okmLen_ge32_lemmas {okmLen : ℕ}
    (hokm : okmLen = 32 ∨ okmLen = 64 ∨ okmLen = 96) :
    (AddWithCarry64 (BitVec.ofNat 64 okmLen) 18446744073709551583#64 true).2.c = true ∧
    BitVec.ule 32#64 (BitVec.ofNat 64 okmLen) = true ∧
    BitVec.ult (BitVec.ofNat 64 okmLen) 32#64 = false := by
  rcases hokm with rfl | rfl | rfl <;> decide

theorem HmacSt.of_copy_empty_208_208 {m₀ m : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key : List (BitVec 8)}
    (hsrc : HmacSt m₀ (hsp s₀ + 208#64) F key [])
    (h56  : m.read64 (hsp s₀ + 264#64) = m₀.read64 (hsp s₀ + 264#64))
    (h64  : m.read64 (hsp s₀ + 272#64) = m₀.read64 (hsp s₀ + 272#64))
    (h72  : m.read64 (hsp s₀ + 280#64) = m₀.read64 (hsp s₀ + 280#64))
    (h80  : m.read64 (hsp s₀ + 288#64) = m₀.read64 (hsp s₀ + 288#64))
    (h88  : m.read64 (hsp s₀ + 296#64) = m₀.read64 (hsp s₀ + 296#64))
    (h96  : m.read64 (hsp s₀ + 304#64) = m₀.read64 (hsp s₀ + 304#64))
    (h104 : m.read64 (hsp s₀ + 312#64) = m₀.read64 (hsp s₀ + 312#64))
    (h112 : m.read64 (hsp s₀ + 320#64) = m₀.read64 (hsp s₀ + 320#64))
    (h120 : m.read64 (hsp s₀ + 328#64) = m₀.read64 (hsp s₀ + 328#64))
    (h128 : m.read64 (hsp s₀ + 336#64) = m₀.read64 (hsp s₀ + 336#64))
    (h136 : m.read64 (hsp s₀ + 344#64) = m₀.read64 (hsp s₀ + 344#64)) :
    HmacSt m (hsp s₀ + 208#64) F key [] :=
  HmacSt.of_copy_empty hsrc
    (Expand.read64_add_off h56) (Expand.read64_add_off h64) (Expand.read64_add_off h72)
    (Expand.read64_add_off h80) (Expand.read64_add_off h88) (Expand.read64_add_off h96)
    (Expand.read64_add_off h104) (Expand.read64_add_off h112) (Expand.read64_add_off h120)
    (Expand.read64_add_off h128) (Expand.read64_add_off h136)

theorem HmacSt.of_copy_empty_208_352 {m₀ m : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key : List (BitVec 8)}
    (hsrc : HmacSt m₀ (hsp s₀ + 208#64) F key [])
    (h56  : m.read64 (hsp s₀ + 408#64) = m₀.read64 (hsp s₀ + 264#64))
    (h64  : m.read64 (hsp s₀ + 416#64) = m₀.read64 (hsp s₀ + 272#64))
    (h72  : m.read64 (hsp s₀ + 424#64) = m₀.read64 (hsp s₀ + 280#64))
    (h80  : m.read64 (hsp s₀ + 432#64) = m₀.read64 (hsp s₀ + 288#64))
    (h88  : m.read64 (hsp s₀ + 440#64) = m₀.read64 (hsp s₀ + 296#64))
    (h96  : m.read64 (hsp s₀ + 448#64) = m₀.read64 (hsp s₀ + 304#64))
    (h104 : m.read64 (hsp s₀ + 456#64) = m₀.read64 (hsp s₀ + 312#64))
    (h112 : m.read64 (hsp s₀ + 464#64) = m₀.read64 (hsp s₀ + 320#64))
    (h120 : m.read64 (hsp s₀ + 472#64) = m₀.read64 (hsp s₀ + 328#64))
    (h128 : m.read64 (hsp s₀ + 480#64) = m₀.read64 (hsp s₀ + 336#64))
    (h136 : m.read64 (hsp s₀ + 488#64) = m₀.read64 (hsp s₀ + 344#64)) :
    HmacSt m (hsp s₀ + 352#64) F key [] :=
  HmacSt.of_copy_empty hsrc
    (Expand.read64_add_off h56) (Expand.read64_add_off h64) (Expand.read64_add_off h72)
    (Expand.read64_add_off h80) (Expand.read64_add_off h88) (Expand.read64_add_off h96)
    (Expand.read64_add_off h104) (Expand.read64_add_off h112) (Expand.read64_add_off h120)
    (Expand.read64_add_off h128) (Expand.read64_add_off h136)

structure StateB1Memcpy (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) (pc_target : BitVec 64 := b + bv% (ls_off% "memcpy")) : Prop where
  pc_eq    : s.pc = pc_target
  exp      : HExpCommon F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  lr_eq    : s.readReg64 .lr = b + 0x5e194#64
  x0_eq    : s.readReg64 .x0 = hsp s₀ + 352#64
  x1_eq    : s.readReg64 .x1 = infoA
  x2_eq    : s.readReg64 .x2 = BitVec.ofNat 64 info.length
  x20_eq   : s.readReg64 .x20 = 0#64
  x21_eq   : s.readReg64 .x21 = BitVec.ofNat 64 okmLen
  x22_eq   : s.readReg64 .x22 = okmA
  x24_eq   : s.readReg64 .x24 = 32#64
  x25_eq   : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x28_eq   : s.readReg64 .x28 = hsp s₀ + 352#64
  hmac_352 : HmacSt s.mem (hsp s₀ + 352#64) F (hkdfExtractBytes F salt ikm) []

set_option hygiene false in
local macro "hkdf_seg_b1a_body" : tactic => `(tactic| (
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp_eq := hx.common.sp_eq; have hx29 := hx.common.x29_eq
  have hx19 := hx.x19_eq; have hx22 := hx.x22_eq; have hx25 := hx.x25_eq
  have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  have hm0 : s.mem.read64 (hsp s₀) = BitVec.ofNat 64 okmLen := by
    simpa [BitVec.add_zero] using hx.m0_eq
  have hm8 := hx.m8_eq; have hm16 := hx.m16_eq
  have hpos_208 : s.mem.read8 (hsp s₀ + 271#64) = 0#8 := by
    simpa [BitVec.add_assoc] using hx.hmac_208.2.2.1
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.common.frame
  rcases okmLen_ge32_lemmas hpre.okm_len with ⟨hokm_c, hokm_ule, hokm_ult⟩
  rcases Expand.cmp_lt64_lemmas (by have := hpre.info_lt; omega : info.length < 64) with
    ⟨h_info_ule, h_info_ult, h_info_cmp⟩
  iterate 36 kdf_step
  refine RunsTo.refl ?_
  refine ⟨by kdf_reg,
    { common := HCommon.of_agreesOutside_hsp (off := 24#64) (sz := 472) hx.common
        (by kdf_reg) (by kdf_reg) (by kdf_reg) (by prove_agrees_hsp) (by decide)
      m0_eq := by simpa [BitVec.add_zero] using (by simp (config := { decide := true }) only [arm64_norm, hm0] : _ = BitVec.ofNat 64 okmLen)
      m8_eq := by simp (config := { decide := true }) only [arm64_norm, hm8]
      m16_eq := by simp (config := { decide := true }) only [arm64_norm, hm16]
      m24_eq := by simp (config := { decide := true }) only [arm64_norm]
      hmac_208 := by
        simp only [Expand.mem_setMem]
        refine HmacSt.of_copy_empty_208_208 hx.hmac_208 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
          simp (config := { decide := true }) only [arm64_norm] },
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, ?_⟩
  simp only [Expand.mem_setMem]
  refine HmacSt.of_copy_empty_208_352 hx.hmac_208 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := { decide := true }) only [arm64_norm]))

/-- Segment `B1a` (`b + 0x5e020` → `b + 0x97228`, 36 steps): copies `Hmac(PRK, [])` from
`hsp s₀ + 208#64` to `hsp s₀ + 352#64`, stores `hsp s₀ + 508#64` at `[sp + 24]`, sets `x24 = 32`,
and calls `memcpy(hsp s₀ + 352#64, infoA, info.length)`. -/
theorem seg_b1a_runsTo [HkdfHooks C.F ext] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateExtractDone b C.F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateB1Memcpy b C.F salt ikm info infoA okmA okmLen s₀) := by
  hkdf_seg_b1a_body

theorem seg_b1a_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    {b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hx : StateExtractDone hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateB1Memcpy hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ · (lsρ lsMemcpySym)) := by
  hkdf_seg_b1a_body

theorem HmacSt.of_copy_352_32 {m₀ m : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key pmsg : List (BitVec 8)}
    (hsrc : HmacSt m₀ (hsp s₀ + 352#64) F key pmsg)
    (h0   : m.read64 (hsp s₀ + 32#64)  = m₀.read64 (hsp s₀ + 352#64))
    (h8   : m.read64 (hsp s₀ + 40#64)  = m₀.read64 (hsp s₀ + 360#64))
    (h16  : m.read64 (hsp s₀ + 48#64)  = m₀.read64 (hsp s₀ + 368#64))
    (h24  : m.read64 (hsp s₀ + 56#64)  = m₀.read64 (hsp s₀ + 376#64))
    (h32  : m.read64 (hsp s₀ + 64#64)  = m₀.read64 (hsp s₀ + 384#64))
    (h40  : m.read64 (hsp s₀ + 72#64)  = m₀.read64 (hsp s₀ + 392#64))
    (h48  : m.read64 (hsp s₀ + 80#64)  = m₀.read64 (hsp s₀ + 400#64))
    (h56  : m.read64 (hsp s₀ + 88#64)  = m₀.read64 (hsp s₀ + 408#64))
    (h64  : m.read64 (hsp s₀ + 96#64)  = m₀.read64 (hsp s₀ + 416#64))
    (h72  : m.read64 (hsp s₀ + 104#64) = m₀.read64 (hsp s₀ + 424#64))
    (h80  : m.read64 (hsp s₀ + 112#64) = m₀.read64 (hsp s₀ + 432#64))
    (h88  : m.read64 (hsp s₀ + 120#64) = m₀.read64 (hsp s₀ + 440#64))
    (h96  : m.read64 (hsp s₀ + 128#64) = m₀.read64 (hsp s₀ + 448#64))
    (h104 : m.read64 (hsp s₀ + 136#64) = m₀.read64 (hsp s₀ + 456#64))
    (h112 : m.read64 (hsp s₀ + 144#64) = m₀.read64 (hsp s₀ + 464#64))
    (h120 : m.read64 (hsp s₀ + 152#64) = m₀.read64 (hsp s₀ + 472#64))
    (h128 : m.read64 (hsp s₀ + 160#64) = m₀.read64 (hsp s₀ + 480#64))
    (h136 : m.read64 (hsp s₀ + 168#64) = m₀.read64 (hsp s₀ + 488#64)) :
    HmacSt m (hsp s₀ + 32#64) F key pmsg :=
  HmacSt.of_copy_19 hsrc h0
    (Expand.read64_add_off h8) (Expand.read64_add_off h16) (Expand.read64_add_off h24)
    (Expand.read64_add_off h32) (Expand.read64_add_off h40) (Expand.read64_add_off h48)
    (Expand.read64_add_off h56) (Expand.read64_add_off h64) (Expand.read64_add_off h72)
    (Expand.read64_add_off h80) (Expand.read64_add_off h88) (Expand.read64_add_off h96)
    (Expand.read64_add_off h104) (Expand.read64_add_off h112) (Expand.read64_add_off h120)
    (Expand.read64_add_off h128) (Expand.read64_add_off h136)

theorem HmacSt.of_memcpy_counter_352 {m₀ : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key info : List (BitVec 8)}
    {b1 c : BitVec 8}
    (h₀ : HmacSt m₀ (hsp s₀ + 352#64) F key [])
    (hinfo : info.length < 55) :
    let m₁ := m₀.writeBytes (hsp s₀ + 352#64) info
    let m₂ := (((m₁.write8 (hsp s₀ + 415#64) b1).write8 (hsp s₀ + 32#64) c).write8
      (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) c).write8
      (hsp s₀ + 415#64) (BitVec.ofNat 8 (info.length + 1))
    HmacSt m₂ (hsp s₀ + 352#64) F key (info ++ [c]) := by
  intro m₁ m₂
  rcases h₀ with ⟨_, _, _, hin, hcnt1, hout, hcnt2⟩
  have hlen : (info ++ [c]).length = info.length + 1 := by simp
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen, Bytes.readBytes_add m₂ (hsp s₀ + 352#64) info.length 1]
    have h_info : m₂.readBytes (hsp s₀ + 352#64) info.length = info := by
      by_cases hi0 : info.length = 0
      · have hnil : info = [] := List.eq_nil_of_length_eq_zero hi0
        subst hnil; rfl
      · dsimp only [m₂, m₁]
        rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
              (by unfold DisjointRegions; bv_omega) (by omega),
            (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) 1 |>.write8 (by simp [InRegion])).readBytes_eq
              (by unfold DisjointRegions; bv_omega) (by omega),
            (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
              (by unfold DisjointRegions; bv_omega) (by omega),
            (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
              (by unfold DisjointRegions; bv_omega) (by omega)]
        exact Bytes.readBytes_writeBytes_same m₀ _ info (by omega)
    have h_c : m₂.readBytes (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) 1 = [c] := by
      dsimp only [Memory.readBytes, m₂]
      rw [Memory.read8_write8_ne (by bv_omega), Memory.read8_write8_same]
    rw [h_info, h_c]
  · rw [hlen, show hsp s₀ + 352#64 + 0x3f#64 = hsp s₀ + 415#64 by bv_omega]
    dsimp only [m₂]
    exact Memory.read8_write8_same _ _ _
  · have h_ag : m₂.readBytes (hsp s₀ + 352#64 + 0x40#64) 32 = m₀.readBytes (hsp s₀ + 352#64 + 0x40#64) 32 := by
      dsimp only [m₂, m₁]
      rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          Expand.writeBytes_readBytes_disj m₀ _ info (hsp s₀ + 352#64 + 0x40#64) 32
            (fun _ _ => by unfold DisjointRegions; bv_omega) (by decide)]
    exact h_ag.trans hin
  · dsimp only [m₂, m₁]
    rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        Expand.writeBytes_read64_disj m₀ _ info (hsp s₀ + 352#64 + 0x60#64)
          (fun _ => by unfold DisjointRegions; bv_omega),
        hcnt1]
  · have h_ag_out : m₂.readBytes (hsp s₀ + 352#64 + 0x68#64) 32 = m₀.readBytes (hsp s₀ + 352#64 + 0x68#64) 32 := by
      dsimp only [m₂, m₁]
      rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          Expand.writeBytes_readBytes_disj m₀ _ info (hsp s₀ + 352#64 + 0x68#64) 32
            (fun _ _ => by unfold DisjointRegions; bv_omega) (by decide)]
    exact h_ag_out.trans hout
  · dsimp only [m₂, m₁]
    rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        Expand.writeBytes_read64_disj m₀ _ info (hsp s₀ + 352#64 + 0x88#64)
          (fun _ => by unfold DisjointRegions; bv_omega),
        hcnt2]

theorem canWrite_hsp_352_add {m : Memory} {s₀ : State} {k : ℕ}
    (hrw : m.RW (hsp s₀) 688) (hk : k < 64) :
    m.canWrite (hsp s₀ + (352#64 + BitVec.ofNat 64 k)) 1 = true ∧
    m.canWrite (hsp s₀ + 352#64 + BitVec.ofNat 64 k) 1 = true := by
  have h1 : m.canWrite (hsp s₀ + (352#64 + BitVec.ofNat 64 k)) 1 = true :=
    hrw.canWrite_sub (by bv_omega) (by decide)
  refine ⟨h1, ?_⟩
  rw [BitVec.add_assoc]; exact h1

structure StateB1Fin (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) (pc_target : BitVec 64 := b + 0x67a58#64) : Prop where
  pc_eq    : s.pc = pc_target
  exp      : HExpCommon F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  lr_eq    : s.readReg64 .lr = b + 0x5e2d4#64
  x0_eq    : s.readReg64 .x0 = hsp s₀ + 540#64
  x1_eq    : s.readReg64 .x1 = hsp s₀ + 32#64
  x21_eq   : s.readReg64 .x21 = BitVec.ofNat 64 okmLen
  x22_eq   : s.readReg64 .x22 = okmA
  x24_eq   : s.readReg64 .x24 = 32#64
  x25_eq   : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32)
  x28_eq   : s.readReg64 .x28 = hsp s₀ + 352#64
  hmac_32  : HmacSt s.mem (hsp s₀ + 32#64) F (hkdfExtractBytes F salt ikm) (info ++ [1#8])

structure StateB1RetFin (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + 0x5e2d4#64
  exp      : HExpCommon F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  x21_eq   : s.readReg64 .x21 = BitVec.ofNat 64 okmLen
  x22_eq   : s.readReg64 .x22 = okmA
  x24_eq   : s.readReg64 .x24 = 32#64
  x25_eq   : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32)
  x28_eq   : s.readReg64 .x28 = hsp s₀ + 352#64
  t1_540   : s.mem.readBytes (hsp s₀ + 540#64) 32 = Expand.t1 F (hkdfExtractBytes F salt ikm) info

structure StateB1Done (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + 0x5e2f8#64
  exp      : HExpCommon F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  x21_eq   : s.readReg64 .x21 = BitVec.ofNat 64 okmLen
  x22_eq   : s.readReg64 .x22 = okmA
  x24_eq   : s.readReg64 .x24 = 32#64
  x25_eq   : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32)
  x28_eq   : s.readReg64 .x28 = hsp s₀ + 352#64
  t1_508   : s.mem.readBytes (hsp s₀ + 508#64) 32 = Expand.t1 F (hkdfExtractBytes F salt ikm) info
  okm_32   : s.mem.readBytes okmA 32 = Expand.t1 F (hkdfExtractBytes F salt ikm) info

theorem hmac_208_write64 {m : Memory} {s₀ : State} {off v : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key : List (BitVec 8)}
    (h : HmacSt m (hsp s₀ + 208#64) F key [])
    (hw : decide (off.toNat + 8 ≤ 208 ∨ (352 ≤ off.toNat ∧ off.toNat + 8 ≤ 688)) = true) :
    HmacSt (m.write64 (hsp s₀ + off) v) (hsp s₀ + 208#64) F key [] := by
  have hw' := of_decide_eq_true hw
  exact HmacSt.of_agreesOutside h
    (AgreesOutside.rfl' m (hsp s₀ + off) 8 |>.write64 (by bv_omega) (by decide))
    (by unfold DisjointRegions; bv_omega)

theorem hmac_208_write8 {m : Memory} {s₀ : State} {a : BitVec 64} {v : BitVec 8}
    {F : ShaState → List (BitVec 8) → ShaState} {key : List (BitVec 8)}
    (h : HmacSt m (hsp s₀ + 208#64) F key [])
    (hw : DisjointRegions a 1 (hsp s₀ + 208#64) 0x90) :
    HmacSt (m.write8 a v) (hsp s₀ + 208#64) F key [] :=
  HmacSt.of_agreesOutside h
    (AgreesOutside.rfl' m a 1 |>.write8 (by simp [InRegion])) hw

macro "prove_hmac_208" hbase:term : tactic =>
  `(tactic| (
    repeat' rw [Expand.mem_setMem]
    repeat' (first
      | ((with_reducible refine hmac_208_write64 ?_ ?hw); case hw => decide)
      | ((with_reducible refine hmac_208_write8 ?_ ?hw); case hw => (unfold DisjointRegions; bv_omega)))
    exact $hbase))

theorem HExpCommon.of_agreesOutside_32_560 {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoA : BitVec 64} {okmLen : ℕ}
    {s₀ s s' : State} {off : BitVec 64} {sz : ℕ}
    (hc : HExpCommon F prk info infoA okmLen s₀ s)
    (hstat : s'.status = .Running)
    (hsp_eq : s'.sp = hsp s₀)
    (hx29 : s'.readReg64 .x29 = hsp s₀ + 592#64)
    (hA : AgreesOutside s.mem s'.mem (hsp s₀ + off) sz)
    (hoff : decide (32 ≤ off.toNat ∧ 0 < sz ∧ off.toNat + sz ≤ 592) = true)
    (hhm : HmacSt s'.mem (hsp s₀ + 208#64) F prk []) :
    HExpCommon F prk info infoA okmLen s₀ s' := by
  have ⟨h1, h2, h3⟩ := of_decide_eq_true hoff
  refine
    { common := HCommon.of_agreesOutside_hsp hc.common hstat hsp_eq hx29 hA
        (decide_eq_true (by omega))
      m0_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m0_eq
      m8_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m8_eq
      m16_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m16_eq
      m24_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m24_eq
      hmac_208 := hhm }

set_option hygiene false in
local macro "hkdf_seg_b1b_post" : tactic => `(tactic| (
  let m₁ := s.mem.writeBytes (hsp s₀ + 352#64) info
  have hA1 : AgreesOutside s.mem m₁ (hsp s₀ + 352#64) 55 :=
    Expand.agreesOutside_writeBytes_le s.mem (hsp s₀ + 352#64) info 55 (by omega)
  have hrw_wb : m₁.RW (hsp s₀) 688 := rw_of_perm_eq hA1.2 hrw_hsp
  rcases canWrite_hsp_352_add hrw_wb (by omega : info.length < 64) with ⟨hcw_pos1, hcw_pos2⟩
  dsimp only [m₁] at hrw_wb hcw_pos1 hcw_pos2
  have hze32 := zeroExtend64_truncate32_ofNat64 (by omega : info.length < 64)
  have hand255 := Expand.zeroExtend64_and255_truncate32_ofNat64 (by omega : info.length < 64)
  have hand64_255 := Expand.and64_255_ofNat64 (by omega : info.length < 64)
  have hand40 := Expand.and_0xffffffffff_ofNat64 (by omega : info.length < 64)
  rcases Expand.cmp32_lt63_lemmas (by omega : info.length < 63) with ⟨hcmp63_eq, hcmp63_ne, hcmp63_z⟩
  have hadd1 := Expand.zeroExtend64_add1_truncate32_ofNat64 (by omega : info.length < 63)
  iterate 26 kdf_step
  refine RunsTo.refl ?_
  have hc1 : HExpCommon C.F (hkdfExtractBytes C.F salt ikm) info infoA okmLen s₀ (s.setMem m₁) :=
    HExpCommon.of_agreesOutside_352_592 (off := 352#64) (sz := 55) hx.exp
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp_eq)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [Expand.mem_setMem]; exact hA1) (by decide)
  have hhm_m2 : HmacSt
      ((((m₁.write8 (hsp s₀ + 415#64) (BitVec.ofNat 8 info.length)).write8
        (hsp s₀ + 32#64) 1#8).write8
        (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) 1#8).write8
        (hsp s₀ + 415#64) (BitVec.ofNat 8 (info.length + 1)))
      (hsp s₀ + 352#64) C.F (hkdfExtractBytes C.F salt ikm) (info ++ [1#8]) :=
    HmacSt.of_memcpy_counter_352 hx.hmac_352 hinfo_lt
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
  simp only [Expand.mem_setMem]
  exact HmacSt.of_copy_352_32 hhm_m2
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
    (by simp (config := { decide := true }) only [m₁, arm64_norm])))

/-- Segment `B1b` (`b + 0x97228` → `b + 0x67974`, 1 `memcpy` + 26 steps): `memcpy` of `info` to
`hsp s₀ + 352#64`, appends counter byte `1#8`, sets `x26 = okmLen - 32`, copies `Hmac` to
`hsp s₀ + 32#64`, and calls `finalize_fixed(hsp s₀ + 540#64, hsp s₀ + 32#64)`. -/
theorem seg_b1b_runsTo [HkdfHooks C.F ext] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateB1Memcpy b C.F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateB1Fin b C.F salt ikm info infoA okmA okmLen s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status
  have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hlr := hx.lr_eq; have hx0 := hx.x0_eq; have hx1 := hx.x1_eq; have hx2 := hx.x2_eq
  have hx20 := hx.x20_eq; have hx21 := hx.x21_eq; have hx22 := hx.x22_eq
  have hx24 := hx.x24_eq; have hx25 := hx.x25_eq; have hx28 := hx.x28_eq
  have hhsp := hsp_aligned hpre.sp_aligned; have hinfo_lt := hpre.info_lt
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.exp.common.frame
  have hrw_dst : s.mem.RW (hsp s₀ + 352#64) info.length := hrw_hsp.sub (by bv_omega)
  have hread_info : s.mem.readBytes infoA info.length = info := HFrame.info_bytes hpre hx.exp.common.frame
  have hx2_nat : (s.readReg64 .x2).toNat = info.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine s2_memcpy_step_ext b C ext hrun hpc hx0 hx1 hx2_nat hlr hread_info hrw_dst ?_
  hkdf_seg_b1b_post

theorem seg_b1b_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    {b_iv : BitVec 64} {aligned : Prop} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
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
  refine s2_memcpy_step_placed_429 h_memcpy hrun hpc hx0 hx1 hx2_nat hlr hread_info hrw_dst ?_
  hkdf_seg_b1b_post

/-- `finalize_fixed` #1 (`b + 0x6ce50` → `b + 0x636cc`): computes `T(1) = Expand.t1 C.F prk info`
at `hsp s₀ + 540#64`. -/
theorem fin_b1_runsTo [HkdfHooks C.F ext] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateB1Fin b C.F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateB1RetFin b C.F salt ikm info infoA okmA okmLen s₀) := by
  have hrw_hsp := HFrame.rw_hsp hpre hx.exp.common.frame
  have hrw_sub := HFrame.rw_sub_544 hpre hx.exp.common.frame
  have hfin_pre : FinPre3 b C.F (hkdfExtractBytes C.F salt ikm) (info ++ [1#8]) s :=
    { pc_eq := hx.pc_eq, status := hx.exp.common.status,
      key_le := by simp [hkdfExtractBytes, hmacWith],
      msg_lt := by have := hpre.info_lt; simp; omega,
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_32,
      rw_out := by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega),
      rw_hm := by rw [hx.x1_eq]; exact hrw_hsp.sub (by bv_omega),
      rw_fsp := by rw [hx.exp.common.sp_eq]; exact hrw_sub.sub (by bv_omega),
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; unfold DisjointRegions; bv_omega,
      disj_out_fsp := by rw [hx.x0_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega,
      disj_hm_fsp := by rw [hx.x1_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega,
      sp_aligned := by rw [hx.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1 }
  refine (FinalizeFixed3Proof.finalize_fixed3_runsTo_ext (ext := ext) hfin_pre).mono
    fun s' ⟨hpc', hrun', hcs, ht1, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq] at ht1
  rw [hx.x0_eq, hx.x1_eq, hx.exp.common.sp_eq] at hfr
  exact ⟨hpc', HExpCommon.of_fin_frame hx.exp hrun' hcs hfr,
    (CalleeSaved.x21 hcs).trans hx.x21_eq, (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x24 hcs).trans hx.x24_eq, (CalleeSaved.x25 hcs).trans hx.x25_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq, (CalleeSaved.x28 hcs).trans hx.x28_eq, ht1⟩

theorem fin_b1_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {b_iv : BitVec 64} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv
      (LibsignalCodeLoaded lsmpl s₀.mem))
    (hx : StateB1Fin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ s (blkPl_425).base) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateB1RetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) := by
  have : HkdfPlacedHooks C.F H :=
    { memset := h_memset, memcpy := h_memcpy, compress256 := h_compress }
  have hrw_hsp := HFrame.rw_hsp hpre hx.exp.common.frame
  have hrw_sub := HFrame.rw_sub_544 hpre hx.exp.common.frame
  have hfin_pre : FinPre3 fin3PlacedFakeB C.F (hkdfExtractBytes C.F salt ikm) (info ++ [1#8]) s :=
    { pc_eq := by rw [fin3PlacedFakeB_off_0]; exact hx.pc_eq, status := hx.exp.common.status,
      key_le := by simp [hkdfExtractBytes, hmacWith],
      msg_lt := by have := hpre.info_lt; simp; omega,
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_32,
      rw_out := by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega),
      rw_hm := by rw [hx.x1_eq]; exact hrw_hsp.sub (by bv_omega),
      rw_fsp := by rw [hx.exp.common.sp_eq]; exact hrw_sub.sub (by bv_omega),
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; unfold DisjointRegions; bv_omega,
      disj_out_fsp := by rw [hx.x0_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega,
      disj_hm_fsp := by rw [hx.x1_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega,
      sp_aligned := by rw [hx.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1 }
  have hcl_s : LibsignalCodeLoaded lsmpl s.mem :=
    CryptoVerification.LibsignalCodeLoaded.of_keepsFrozenNoAnon hpre.base_al (HFrame.keepsFrozen hpre hx.exp.common.frame)
  refine (FinalizeFixed3Proof.finalize_fixed3_placed_runsTo_of_other_block
    hcl_s hfin_pre).mono fun s' ⟨hpc', hrun', hcs, ht1, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq] at ht1
  rw [hx.x0_eq, hx.x1_eq, hx.exp.common.sp_eq] at hfr
  exact ⟨hpc', HExpCommon.of_fin_frame hx.exp hrun' hcs hfr,
    (CalleeSaved.x21 hcs).trans hx.x21_eq, (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x24 hcs).trans hx.x24_eq, (CalleeSaved.x25 hcs).trans hx.x25_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq, (CalleeSaved.x28 hcs).trans hx.x28_eq, ht1⟩

theorem readBytes_32_hsp_508_of_540 {m₀ m : Memory} {s₀ : State} {bs : List (BitVec 8)}
    (hbs : m₀.readBytes (hsp s₀ + 540#64) 32 = bs)
    (h0  : m.read64 (hsp s₀ + 508#64) = m₀.read64 (hsp s₀ + 540#64))
    (h8  : m.read64 (hsp s₀ + 516#64) = m₀.read64 (hsp s₀ + 548#64))
    (h16 : m.read64 (hsp s₀ + 524#64) = m₀.read64 (hsp s₀ + 556#64))
    (h24 : m.read64 (hsp s₀ + 532#64) = m₀.read64 (hsp s₀ + 564#64)) :
    m.readBytes (hsp s₀ + 508#64) 32 = bs := by
  rw [readBytes_32_eq_of_read64_eq h0
    (Expand.read64_add_off h8) (Expand.read64_add_off h16) (Expand.read64_add_off h24), hbs]

set_option hygiene false in
local macro "hkdf_seg_b1d_post" : tactic => `(tactic| (
  let prk := hkdfExtractBytes C.F salt ikm
  let m₁ := s.mem.writeBytes okmA (Expand.t1 C.F prk info)
  have hA1 : AgreesOutside s.mem m₁ (okmA + 0#64) 32 := by
    rw [BitVec.add_zero]
    exact Expand.agreesOutside_writeBytes_le s.mem okmA (Expand.t1 C.F prk info) 32
      (by rw [Expand.t1_length])
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
  · simp only [Expand.mem_setMem]
    have ht1_m1 : m₁.readBytes (hsp s₀ + 540#64) 32 = Expand.t1 C.F prk info := by
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
    dsimp only [Expand.mem_setMem]
    refine (hA2.readBytes_eq hd (by decide)).trans ?_
    dsimp only [m₁, prk]
    conv_lhs => rw [← Expand.t1_length C.F (hkdfExtractBytes C.F salt ikm) info]
    exact Bytes.readBytes_writeBytes_same s.mem okmA
      (Expand.t1 C.F (hkdfExtractBytes C.F salt ikm) info)
      (by rw [Expand.t1_length]; decide)))

/-- Segment `B1d` (`b + 0x5e1f0` → `b + 0x5e214`, 4 steps + `memcpy` + 5 steps): copies `T(1)`
(32 B) from `hsp s₀ + 540#64` to `okmA` and caches `T(1)` at `hsp s₀ + 508#64`. -/
theorem seg_b1d_runsTo [HkdfHooks C.F ext] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateB1RetFin b C.F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateB1Done b C.F salt ikm info infoA okmA okmLen s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status
  have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hx21 := hx.x21_eq; have hx22 := hx.x22_eq; have hx24 := hx.x24_eq
  have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx28 := hx.x28_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_okm : s.mem.RW okmA okmLen := HFrame.rw_okm hpre hx.exp.common.frame
  have hrw_dst : s.mem.RW okmA 32 := hrw_okm.sub (by have := hpre.okm_len; bv_omega)
  iterate 4 kdf_step
  refine s2_memcpy_step_ext b C ext hrun rfl rfl rfl rfl rfl hx.t1_540 hrw_dst ?_
  hkdf_seg_b1d_post

theorem seg_b1d_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
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
  iterate 4 kdf_step
  refine s2_memcpy_step_placed_429 h_memcpy hrun rfl rfl rfl rfl rfl hx.t1_540 hrw_dst ?_
  hkdf_seg_b1d_post

/-- Full Extract + Expand Block 1 (`b + 0x63284` → `b + 0x636f0`) of `spqr::kdf::hkdf_to_slice`. -/
theorem block1_phase_runsTo [HkdfHooks C.F ext]
    (hNfs : Nfs3GenRunsToExt b C.F ext)
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀) :
    RunsTo (tripleRatchetProgAtExt b ext) s₀
      (StateB1Done b C.F salt ikm info infoA okmA okmLen s₀) :=
  (extract_phase_runsTo hNfs hpre).trans fun _ hs0 =>
  (seg_b1a_runsTo hpre hs0).trans fun _ hs1 =>
  (seg_b1b_runsTo hpre hs1).trans fun _ hs2 =>
  (fin_b1_runsTo hpre hs2).trans fun _ hs3 =>
  seg_b1d_runsTo hpre hs3

theorem block1_phase_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    (hNfs : Nfs3GenRunsToProg ((blkPC_379).rebase (blkPl_379).base H)
      nfs3PlacedFakeB (blkPl_402).base (LibsignalCodeLoaded lsmpl) C.F)
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀
      nfs3PlacedFakeB (LibsignalCodeLoaded lsmpl s₀.mem)) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s₀
      (StateB1Done hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) :=
  (extract_phase_placed_runsTo h_memcpy h_memset h_compress hNfs hpre).trans fun _ hs0 =>
  (seg_b1a_placed_runsTo hpre hs0).trans fun _ hs1 =>
  (seg_b1b_placed_runsTo h_memcpy hpre hs1).trans fun _ hs2 =>
  (fin_b1_placed_runsTo h_memcpy h_memset h_compress hpre hs2).trans fun _ hs3 =>
  seg_b1d_placed_runsTo h_memcpy hpre hs3

end CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof

