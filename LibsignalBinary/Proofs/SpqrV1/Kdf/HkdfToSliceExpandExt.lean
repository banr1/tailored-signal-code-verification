/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractDefsExt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HooksExt
import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
import LibsignalBinary.Proofs.SpqrV1.Chain.Defs -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.Repr -- shake: keep

/-!
# `spqr::kdf::hkdf_to_slice`: Contract-Backed Extract Completion and Expand Block 1

Completes the HKDF-Extract phase (`0x633cc → 0x634fc`) and proves HKDF-Expand Block 1, epilogue,
`okmLen = 32` exit, and loop entry under `HkdfStubsExt` and `S2FrameRO` at stack budget
`hkdfToSliceStackExt` (`17616` B).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf.HkdfToSliceExtProof

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame frame_of_agreesOutside)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.ChainProofs hiding hkdfToSliceName
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local simp, local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint
  extractLsb'_56_8_read64
  State.readReg64_setMem State.pc_setMem State.sp_setMem State.status_setMem
  Expand.mem_setMem
  extractLsb'_0_64_zero128 extractLsb'_64_64_zero128
  hsp_592_add_96_eq_sp
  read8_write64_264_271

@[local simp, local arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [(ls_off% hkdfToSliceName + 328) → (ls_off% hkdfToSliceName + 1808)]

theorem cs_x19 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x19 = s.readReg64 .x19 := h.2 .x19 (by simp)
theorem cs_x20 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x20 = s.readReg64 .x20 := h.2 .x20 (by simp)
theorem cs_x21 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x21 = s.readReg64 .x21 := h.2 .x21 (by simp)
theorem cs_x22 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x22 = s.readReg64 .x22 := h.2 .x22 (by simp)
theorem cs_x24 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x24 = s.readReg64 .x24 := h.2 .x24 (by simp)
theorem cs_x25 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x25 = s.readReg64 .x25 := h.2 .x25 (by simp)
theorem cs_x26 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x26 = s.readReg64 .x26 := h.2 .x26 (by simp)
theorem cs_x27 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x27 = s.readReg64 .x27 := h.2 .x27 (by simp)
theorem cs_x28 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x28 = s.readReg64 .x28 := h.2 .x28 (by simp)

theorem HCommonExt.of_nfs_frameRO_352 {b : BitVec 64} {saltRO ikmRO infoRO : Bool}
    {roRegs : List (BitVec 64 × ℕ)} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s s' : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hc : HCommonExt roRegs okmLen s₀ s) (hstat : s'.status = .Running)
    (hcs : CalleeSaved s s')
    (hfr : S2FrameRO roRegs s.mem s'.mem [(hsp s₀ + 352#64, 0x98), (hsp s₀ - 16928#64, 16928)]) :
    HCommonExt roRegs okmLen s₀ s' := by
  have hsaved' : HSaved s₀ s'.mem := by
    refine HSaved.of_s2FrameRO hc.saved (HFrameExt.rw_hsp hpre hc.frame) hfr fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  have hframe' : HFrameExt roRegs okmLen s₀ s'.mem := by
    refine S2FrameRO.trans hc.frame (S2FrameRO.mono hfr ?_); intro a ha r hr
    have hstack := ha (hsp s₀ - 16928#64, 17616) (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold OutsideRegion at *; bv_omega)
  exact ⟨hstat, hcs.1.trans hc.sp_eq, (cs_x29 hcs).trans hc.x29_eq, hsaved', hframe'⟩

/-! ## Extract-Completion Cut Predicates & Proofs (`hex:633cc → hex:634fc`) -/

structure StateEFinExt (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% finalizeFixed3Name)
  common  : HCommonExt roRegs okmLen s₀ s
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% hkdfToSliceName + 380)
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 507#64
  x1_eq   : s.readReg64 .x1 = hsp s₀ + 32#64
  x19_eq  : s.readReg64 .x19 = hsp s₀ + 208#64
  x22_eq  : s.readReg64 .x22 = okmA
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq  : s.readReg64 .x27 = infoA
  m16_eq  : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  hmac_32 : ∃ pfx tail, pfx ++ tail = ikm ∧ pfx.length % 64 = 0 ∧ tail.length < 64 ∧
              HmacStN s.mem (hsp s₀ + 32#64) F (effectiveHmacKey F salt) pfx tail

structure StateERetFinExt (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% hkdfToSliceName + 380)
  common  : HCommonExt roRegs okmLen s₀ s
  x19_eq  : s.readReg64 .x19 = hsp s₀ + 208#64
  x22_eq  : s.readReg64 .x22 = okmA
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq  : s.readReg64 .x27 = infoA
  m16_eq  : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  prk_507 : s.mem.readBytes (hsp s₀ + 507#64) 32 = hkdfExtractBytes F salt ikm

structure StateENfs2Ext (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% newFromSlice3Name)
  common  : HCommonExt roRegs okmLen s₀ s
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% hkdfToSliceName + 396)
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 352#64
  x1_eq   : s.readReg64 .x1 = hsp s₀ + 507#64
  x2_eq   : s.readReg64 .x2 = 32#64
  x19_eq  : s.readReg64 .x19 = hsp s₀ + 208#64
  x22_eq  : s.readReg64 .x22 = okmA
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq  : s.readReg64 .x27 = infoA
  m16_eq  : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  prk_507 : s.mem.readBytes (hsp s₀ + 507#64) 32 = hkdfExtractBytes F salt ikm

structure StateERet2Ext (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + bv% (ls_off% hkdfToSliceName + 396)
  common   : HCommonExt roRegs okmLen s₀ s
  x19_eq   : s.readReg64 .x19 = hsp s₀ + 208#64
  x22_eq   : s.readReg64 .x22 = okmA
  x25_eq   : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq   : s.readReg64 .x27 = infoA
  m16_eq   : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  tag_352  : s.mem.read64 (hsp s₀ + 352#64) = 0#64
  hmac_360 : HmacSt s.mem (hsp s₀ + 360#64) F (hkdfExtractBytes F salt ikm) []

structure StateExtractDoneExt (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + bv% (ls_off% hkdfToSliceName + 632)
  common   : HCommonExt roRegs okmLen s₀ s
  x19_eq   : s.readReg64 .x19 = hsp s₀ + 208#64
  x22_eq   : s.readReg64 .x22 = okmA
  x25_eq   : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq   : s.readReg64 .x27 = infoA
  m0_eq    : s.mem.read64 (hsp s₀ + 0#64) = BitVec.ofNat 64 okmLen
  m8_eq    : s.mem.read64 (hsp s₀ + 8#64) = infoA
  m16_eq   : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  hmac_208 : HmacSt s.mem (hsp s₀ + 208#64) F (hkdfExtractBytes F salt ikm) []

section ExtractCompletion

variable {img : Obj.Image} {b : BitVec 64} {F : ShaCompress} {ext : String → Option (State → State)}

/-- Segment `E1d` (`b + hex:633cc` → `b + hex:6ce50`, 13 steps): copies `Hmac` from `hsp s₀ + 208#64`
to `hsp s₀ + 32#64` and calls `finalize_fixed(hsp s₀ + 507#64, hsp s₀ + 32#64)`. -/
theorem seg_e1d_runsTo_ext {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateE3ccExt b roRegs F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateEFinExt b roRegs F salt ikm info infoA okmA okmLen s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.common.status
  have hsp_eq := hx.common.sp_eq; have hx29 := hx.common.x29_eq
  have hx19 := hx.x19_eq; have hx22 := hx.x22_eq
  have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  have hm16 := hx.m16_eq; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.common.frame
  iterate 13 kdf_step
  refine RunsTo.refl ?_
  refine ⟨by kdf_reg,
    HCommonExt.of_agreesOutside_hsp (off := 32#64) (sz := 0x90) hx.common
      (by kdf_reg) (by kdf_reg) (by kdf_reg) (by prove_agrees_hsp) (by decide),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by simp (config := { decide := true }) only [arm64_norm, hm16], ?_⟩
  rcases hx.hmac_208 with ⟨pfx, tail, hpt, hmod, hlt, hhm⟩
  refine ⟨pfx, tail, hpt, hmod, hlt, ?_⟩
  simp only [Expand.mem_setMem]
  refine HmacStN.of_copy_208_32 hhm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := { decide := true }) only [arm64_norm]

/-- `finalize_fixed` in Extract (`img.base + hex:6ce50` → `img.base + hex:63400`): produces
`PRK = hkdfExtractBytes F salt ikm` at `hsp s₀ + 507#64`. -/
theorem fin_extract_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateEFinExt img.base roRegs F salt ikm info infoA okmA okmLen s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateERetFinExt img.base roRegs F salt ikm info infoA okmA okmLen s₀) := by
  rcases hx.hmac_32 with ⟨pfx, tail, hpt, hmod, hlt, hhm⟩
  have hrw_hsp := HFrameExt.rw_hsp hpre hx.common.frame
  have hrw_sub := HFrameExt.rw_sub_16528 hpre hx.common.frame
  have hpfx_lt : pfx.length < 2 ^ 63 := by
    have : (pfx ++ tail).length = ikm.length := by rw [hpt]
    rw [List.length_append] at this; have := hpre.ikm_len; omega
  have hfin_pre : FinPre3GenExt img F salt pfx tail s :=
    { frz          := hfrz
      sym          := hsym
      pc_eq        := hx.pc_eq
      status       := hx.common.status
      pfx_lt       := hpfx_lt
      tail_lt      := hlt
      hmac_st      := by rw [hx.x1_eq]; exact hhm
      rw_out       := by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_hm        := by rw [hx.x1_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_fsp       := by rw [hx.common.sp_eq]; exact hrw_sub
      disj_out_hm  := by rw [hx.x0_eq, hx.x1_eq]; unfold DisjointRegions; bv_omega
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; unfold DisjointRegions; bv_omega
      disj_hm_fsp  := by rw [hx.x1_eq, hx.common.sp_eq]; unfold DisjointRegions; bv_omega
      sp_aligned   := by rw [hx.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1 }
  refine (hs.fin_ok hfin_pre).mono fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, hpt] at hout
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq] at hfr
  have hm16' : s'.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    refine (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => ?_).trans hx.m16_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  exact ⟨hpc',
    HCommonExt.of_fin_frame (outOff := 507#64) hpre hx.common hrun' hcs hfr (by decide),
    (cs_x19 hcs).trans hx.x19_eq, (cs_x22 hcs).trans hx.x22_eq,
    (cs_x25 hcs).trans hx.x25_eq, (cs_x26 hcs).trans hx.x26_eq,
    (cs_x27 hcs).trans hx.x27_eq, hm16', hout⟩

/-- Segment `E2` (`b + hex:63400` → `b + hex:66fa0`, 4 steps): sets up `new_from_slice` #2 with
`x0 = hsp s₀ + 352#64`, `x1 = hsp s₀ + 507#64`, `x2 = 32#64`. -/
theorem seg_e2_runsTo_ext {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    { infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hx : StateERetFinExt b roRegs F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateENfs2Ext b roRegs F salt ikm info infoA okmA okmLen s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.common.status
  have hsp_eq := hx.common.sp_eq; have hx29 := hx.common.x29_eq
  have hx19 := hx.x19_eq; have hx22 := hx.x22_eq
  have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  iterate 4 kdf_step
  refine RunsTo.refl ?_
  exact ⟨by kdf_reg,
    ⟨by kdf_reg, by kdf_reg, by kdf_reg, hx.common.saved, hx.common.frame⟩,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    hx.m16_eq, hx.prk_507⟩

/-- `new_from_slice` #2 (`img.base + hex:66fa0` → `img.base + hex:63410`): initializes
`Hmac(hkdfExtractBytes F salt ikm, [])` at `hsp s₀ + 360#64`. -/
theorem nfs2_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s : State}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateENfs2Ext img.base roRegs F salt ikm info infoA okmA okmLen s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateERet2Ext img.base roRegs F salt ikm info infoA okmA okmLen s₀) := by
  have hx2_nat : (s.readReg64 .x2).toNat = 32 := by rw [hx.x2_eq]; rfl
  have hrw_hsp := HFrameExt.rw_hsp hpre hx.common.frame
  have hnfs_pre : Nfs3GenPreExt img false roRegs s :=
    { frz          := hfrz
      sym          := hsym
      pc_eq        := hx.pc_eq
      status       := hx.common.status
      key_lt       := by rw [hx2_nat]; decide
      ro_iv_bytes  := HFrameExt.ro_iv_bytes hpre hx.common.frame
      base_al      := hpre.base_al
      ro_iv_read   := HFrameExt.ro_iv_read hpre hx.common.frame
      disj_iv_stk  := by
        rw [hx.common.sp_eq]
        exact hpre.disj_iv_stk.sub_right (hsp s₀ - 16928#64) ⟨by decide, by bv_omega⟩
      rw_out       := by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_stk       := by rw [hx.common.sp_eq]; exact HFrameExt.rw_sub_16928 hpre hx.common.frame
      disj_out_stk := by rw [hx.x0_eq, hx.common.sp_eq]; unfold DisjointRegions; bv_omega
      key_read     := by rw [hx.x1_eq, hx2_nat]; exact (hrw_hsp.sub (by bv_omega)).readable
      key_perm     := by
        simp only [Bool.false_eq_true, ↓reduceIte, hx.x1_eq, hx2_nat]
        exact hrw_hsp.sub (by bv_omega)
      out_key_stk  := by
        rw [hx.x1_eq, hx2_nat, hx.common.sp_eq]; intro a ha
        unfold InRegion OutsideRegion at *; bv_omega
      out_key_out  := by
        rw [hx.x1_eq, hx2_nat, hx.x0_eq]; intro a ha
        unfold InRegion OutsideRegion at *; bv_omega
      sp_aligned   := by rw [hx.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1 }
  refine (hs.nfs_ok hnfs_pre).mono fun s' ⟨hpc', hrun', hcs, htag, hhm, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq] at htag
  have hx0_8 : s.readReg64 .x0 + 8#64 = hsp s₀ + 360#64 := by rw [hx.x0_eq]; bv_lin
  have hprk_s : s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat =
      hkdfExtractBytes F salt ikm := by
    rw [hx.x1_eq, hx2_nat]; exact hx.prk_507
  rw [hx0_8, hprk_s, effectiveHmacKey_of_le F (by simp [hkdfExtractBytes, hmacWith])] at hhm
  rw [hx.x0_eq, hx.common.sp_eq] at hfr
  have hm16' : s'.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    refine (hfr.read64_eq_of_readable (hrw_hsp.sub (by bv_omega)).readable fun r hr => ?_).trans hx.m16_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  exact ⟨hpc',
    HCommonExt.of_nfs_frameRO_352 hpre hx.common hrun' hcs hfr,
    (cs_x19 hcs).trans hx.x19_eq, (cs_x22 hcs).trans hx.x22_eq,
    (cs_x25 hcs).trans hx.x25_eq, (cs_x26 hcs).trans hx.x26_eq,
    (cs_x27 hcs).trans hx.x27_eq, hm16', htag, hhm⟩

private theorem okmLen_cmp_lemmas_ext {okmLen : ℕ}
    (hokm : okmLen = 32 ∨ okmLen = 64 ∨ okmLen = 96) :
    (AddWithCarry64 (BitVec.ofNat 64 okmLen + bv% (2 ^ 64 - 8161)) 8159#64 true).2.c = true ∧
    BitVec.ule bv% (2 ^ 64 - 8160) (BitVec.ofNat 64 okmLen + bv% (2 ^ 64 - 8161)) = true ∧
    BitVec.ult (BitVec.ofNat 64 okmLen + bv% (2 ^ 64 - 8161)) bv% (2 ^ 64 - 8160) = false := by
  rcases hokm with rfl | rfl | rfl <;> decide

/-- Segment `E3` (`b + hex:63410` → `b + hex:634fc`, 34 steps): checks `tag_352 = 0`, copies
`Hmac(PRK, [])` from `hsp s₀ + 360#64` to `hsp s₀ + 208#64`, stores `[sp + 0] = okmLen` and
`[sp + 8] = infoA`, checks `okmLen ≤ 8160`, and branches to `hex:634fc`. -/
theorem seg_e3_runsTo_ext {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateERet2Ext b roRegs F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateExtractDoneExt b roRegs F salt ikm info infoA okmA okmLen s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.common.status
  have hsp_eq := hx.common.sp_eq; have hx29 := hx.common.x29_eq
  have hx19 := hx.x19_eq; have hx22 := hx.x22_eq
  have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  have hm16 := hx.m16_eq; have htag := hx.tag_352
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.common.frame
  rcases okmLen_cmp_lemmas_ext hpre.okm_len with ⟨hokm_c, hokm_ule, hokm_ult⟩
  iterate 34 kdf_step
  refine RunsTo.refl ?_
  refine ⟨by kdf_reg,
    HCommonExt.of_agreesOutside_hsp (off := 0#64) (sz := 352) hx.common
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
    by simp (config := { decide := true }) only [arm64_norm, hm16],
    ?_⟩
  simp only [Expand.mem_setMem]
  refine HmacSt.of_copy_empty_360_208 hx.hmac_360 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := { decide := true }) only [arm64_norm]

/-- Full Extract phase (`img.base + hex:63284` → `img.base + hex:634fc`) of `spqr::kdf::hkdf_to_slice`. -/
theorem extract_phase_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hfrz : img.FrozenLoaded s₀) (hsym : s₀.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s₀
      (StateExtractDoneExt img.base roRegs F salt ikm info infoA okmA okmLen s₀) :=
  RunsTo.trans_toE_inv hfrz hsym (seg_e0_runsTo_ext hpre) fun _ hf0 hs0 hx0 =>
  RunsToE.trans_inv hf0 hs0 (nfs1_runsTo_ext hs hf0 hs0 hpre hx0) fun _ hf1 hs1 hx1 =>
  RunsToE.trans_inv hf1 hs1 (seg_e1_runsTo_ext hs hf1 hs1 hpre hx1) fun _ hf2 hs2 hx2 =>
  RunsTo.trans_toE_inv hf2 hs2 (seg_e1d_runsTo_ext hpre hx2) fun _ hf3 hs3 hx3 =>
  RunsToE.trans_inv hf3 hs3 (fin_extract_runsTo_ext hs hf3 hs3 hpre hx3) fun _ hf4 hs4 hx4 =>
  RunsTo.trans_toE_inv hf4 hs4 (seg_e2_runsTo_ext hx4) fun _ hf5 hs5 hx5 =>
  RunsToE.trans_inv hf5 hs5 (nfs2_runsTo_ext hs hf5 hs5 hpre hx5) fun _ _ _ hx6 =>
  runsTo_toE (seg_e3_runsTo_ext hpre hx6)

end ExtractCompletion

/-! ## Expand Phase Common Invariant (`HExpCommonExt`) & Block 1 (`hex:634fc → hex:636f0`) -/

/-- Common state invariant across the Expand phase (`hex:63588 .. hex:63990`) of `hkdf_to_slice`. -/
structure HExpCommonExt (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  common   : HCommonExt roRegs okmLen s₀ s
  m0_eq    : s.mem.read64 (hsp s₀ + 0#64) = BitVec.ofNat 64 okmLen
  m8_eq    : s.mem.read64 (hsp s₀ + 8#64) = infoA
  m16_eq   : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  m24_eq   : s.mem.read64 (hsp s₀ + 24#64) = hsp s₀ + 508#64
  hmac_208 : HmacSt s.mem (hsp s₀ + 208#64) F prk []

theorem HExpCommonExt.of_agreesOutside_32_208 {roRegs : List (BitVec 64 × ℕ)}
    {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoA : BitVec 64} {okmLen : ℕ}
    {s₀ s s' : State} {off : BitVec 64} {sz : ℕ}
    (hc : HExpCommonExt roRegs F prk info infoA okmLen s₀ s)
    (hstat : s'.status = .Running) (hsp_eq : s'.sp = hsp s₀)
    (hx29 : s'.readReg64 .x29 = hsp s₀ + 592#64)
    (hA : AgreesOutside s.mem s'.mem (hsp s₀ + off) sz)
    (hoff : decide (32 ≤ off.toNat ∧ 0 < sz ∧ off.toNat + sz ≤ 208) = true) :
    HExpCommonExt roRegs F prk info infoA okmLen s₀ s' := by
  have ⟨h1, h2, h3⟩ := of_decide_eq_true hoff
  refine
    { common := HCommonExt.of_agreesOutside_hsp hc.common hstat hsp_eq hx29 hA (decide_eq_true (by omega))
      m0_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m0_eq
      m8_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m8_eq
      m16_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m16_eq
      m24_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m24_eq
      hmac_208 := HmacSt.of_agreesOutside hc.hmac_208 hA (by unfold DisjointRegions; bv_omega) }

theorem HExpCommonExt.of_agreesOutside_352_592 {roRegs : List (BitVec 64 × ℕ)}
    {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoA : BitVec 64} {okmLen : ℕ}
    {s₀ s s' : State} {off : BitVec 64} {sz : ℕ}
    (hc : HExpCommonExt roRegs F prk info infoA okmLen s₀ s)
    (hstat : s'.status = .Running) (hsp_eq : s'.sp = hsp s₀)
    (hx29 : s'.readReg64 .x29 = hsp s₀ + 592#64)
    (hA : AgreesOutside s.mem s'.mem (hsp s₀ + off) sz)
    (hoff : decide (352 ≤ off.toNat ∧ 0 < sz ∧ off.toNat + sz ≤ 592) = true) :
    HExpCommonExt roRegs F prk info infoA okmLen s₀ s' := by
  have ⟨h1, h2, h3⟩ := of_decide_eq_true hoff
  refine
    { common := HCommonExt.of_agreesOutside_hsp hc.common hstat hsp_eq hx29 hA (decide_eq_true (by omega))
      m0_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m0_eq
      m8_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m8_eq
      m16_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m16_eq
      m24_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m24_eq
      hmac_208 := HmacSt.of_agreesOutside hc.hmac_208 hA (by unfold DisjointRegions; bv_omega) }

theorem HExpCommonExt.of_agreesOutside_32_560 {roRegs : List (BitVec 64 × ℕ)}
    {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoA : BitVec 64} {okmLen : ℕ}
    {s₀ s s' : State} {off : BitVec 64} {sz : ℕ}
    (hc : HExpCommonExt roRegs F prk info infoA okmLen s₀ s)
    (hstat : s'.status = .Running) (hsp_eq : s'.sp = hsp s₀)
    (hx29 : s'.readReg64 .x29 = hsp s₀ + 592#64)
    (hA : AgreesOutside s.mem s'.mem (hsp s₀ + off) sz)
    (hoff : decide (32 ≤ off.toNat ∧ 0 < sz ∧ off.toNat + sz ≤ 592) = true)
    (hhm : HmacSt s'.mem (hsp s₀ + 208#64) F prk []) :
    HExpCommonExt roRegs F prk info infoA okmLen s₀ s' := by
  have ⟨h1, h2, h3⟩ := of_decide_eq_true hoff
  refine
    { common := HCommonExt.of_agreesOutside_hsp hc.common hstat hsp_eq hx29 hA (decide_eq_true (by omega))
      m0_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m0_eq
      m8_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m8_eq
      m16_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m16_eq
      m24_eq := (hA.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc.m24_eq
      hmac_208 := hhm }

theorem HmacSt.of_s2FrameRO_empty {roRegs : List (BitVec 64 × ℕ)}
    {F : ShaState → List (BitVec 8) → ShaState}
    {key : List (BitVec 8)} {m m' : Memory} {a : BitVec 64} {regs : List (BitVec 64 × ℕ)}
    (h : HmacSt m a F key []) (hrw : m.RW a 0x90) (hfr : S2FrameRO roRegs m m' regs)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 a 0x90) :
    HmacSt m' a F key [] := by
  rcases h with ⟨hlen, _, hpos, hin, hcnt1, hout, hcnt2⟩
  refine ⟨hlen, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have hpos_rd := hrw.readable (a + 0x3f#64) (by simp only [InRegion]; bv_omega)
    refine (hfr.1 _ hpos_rd.1 hpos_rd.2 fun r hr => ?_).trans hpos
    exact (hd r hr).outside (by unfold InRegion; bv_omega) (by decide)
  · refine (hfr.readBytes_eq (hrw.sub (by bv_omega)).readable (fun r hr => ?_) (by decide)).trans hin
    exact (hd r hr).sub_right _ ⟨by decide, by bv_omega⟩
  · refine (hfr.read64_eq_of_readable (hrw.sub (by bv_omega)).readable fun r hr => ?_).trans hcnt1
    exact (hd r hr).sub_right _ ⟨by decide, by bv_omega⟩
  · refine (hfr.readBytes_eq (hrw.sub (by bv_omega)).readable (fun r hr => ?_) (by decide)).trans hout
    exact (hd r hr).sub_right _ ⟨by decide, by bv_omega⟩
  · refine (hfr.read64_eq_of_readable (hrw.sub (by bv_omega)).readable fun r hr => ?_).trans hcnt2
    exact (hd r hr).sub_right _ ⟨by decide, by bv_omega⟩

theorem HmacSt.of_s2Frame_empty {F : ShaState → List (BitVec 8) → ShaState}
    {key : List (BitVec 8)} {m m' : Memory} {a : BitVec 64} {regs : List (BitVec 64 × ℕ)}
    (h : HmacSt m a F key []) (hrw : m.RW a 0x90) (hfr : S2Frame m m' regs)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 a 0x90) :
    HmacSt m' a F key [] :=
  HmacSt.of_s2FrameRO_empty h hrw (S2FrameRO.of_s2frame (roRegs := []) hfr) hd

theorem HExpCommonExt.of_s2FrameRO_352_592 {b : BitVec 64} {saltRO ikmRO infoRO : Bool}
    {roRegs : List (BitVec 64 × ℕ)} {F : ShaState → List (BitVec 8) → ShaState}
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s s' : State} {dstOff : BitVec 64} {dstLen : ℕ}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hc : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s)
    (hstat : s'.status = .Running) (hcc : CallingConventionPreserved s s')
    (hfr : S2FrameRO roRegs s.mem s'.mem [(hsp s₀ + dstOff, dstLen), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hdst : 352 ≤ dstOff.toNat ∧ dstOff.toNat < 592 ∧ dstOff.toNat + dstLen ≤ 592) :
    HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s' := by
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hc.common.frame
  have hd_low : ∀ r ∈ [(hsp s₀ + dstOff, dstLen), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
      DisjointRegions r.1 r.2 (hsp s₀) 32 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rcases hdst with ⟨_, _, _⟩; dsimp [extHookStack]; unfold DisjointRegions; bv_omega)
  have hd_208 : ∀ r ∈ [(hsp s₀ + dstOff, dstLen), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
      DisjointRegions r.1 r.2 (hsp s₀ + 208#64) 0x90 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rcases hdst with ⟨_, _, _⟩; dsimp [extHookStack]; unfold DisjointRegions; bv_omega)
  exact
    { common := HCommonExt.of_s2FrameRO_hsp hpre hc.common hstat hcc hfr ⟨hdst.2.1, hdst.2.2⟩ (by decide)
      m0_eq := (hfr.read64_eq_of_readable (hrw_hsp.sub (by bv_omega)).readable fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 0#64) ⟨by decide, by bv_omega⟩).trans hc.m0_eq
      m8_eq := (hfr.read64_eq_of_readable (hrw_hsp.sub (by bv_omega)).readable fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 8#64) ⟨by decide, by bv_omega⟩).trans hc.m8_eq
      m16_eq := (hfr.read64_eq_of_readable (hrw_hsp.sub (by bv_omega)).readable fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 16#64) ⟨by decide, by bv_omega⟩).trans hc.m16_eq
      m24_eq := (hfr.read64_eq_of_readable (hrw_hsp.sub (by bv_omega)).readable fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 24#64) ⟨by decide, by bv_omega⟩).trans hc.m24_eq
      hmac_208 := HmacSt.of_s2FrameRO_empty hc.hmac_208 (hrw_hsp.sub (by bv_omega)) hfr hd_208 }

theorem HExpCommonExt.of_s2Frame_352_592 {b : BitVec 64} {saltRO ikmRO infoRO : Bool}
    {roRegs : List (BitVec 64 × ℕ)} {F : ShaState → List (BitVec 8) → ShaState}
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s s' : State} {dstOff : BitVec 64} {dstLen : ℕ}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hc : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s)
    (hstat : s'.status = .Running) (hcc : CallingConventionPreserved s s')
    (hfr : S2Frame s.mem s'.mem [(hsp s₀ + dstOff, dstLen), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hdst : 352 ≤ dstOff.toNat ∧ dstOff.toNat < 592 ∧ dstOff.toNat + dstLen ≤ 592) :
    HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s' :=
  HExpCommonExt.of_s2FrameRO_352_592 hpre hc hstat hcc (S2FrameRO.of_s2frame hfr) hdst

theorem HExpCommonExt.of_fin_frame {b : BitVec 64} {saltRO ikmRO infoRO : Bool}
    {roRegs : List (BitVec 64 × ℕ)} {F : ShaState → List (BitVec 8) → ShaState}
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s s' : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hc : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s)
    (hstat : s'.status = .Running) (hcs : CalleeSaved s s')
    (hfr : S2Frame s.mem s'.mem [(hsp s₀ + 540#64, 32), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 16528#64, 16528)]) :
    HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s' := by
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hc.common.frame
  have hd_low : ∀ r ∈ [(hsp s₀ + 540#64, (32 : ℕ)), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 16528#64, 16528)],
      DisjointRegions r.1 r.2 (hsp s₀) 32 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  have hd_208 : ∀ r ∈ [(hsp s₀ + 540#64, (32 : ℕ)), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 16528#64, 16528)],
      DisjointRegions r.1 r.2 (hsp s₀ + 208#64) 0x90 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  exact
    { common := HCommonExt.of_fin_frame (outOff := 540#64) hpre hc.common hstat hcs hfr (by decide)
      m0_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 0#64) ⟨by decide, by bv_omega⟩).trans hc.m0_eq
      m8_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 8#64) ⟨by decide, by bv_omega⟩).trans hc.m8_eq
      m16_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 16#64) ⟨by decide, by bv_omega⟩).trans hc.m16_eq
      m24_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 24#64) ⟨by decide, by bv_omega⟩).trans hc.m24_eq
      hmac_208 := HmacSt.of_s2Frame_empty hc.hmac_208 (hrw_hsp.sub (by bv_omega)) hfr hd_208 }

theorem HExpCommonExt.of_s2Frame_okm {b : BitVec 64} {saltRO ikmRO infoRO : Bool}
    {roRegs : List (BitVec 64 × ℕ)} {F : ShaState → List (BitVec 8) → ShaState}
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s s' : State} {okmOff : BitVec 64} {okmSub : ℕ}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hc : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s)
    (hstat : s'.status = .Running) (hcc : CallingConventionPreserved s s')
    (hfr : S2Frame s.mem s'.mem [(okmA + okmOff, okmSub), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hokm : 0 < okmSub ∧ okmOff.toNat + okmSub ≤ okmLen) :
    HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s' := by
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hc.common.frame
  have hd_stk : DisjointRegions (okmA + okmOff) okmSub (hsp s₀) 592 := by
    have hd1 := hpre.disj_okm_stk.sub_left (okmA + okmOff)
      ⟨hokm.1, by have := hokm.2; have := hpre.okm_len; bv_omega⟩
    exact hd1.sub_right (hsp s₀) ⟨by decide, by bv_omega⟩
  have hd_low : ∀ r ∈ [(okmA + okmOff, okmSub), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
      DisjointRegions r.1 r.2 (hsp s₀) 32 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd_stk.sub_right (hsp s₀) ⟨by decide, by bv_omega⟩
    · dsimp [extHookStack]; unfold DisjointRegions; bv_omega
  have hd_208 : ∀ r ∈ [(okmA + okmOff, okmSub), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
      DisjointRegions r.1 r.2 (hsp s₀ + 208#64) 0x90 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd_stk.sub_right (hsp s₀ + 208#64) ⟨by decide, by bv_omega⟩
    · dsimp [extHookStack]; unfold DisjointRegions; bv_omega
  exact
    { common := HCommonExt.of_s2Frame_okm hpre hc.common hstat hcc hfr hokm (by decide)
      m0_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 0#64) ⟨by decide, by bv_omega⟩).trans hc.m0_eq
      m8_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 8#64) ⟨by decide, by bv_omega⟩).trans hc.m8_eq
      m16_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 16#64) ⟨by decide, by bv_omega⟩).trans hc.m16_eq
      m24_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 24#64) ⟨by decide, by bv_omega⟩).trans hc.m24_eq
      hmac_208 := HmacSt.of_s2Frame_empty hc.hmac_208 (hrw_hsp.sub (by bv_omega)) hfr hd_208 }

structure StateB1MemcpyExt (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + bv% (ls_off% "memcpy")
  exp      : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  lr_eq    : s.readReg64 .lr = b + bv% (ls_off% hkdfToSliceName + 776)
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

theorem HmacSt.of_s2FrameRO_counter_352 {roRegs : List (BitVec 64 × ℕ)} {m₀ m₁ : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key info : List (BitVec 8)} {b1 c : BitVec 8}
    (h₀ : HmacSt m₀ (hsp s₀ + 352#64) F key [])
    (hrw₀ : m₀.RW (hsp s₀) 688)
    (hinfo : info.length < 55)
    (hread : m₁.readBytes (hsp s₀ + 352#64) info.length = info)
    (hfr : S2FrameRO roRegs m₀ m₁ [(hsp s₀ + 352#64, info.length), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    let m₂ := (((m₁.write8 (hsp s₀ + 415#64) b1).write8 (hsp s₀ + 32#64) c).write8
      (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) c).write8
      (hsp s₀ + 415#64) (BitVec.ofNat 8 (info.length + 1))
    HmacSt m₂ (hsp s₀ + 352#64) F key (info ++ [c]) := by
  intro m₂
  rcases h₀ with ⟨_, _, _, hin, hcnt1, hout, hcnt2⟩
  have hlen : (info ++ [c]).length = info.length + 1 := by simp
  have hd_hi : ∀ (off : BitVec 64) (sz : ℕ),
      decide (416 ≤ off.toNat ∧ 0 < sz ∧ off.toNat + sz ≤ 496) = true →
      ∀ r ∈ [(hsp s₀ + 352#64, info.length), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
        DisjointRegions r.1 r.2 (hsp s₀ + off) sz := by
    intro off sz hoff r hr
    have ⟨_, _, _⟩ := of_decide_eq_true hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (dsimp [extHookStack]; unfold DisjointRegions; bv_omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen, Bytes.readBytes_add m₂ (hsp s₀ + 352#64) info.length 1]
    have h_info : m₂.readBytes (hsp s₀ + 352#64) info.length = info := by
      by_cases hi0 : info.length = 0
      · have hnil : info = [] := List.eq_nil_of_length_eq_zero hi0
        subst hnil; rfl
      · dsimp only [m₂]
        rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
              (by unfold DisjointRegions; bv_omega) (by omega),
            (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) 1 |>.write8 (by simp [InRegion])).readBytes_eq
              (by unfold DisjointRegions; bv_omega) (by omega),
            (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
              (by unfold DisjointRegions; bv_omega) (by omega),
            (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
              (by unfold DisjointRegions; bv_omega) (by omega)]
        exact hread
    have h_c : m₂.readBytes (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) 1 = [c] := by
      dsimp only [Memory.readBytes, m₂]
      rw [Memory.read8_write8_ne (by bv_omega), Memory.read8_write8_same]
    rw [h_info, h_c]
  · rw [hlen, show hsp s₀ + 352#64 + 0x3f#64 = hsp s₀ + 415#64 by bv_omega]
    exact Memory.read8_write8_same _ _ _
  · dsimp only [m₂]
    rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
          (by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) 1 |>.write8 (by simp [InRegion])).readBytes_eq
          (by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
          (by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
          (by unfold DisjointRegions; bv_omega) (by decide),
        show hsp s₀ + 352#64 + 0x40#64 = hsp s₀ + 416#64 by bv_lin]
    rw [show hsp s₀ + 352#64 + 0x40#64 = hsp s₀ + 416#64 by bv_lin] at hin
    exact (hfr.readBytes_eq (hrw₀.sub (by bv_omega)).readable (hd_hi 416#64 32 (by decide)) (by decide)).trans hin
  · dsimp only [m₂]
    rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        show hsp s₀ + 352#64 + 0x60#64 = hsp s₀ + 448#64 by bv_lin]
    rw [show hsp s₀ + 352#64 + 0x60#64 = hsp s₀ + 448#64 by bv_lin] at hcnt1
    exact (hfr.read64_eq_of_readable (hrw₀.sub (by bv_omega)).readable (hd_hi 448#64 8 (by decide))).trans hcnt1
  · dsimp only [m₂]
    rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
          (by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) 1 |>.write8 (by simp [InRegion])).readBytes_eq
          (by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
          (by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
          (by unfold DisjointRegions; bv_omega) (by decide),
        show hsp s₀ + 352#64 + 0x68#64 = hsp s₀ + 456#64 by bv_lin]
    rw [show hsp s₀ + 352#64 + 0x68#64 = hsp s₀ + 456#64 by bv_lin] at hout
    exact (hfr.readBytes_eq (hrw₀.sub (by bv_omega)).readable (hd_hi 456#64 32 (by decide)) (by decide)).trans hout
  · dsimp only [m₂]
    rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        show hsp s₀ + 352#64 + 0x88#64 = hsp s₀ + 488#64 by bv_lin]
    rw [show hsp s₀ + 352#64 + 0x88#64 = hsp s₀ + 488#64 by bv_lin] at hcnt2
    exact (hfr.read64_eq_of_readable (hrw₀.sub (by bv_omega)).readable (hd_hi 488#64 8 (by decide))).trans hcnt2

structure StateB1FinExt (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% finalizeFixed3Name)
  exp     : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% hkdfToSliceName + 1096)
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 540#64
  x1_eq   : s.readReg64 .x1 = hsp s₀ + 32#64
  x21_eq  : s.readReg64 .x21 = BitVec.ofNat 64 okmLen
  x22_eq  : s.readReg64 .x22 = okmA
  x24_eq  : s.readReg64 .x24 = 32#64
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32)
  x28_eq  : s.readReg64 .x28 = hsp s₀ + 352#64
  hmac_32 : HmacSt s.mem (hsp s₀ + 32#64) F (hkdfExtractBytes F salt ikm) (info ++ [1#8])

structure StateB1RetFinExt (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% hkdfToSliceName + 1096)
  exp    : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  x21_eq : s.readReg64 .x21 = BitVec.ofNat 64 okmLen
  x22_eq : s.readReg64 .x22 = okmA
  x24_eq : s.readReg64 .x24 = 32#64
  x25_eq : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq : s.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32)
  x28_eq : s.readReg64 .x28 = hsp s₀ + 352#64
  t1_540 : s.mem.readBytes (hsp s₀ + 540#64) 32 = Expand.t1 F (hkdfExtractBytes F salt ikm) info

structure StateB1DoneExt (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% hkdfToSliceName + 1132)
  exp    : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  x21_eq : s.readReg64 .x21 = BitVec.ofNat 64 okmLen
  x22_eq : s.readReg64 .x22 = okmA
  x24_eq : s.readReg64 .x24 = 32#64
  x25_eq : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq : s.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32)
  x28_eq : s.readReg64 .x28 = hsp s₀ + 352#64
  t1_508 : s.mem.readBytes (hsp s₀ + 508#64) 32 = Expand.t1 F (hkdfExtractBytes F salt ikm) info
  okm_32 : s.mem.readBytes okmA 32 = Expand.t1 F (hkdfExtractBytes F salt ikm) info

section Block1Segments

variable {img : Obj.Image} {b : BitVec 64} {F : ShaCompress} {ext : String → Option (State → State)}

/-- Segment `B1a` (`b + hex:634fc` → `b + hex:78a48`, 36 steps): copies `Hmac(PRK, [])` from
`hsp s₀ + 208#64` to `hsp s₀ + 352#64`, stores `hsp s₀ + 508#64` at `[sp + 24]`, sets `x24 = 32`,
and calls `memcpy(hsp s₀ + 352#64, infoA, info.length)`. -/
theorem seg_b1a_runsTo_ext {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateExtractDoneExt b roRegs F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateB1MemcpyExt b roRegs F salt ikm info infoA okmA okmLen s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.common.status
  have hsp_eq := hx.common.sp_eq; have hx29 := hx.common.x29_eq
  have hx19 := hx.x19_eq; have hx22 := hx.x22_eq
  have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  have hm0 : s.mem.read64 (hsp s₀) = BitVec.ofNat 64 okmLen := by simpa [BitVec.add_zero] using hx.m0_eq
  have hm8 := hx.m8_eq; have hm16 := hx.m16_eq
  have hpos_208 : s.mem.read8 (hsp s₀ + 271#64) = 0#8 := by
    simpa [BitVec.add_assoc] using hx.hmac_208.2.2.1
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.common.frame
  rcases okmLen_ge32_lemmas hpre.okm_len with ⟨hokm_c, hokm_ule, hokm_ult⟩
  rcases Expand.cmp_lt64_lemmas (by have := hpre.info_lt; omega : info.length < 64) with
    ⟨h_info_ule, h_info_ult, h_info_cmp⟩
  iterate 36 kdf_step
  refine RunsTo.refl ?_
  refine ⟨by kdf_reg,
    { common := HCommonExt.of_agreesOutside_hsp (off := 24#64) (sz := 472) hx.common
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
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    ?_⟩
  simp only [Expand.mem_setMem]
  refine HmacSt.of_copy_empty_208_352 hx.hmac_208 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := { decide := true }) only [arm64_norm]

private theorem seg_b1b_post {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s s₁ : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateB1MemcpyExt b roRegs F salt ikm info infoA okmA okmLen s₀ s)
    (hpc : s₁.pc = b + bv% (ls_off% hkdfToSliceName + 776)) (hrun : s₁.status = .Running)
    (hcc : CallingConventionPreserved s s₁)
    (hread_info : s₁.mem.readBytes (hsp s₀ + 352#64) info.length = info)
    (hfr : S2FrameRO roRegs s.mem s₁.mem
      [(hsp s₀ + 352#64, info.length), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    RunsTo (tripleRatchetProgAtExt b ext) s₁
      (StateB1FinExt b roRegs F salt ikm info infoA okmA okmLen s₀) := by
  have hc1 : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s₁ :=
    HExpCommonExt.of_s2FrameRO_352_592 (dstOff := 352#64) (dstLen := info.length)
      hpre hx.exp hrun hcc hfr ⟨by decide, by decide, by have := hpre.info_lt; bv_omega⟩
  have hsp_eq := hc1.common.sp_eq; have hx29 := hc1.common.x29_eq
  have hx20 : s₁.readReg64 .x20 = 0#64 := (cc_x20 hcc).trans hx.x20_eq
  have hx21 : s₁.readReg64 .x21 = BitVec.ofNat 64 okmLen := (cc_x21 hcc).trans hx.x21_eq
  have hx22 : s₁.readReg64 .x22 = okmA := (cc_x22 hcc).trans hx.x22_eq
  have hx24 : s₁.readReg64 .x24 = 32#64 := (cc_x24 hcc).trans hx.x24_eq
  have hx25 : s₁.readReg64 .x25 = BitVec.ofNat 64 info.length := (cc_x25 hcc).trans hx.x25_eq
  have hx28 : s₁.readReg64 .x28 = hsp s₀ + 352#64 := (cc_x28 hcc).trans hx.x28_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hinfo_lt := hpre.info_lt
  have hrw₀ : s.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.exp.common.frame
  have hrw_wb : s₁.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hc1.common.frame
  rcases canWrite_hsp_352_add hrw_wb (by omega : info.length < 64) with ⟨hcw_pos1, hcw_pos2⟩
  have hze32 := zeroExtend64_truncate32_ofNat64 (by omega : info.length < 64)
  have hand255 := Expand.zeroExtend64_and255_truncate32_ofNat64 (by omega : info.length < 64)
  have hand64_255 := Expand.and64_255_ofNat64 (by omega : info.length < 64)
  have hand40 := Expand.and_0xffffffffff_ofNat64 (by omega : info.length < 64)
  rcases Expand.cmp32_lt63_lemmas (by omega : info.length < 63) with ⟨hcmp63_eq, hcmp63_ne, hcmp63_z⟩
  have hadd1 := Expand.zeroExtend64_add1_truncate32_ofNat64 (by omega : info.length < 63)
  iterate 26 kdf_step
  refine RunsTo.refl ?_
  have hhm_m2 : HmacSt
      ((((s₁.mem.write8 (hsp s₀ + 415#64) (BitVec.ofNat 8 info.length)).write8
        (hsp s₀ + 32#64) 1#8).write8
        (hsp s₀ + 352#64 + BitVec.ofNat 64 info.length) 1#8).write8
        (hsp s₀ + 415#64) (BitVec.ofNat 8 (info.length + 1)))
      (hsp s₀ + 352#64) F (hkdfExtractBytes F salt ikm) (info ++ [1#8]) :=
    HmacSt.of_s2FrameRO_counter_352 hx.hmac_352 hrw₀ hinfo_lt hread_info hfr
  refine ⟨by kdf_reg,
    HExpCommonExt.of_agreesOutside_32_560 (off := 32#64) (sz := 560) hc1
      (by kdf_reg) (by kdf_reg) (by kdf_reg)
      (by prove_agrees_hsp) (by decide)
      (by prove_hmac_208 hc1.hmac_208),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg,
    by
      simp (config := { decide := true }) only [arm64_norm]
      rcases hpre.okm_len with rfl | rfl | rfl <;> rfl,
    by kdf_reg, ?_⟩
  simp only [Expand.mem_setMem]
  refine HmacSt.of_copy_352_32 hhm_m2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := { decide := true }) only [arm64_norm]

/-- Segment `B1b` (`img.base + hex:78a48` → `img.base + hex:6ce50`, 1 `memcpy` + 26 steps): `memcpy`
of `info` (RO or RW) to `hsp s₀ + 352#64`, appends counter byte `1#8`, sets `x26 = okmLen - 32`,
copies `Hmac` to `hsp s₀ + 32#64`, and calls `finalize_fixed(hsp s₀ + 540#64, hsp s₀ + 32#64)`. -/
theorem seg_b1b_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateB1MemcpyExt img.base roRegs F salt ikm info infoA okmA okmLen s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateB1FinExt img.base roRegs F salt ikm info infoA okmA okmLen s₀) := by
  have hx2_nat : (s.readReg64 .x2).toNat = info.length := by
    have := hpre.info_lt; rw [hx.x2_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hinfo_inv := HFrameExt.info_inv hpre hx.exp.common.frame
  have hsrc_perm : if infoRO then s.mem.Readable infoA info.length ∧
      (∀ a, InRegion infoA info.length a → ∃ r ∈ roRegs, InRegion r.1 r.2 a)
    else RW s.mem infoA info.length := by
    cases hro : infoRO
    · have hp := hinfo_inv.perm_inv; rw [hro] at hp
      simp only [Bool.false_eq_true, ↓reduceIte] at hp ⊢
      exact hp.1
    · have hp := hinfo_inv.perm_inv; rw [hro] at hp
      simp only [↓reduceIte] at hp ⊢
      exact ⟨hinfo_inv.readable, hp⟩
  have hmc := memcpy_any_subroutine_runsTo hs.hooks infoRO roRegs hfrz hsym
    hx.pc_eq hx.exp.common.status hx.x0_eq hx.x1_eq hx2_nat
    hinfo_inv.bytes_eq
    ((HFrameExt.rw_hsp hpre hx.exp.common.frame).sub (by have := hpre.info_lt; bv_omega))
    hsrc_perm
    (by rw [hx.exp.common.sp_eq]; exact HFrameExt.rw_ext_stk hpre hx.exp.common.frame)
    (Or.inr (by rw [hx.exp.common.sp_eq]; have := hpre.info_lt; dsimp [extHookStack]; unfold DisjointRegions; bv_omega))
    (fun a ha => by
      have ho := hinfo_inv.out_stk a ha; have := hpre.info_lt
      unfold OutsideRegion at ho ⊢; bv_omega)
    (fun a ha => by
      rw [hx.exp.common.sp_eq]
      have ho := hinfo_inv.out_stk a ha
      dsimp [extHookStack]; unfold OutsideRegion at ho ⊢; bv_omega)
    (by rw [hx.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).1)
  refine hmc.trans fun s₁ ⟨hpc₁, hrun₁, hcc₁, _, hread₁, _, hfr₁⟩ => ?_
  rw [hx.lr_eq] at hpc₁; rw [hx.exp.common.sp_eq] at hfr₁
  exact runsTo_toE (seg_b1b_post hpre hx hpc₁ hrun₁ hcc₁ hread₁ hfr₁)

/-- `finalize_fixed` #1 (`img.base + hex:6ce50` → `img.base + hex:636cc`): computes
`T(1) = Expand.t1 F prk info` at `hsp s₀ + 540#64`. -/
theorem fin_b1_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateB1FinExt img.base roRegs F salt ikm info infoA okmA okmLen s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateB1RetFinExt img.base roRegs F salt ikm info infoA okmA okmLen s₀) := by
  have hrw_hsp := HFrameExt.rw_hsp hpre hx.exp.common.frame
  have hrw_sub := HFrameExt.rw_sub_16528 hpre hx.exp.common.frame
  have hhm_n : HmacStN s.mem (s.readReg64 .x1) F
      (effectiveHmacKey F (hkdfExtractBytes F salt ikm)) [] (info ++ [1#8]) := by
    rw [hx.x1_eq, effectiveHmacKey_of_le F (by simp [hkdfExtractBytes, hmacWith])]
    exact HmacStN.of_hmacSt hx.hmac_32
  have hfin_pre : FinPre3GenExt img F (hkdfExtractBytes F salt ikm) [] (info ++ [1#8]) s :=
    { frz          := hfrz
      sym          := hsym
      pc_eq        := hx.pc_eq
      status       := hx.exp.common.status
      pfx_lt       := by decide
      tail_lt      := by have := hpre.info_lt; simp; omega
      hmac_st      := hhm_n
      rw_out       := by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_hm        := by rw [hx.x1_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_fsp       := by rw [hx.exp.common.sp_eq]; exact hrw_sub
      disj_out_hm  := by rw [hx.x0_eq, hx.x1_eq]; unfold DisjointRegions; bv_omega
      disj_out_fsp := by rw [hx.x0_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega
      disj_hm_fsp  := by rw [hx.x1_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega
      sp_aligned   := by rw [hx.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1 }
  refine (hs.fin_ok hfin_pre).mono fun s' ⟨hpc', hrun', hcs, ht1, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, List.nil_append] at ht1
  rw [hx.x0_eq, hx.x1_eq, hx.exp.common.sp_eq] at hfr
  exact ⟨hpc',
    HExpCommonExt.of_fin_frame hpre hx.exp hrun' hcs hfr,
    (cs_x21 hcs).trans hx.x21_eq, (cs_x22 hcs).trans hx.x22_eq,
    (cs_x24 hcs).trans hx.x24_eq, (cs_x25 hcs).trans hx.x25_eq,
    (cs_x26 hcs).trans hx.x26_eq, (cs_x28 hcs).trans hx.x28_eq,
    ht1⟩

private structure StateB1dMemcpy (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% "memcpy")
  exp    : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  lr_eq  : s.readReg64 .lr = b + bv% (ls_off% hkdfToSliceName + 1112)
  x0_eq  : s.readReg64 .x0 = okmA
  x1_eq  : s.readReg64 .x1 = hsp s₀ + 540#64
  x2_eq  : s.readReg64 .x2 = 32#64
  x21_eq : s.readReg64 .x21 = BitVec.ofNat 64 okmLen
  x22_eq : s.readReg64 .x22 = okmA
  x24_eq : s.readReg64 .x24 = 32#64
  x25_eq : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq : s.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32)
  x28_eq : s.readReg64 .x28 = hsp s₀ + 352#64
  t1_540 : s.mem.readBytes (hsp s₀ + 540#64) 32 = Expand.t1 F (hkdfExtractBytes F salt ikm) info

private theorem seg_b1d_pre {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hx : StateB1RetFinExt b roRegs F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateB1dMemcpy b roRegs F salt ikm info infoA okmA okmLen s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status
  have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hx21 := hx.x21_eq; have hx22 := hx.x22_eq; have hx24 := hx.x24_eq
  have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx28 := hx.x28_eq
  iterate 4 kdf_step
  refine RunsTo.refl ?_
  exact ⟨by kdf_reg,
    { common := ⟨by kdf_reg, by kdf_reg, by kdf_reg, hx.exp.common.saved, hx.exp.common.frame⟩
      m0_eq := hx.exp.m0_eq
      m8_eq := hx.exp.m8_eq
      m16_eq := hx.exp.m16_eq
      m24_eq := hx.exp.m24_eq
      hmac_208 := hx.exp.hmac_208 },
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    hx.t1_540⟩

set_option maxHeartbeats 1600000 in
private theorem seg_b1d_post {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s₁ s₂ : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateB1dMemcpy b roRegs F salt ikm info infoA okmA okmLen s₀ s₁)
    (hpc : s₂.pc = b + bv% (ls_off% hkdfToSliceName + 1112)) (hrun : s₂.status = .Running)
    (hcc : CallingConventionPreserved s₁ s₂)
    (hokm_32 : s₂.mem.readBytes okmA 32 = Expand.t1 F (hkdfExtractBytes F salt ikm) info)
    (hfr : S2Frame s₁.mem s₂.mem [(okmA, 32), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    RunsTo (tripleRatchetProgAtExt b ext) s₂
      (StateB1DoneExt b roRegs F salt ikm info infoA okmA okmLen s₀) := by
  have hfr0 : S2Frame s₁.mem s₂.mem [(okmA + 0#64, 32), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    simpa [BitVec.add_zero] using hfr
  have hc2 : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s₂ :=
    HExpCommonExt.of_s2Frame_okm (okmOff := 0#64) (okmSub := 32) hpre hx.exp hrun hcc hfr0
      ⟨by decide, by have := hpre.okm_len; rw [BitVec.toNat_zero, Nat.zero_add]; omega⟩
  have hsp_eq := hc2.common.sp_eq; have hx29 := hc2.common.x29_eq
  have hx21 : s₂.readReg64 .x21 = BitVec.ofNat 64 okmLen := (cc_x21 hcc).trans hx.x21_eq
  have hx22 : s₂.readReg64 .x22 = okmA := (cc_x22 hcc).trans hx.x22_eq
  have hx24 : s₂.readReg64 .x24 = 32#64 := (cc_x24 hcc).trans hx.x24_eq
  have hx25 : s₂.readReg64 .x25 = BitVec.ofNat 64 info.length := (cc_x25 hcc).trans hx.x25_eq
  have hx26 : s₂.readReg64 .x26 = BitVec.ofNat 64 (okmLen - 32) := (cc_x26 hcc).trans hx.x26_eq
  have hx28 : s₂.readReg64 .x28 = hsp s₀ + 352#64 := (cc_x28 hcc).trans hx.x28_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hm24_2 : s₂.mem.read64 (hsp s₀ + 24#64) = hsp s₀ + 508#64 := hc2.m24_eq
  have hrw1 : s₁.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.exp.common.frame
  have hrw2 : s₂.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hc2.common.frame
  have ht1_m2 : s₂.mem.readBytes (hsp s₀ + 540#64) 32 =
      Expand.t1 F (hkdfExtractBytes F salt ikm) info := by
    refine (hfr.readBytes_eq (hrw1.sub (by bv_omega)) (fun r hr => ?_) (by decide)).trans hx.t1_540
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only
    · exact (hpre.disj_okm_stk.sub_left okmA
        ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (hsp s₀ + 540#64)
        ⟨by decide, by bv_omega⟩
    · dsimp [extHookStack]; unfold DisjointRegions; bv_omega
  iterate 5 kdf_step
  refine RunsTo.refl ?_
  refine ⟨by kdf_reg,
    HExpCommonExt.of_agreesOutside_352_592 (off := 508#64) (sz := 32) hc2
      (by kdf_reg) (by kdf_reg) (by kdf_reg)
      (by prove_agrees_hsp) (by decide),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    ?_, ?_⟩
  · simp only [Expand.mem_setMem]
    exact readBytes_32_hsp_508_of_540 ht1_m2
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
  · have hd : DisjointRegions (hsp s₀ + 508#64) 32 okmA 32 :=
      (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 508#64)
        ⟨by decide, by bv_omega⟩).sub_right okmA
        ⟨by decide, by have := hpre.okm_len; bv_omega⟩
    have hA2 : AgreesOutside s₂.mem
        ((((s₂.mem.write64 (hsp s₀ + 508#64) (s₂.mem.read64 (hsp s₀ + 540#64))).write64
          (hsp s₀ + 516#64) (s₂.mem.read64 (hsp s₀ + 548#64))).write64
          (hsp s₀ + 524#64) (s₂.mem.read64 (hsp s₀ + 556#64))).write64
          (hsp s₀ + 532#64) (s₂.mem.read64 (hsp s₀ + 564#64)))
        (hsp s₀ + 508#64) 32 := by prove_agrees_hsp
    dsimp only [Expand.mem_setMem]
    exact (hA2.readBytes_eq hd (by decide)).trans hokm_32

/-- Segment `B1d` (`img.base + hex:636cc` → `img.base + hex:636f0`, 4 steps + `memcpy` + 5 steps):
copies `T(1)` (32 B) from `hsp s₀ + 540#64` to `okmA` and caches `T(1)` at `hsp s₀ + 508#64`. -/
theorem seg_b1d_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateB1RetFinExt img.base roRegs F salt ikm info infoA okmA okmLen s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateB1DoneExt img.base roRegs F salt ikm info infoA okmA okmLen s₀) := by
  refine RunsTo.trans_toE_inv hfrz hsym (seg_b1d_pre hx)
    fun s₁ hf₁ hs₁ hx₁ => ?_
  have hx2_nat : (s₁.readReg64 .x2).toNat = (Expand.t1 F (hkdfExtractBytes F salt ikm) info).length := by
    rw [hx₁.x2_eq, Expand.t1_length]; rfl
  have hrw_hsp : s₁.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx₁.exp.common.frame
  have hrw_okm : s₁.mem.RW okmA okmLen := HFrameExt.rw_okm hpre hx₁.exp.common.frame
  have hd_dst_src : DisjointRegions okmA 32 (hsp s₀ + 540#64) 32 :=
    (hpre.disj_okm_stk.sub_left okmA
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (hsp s₀ + 540#64)
      ⟨by decide, by bv_omega⟩
  have hd_dst_stk : DisjointRegions okmA 32 (s₁.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hx₁.exp.common.sp_eq]
    exact (hpre.disj_okm_stk.sub_left okmA
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right
      (hsp s₀ - BitVec.ofNat 64 extHookStack) ⟨by decide, by dsimp [extHookStack]; bv_omega⟩
  have hmc := memcpy_opt_subroutine_runsTo hs.hooks.memcpy hf₁ hs₁
    hx₁.pc_eq hx₁.exp.common.status hx₁.x0_eq hx₁.x1_eq hx2_nat
    (by rw [Expand.t1_length]; exact hx₁.t1_540)
    (by rw [Expand.t1_length]; exact hrw_okm.sub (by have := hpre.okm_len; bv_omega))
    (by rw [Expand.t1_length]; exact hrw_hsp.sub (by bv_omega))
    (by rw [hx₁.exp.common.sp_eq]; exact HFrameExt.rw_ext_stk hpre hx₁.exp.common.frame)
    (by rw [Expand.t1_length]; exact Or.inr hd_dst_src)
    (by rw [Expand.t1_length]; exact Or.inr hd_dst_stk)
    (Or.inr (by rw [Expand.t1_length, hx₁.exp.common.sp_eq]; dsimp [extHookStack]; unfold DisjointRegions; bv_omega))
    (by rw [hx₁.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).1)
  refine hmc.trans fun s₂ ⟨hpc₂, hrun₂, hcc₂, _, hread₂, _, hfr₂⟩ => ?_
  rw [hx₁.lr_eq] at hpc₂; rw [hx₁.exp.common.sp_eq] at hfr₂
  rw [Expand.t1_length] at hread₂ hfr₂
  exact runsTo_toE (seg_b1d_post hpre hx₁ hpc₂ hrun₂ hcc₂ hread₂ hfr₂)

/-- Full Extract + Expand Block 1 (`img.base + hex:63284` → `img.base + hex:636f0`) of `spqr::kdf::hkdf_to_slice`. -/
theorem block1_phase_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hfrz : img.FrozenLoaded s₀) (hsym : s₀.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s₀
      (StateB1DoneExt img.base roRegs F salt ikm info infoA okmA okmLen s₀) :=
  RunsToE.trans_inv hfrz hsym (extract_phase_runsTo_ext hs hfrz hsym hpre) fun _ hf0 hs0 hx0 =>
  RunsTo.trans_toE_inv hf0 hs0 (seg_b1a_runsTo_ext hpre hx0) fun _ hf1 hs1 hx1 =>
  RunsToE.trans_inv hf1 hs1 (seg_b1b_runsTo_ext hs hf1 hs1 hpre hx1) fun _ hf2 hs2 hx2 =>
  RunsToE.trans_inv hf2 hs2 (fin_b1_runsTo_ext hs hf2 hs2 hpre hx2) fun _ hf3 hs3 hx3 =>
  seg_b1d_runsTo_ext hs hf3 hs3 hpre hx3

end Block1Segments

/-! ## Postcondition, Epilogue (`hex:634a8`), `okmLen = 32` Exit, & Loop Entry (`hex:637b8`) -/

def HPostCSExt (roRegs : List (BitVec 64 × ℕ)) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s' : State) : Prop :=
  s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
  s'.mem.readBytes okmA okmLen = hkdfExpand F (hkdfExtractBytes F salt ikm) info okmLen ∧
  HFrameExt roRegs okmLen s₀ s'.mem

structure StateDoneExt (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% hkdfToSliceName + 548)
  common  : HCommonExt roRegs okmLen s₀ s
  okm_all : s.mem.readBytes okmA okmLen = hkdfExpand F (hkdfExtractBytes F salt ikm) info okmLen

section EpilogueAndLoopEntry

variable {b : BitVec 64} {F : ShaCompress} {ext : String → Option (State → State)}

theorem epilogue_runsTo_ext {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateDoneExt b roRegs F salt ikm info okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (HPostCSExt roRegs F salt ikm info okmA okmLen s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp_eq := hx.common.sp_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.common.frame
  rcases hx.common.saved with
    ⟨m592, m600, m608, m616, m624, m632, m640, m648, m656, m664, m672, m680⟩
  iterate 21 kdf_step
  refine RunsTo.refl ?_
  have hA : AgreesOutside s.mem
      ((((((((s.mem.write64 (hsp s₀ + 32#64) 0#64).write64 (hsp s₀ + 40#64) 0#64).write64
        (hsp s₀ + 48#64) 0#64).write64 (hsp s₀ + 56#64) 0#64).write64
        (hsp s₀ + 64#64) 0#64).write64 (hsp s₀ + 72#64) 0#64).write64
        (hsp s₀ + 80#64) 0#64).write64 (hsp s₀ + 88#64) 0#64
      |>.write64 (hsp s₀ + 256#64) 0#64 |>.write64 (hsp s₀ + 264#64) 0#64
      |>.write64 (hsp s₀ + 240#64) 0#64 |>.write64 (hsp s₀ + 248#64) 0#64
      |>.write64 (hsp s₀ + 224#64) 0#64 |>.write64 (hsp s₀ + 232#64) 0#64
      |>.write64 (hsp s₀ + 208#64) 0#64 |>.write64 (hsp s₀ + 216#64) 0#64)
      (hsp s₀ + 32#64) 240 := by prove_agrees_hsp
  have hd_okm : DisjointRegions (hsp s₀ + 32#64) 240 okmA okmLen :=
    hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 32#64) ⟨by decide, by bv_omega⟩
  refine ⟨by kdf_reg, by kdf_reg,
    ⟨by kdf_reg, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> kdf_reg⟩,
    (hA.readBytes_eq hd_okm (by have := hpre.okm_len; omega)).trans hx.okm_all,
    HFrameExt.of_agreesOutside_hsp (off := 32#64) (sz := 240) hx.common.frame hA (by decide)⟩

end EpilogueAndLoopEntry

end CryptoVerification.SpqrV1.Kdf.HkdfToSliceExtProof

