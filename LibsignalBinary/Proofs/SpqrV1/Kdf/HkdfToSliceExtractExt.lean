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
import LibsignalBinary.Proofs.SpqrV1.Kdf.HooksExt
import LibsignalBinary.Proofs.SpqrV1.Chain.Defs -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.Repr -- shake: keep

/-!
# `spqr::kdf::hkdf_to_slice`: Contract-Backed Extract Segments

Proves the prologue, initial `new_from_slice` call, and `ikm` absorption (`0x63284 → 0x633cc`)
under `HkdfStubsExt` and `HPreExt`.
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
attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint
  extractLsb'_56_8_read64
  read8_write64_264_271

@[local simp, local arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [(ls_off% hkdfToSliceName) → (ls_off% hkdfToSliceName + 336)]

section ExtractSegments

variable {img : Obj.Image} {b : BitVec 64} {F : ShaCompress} {ext : String → Option (State → State)}

/-- Segment `E0` (`b + hex:63284` → `b + hex:66fa0`, 18 steps): prologue saving `x19..x30` at
`hsp s₀ + 592 .. 688`, setting `sp = hsp s₀`, `x29 = hsp s₀ + 592#64`, moving arguments into
`x22..x27`, and calling `new_from_slice(hsp s₀ + 32#64, saltA, salt.length)`. -/
theorem seg_e0_runsTo_ext {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀) :
    RunsTo (tripleRatchetProgAtExt b ext) s₀
      (StateENfs1Ext b roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀) := by
  have hpc := hpre.pc_eq; have hrun := hpre.status
  have hx0 := hpre.x0_eq; have hx1 := hpre.x1_eq; have hx2 := hpre.x2_eq; have hx3 := hpre.x3_eq
  have hx4 := hpre.x4_eq; have hx5 := hpre.x5_eq; have hx6 := hpre.x6_eq; have hx7 := hpre.x7_eq
  have hsp_al := hpre.sp_aligned; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s₀.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre (S2FrameRO.refl roRegs s₀.mem _)
  iterate 18 kdf_step
  refine RunsTo.refl ⟨by kdf_reg, ⟨by kdf_reg, by kdf_reg, by kdf_reg, ?_, ?_⟩,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg⟩
  · simp only [Expand.mem_setMem]
    exact ⟨by simp (config := { decide := true }) only [arm64_norm], by simp (config := { decide := true }) only [arm64_norm],
      by simp (config := { decide := true }) only [arm64_norm], by simp (config := { decide := true }) only [arm64_norm],
      by simp (config := { decide := true }) only [arm64_norm], by simp (config := { decide := true }) only [arm64_norm],
      by simp (config := { decide := true }) only [arm64_norm], by simp (config := { decide := true }) only [arm64_norm],
      by simp (config := { decide := true }) only [arm64_norm], by simp (config := { decide := true }) only [arm64_norm],
      by simp (config := { decide := true }) only [arm64_norm], by simp (config := { decide := true }) only [arm64_norm]⟩
  · exact HFrameExt.of_agreesOutside_hsp (off := 592#64) (sz := 96)
      (S2FrameRO.refl roRegs s₀.mem _) (by prove_agrees_hsp) (by decide)

/-- `new_from_slice` #1 (`img.base + hex:66fa0` → `img.base + hex:632cc`): initializes
`Hmac(effectiveHmacKey F salt, [])` at `hsp s₀ + 40#64`. -/
theorem nfs1_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s : State} (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateENfs1Ext img.base roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateERet1Ext img.base roRegs F salt ikm info ikmA infoA okmA okmLen s₀) := by
  have hx2_nat : (s.readReg64 .x2).toNat = salt.length := by
    rw [hx.x2_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hpre.salt_lt; omega)]
  have hsalt_inv := HFrameExt.salt_inv hpre hx.common.frame
  have hnpre : Nfs3GenPreExt img saltRO roRegs s := {
    frz          := hfrz
    sym          := hsym
    pc_eq        := hx.pc_eq
    status       := hx.common.status
    key_lt       := by rw [hx2_nat]; exact hpre.salt_lt
    ro_iv_bytes  := HFrameExt.ro_iv_bytes hpre hx.common.frame
    base_al      := hpre.base_al
    ro_iv_read   := HFrameExt.ro_iv_read hpre hx.common.frame
    disj_iv_stk  := by
      rw [hx.common.sp_eq]
      exact hpre.disj_iv_stk.sub_right (hsp s₀ - 16928#64) ⟨by decide, by bv_omega⟩
    rw_out       := by rw [hx.x0_eq]; exact (HFrameExt.rw_hsp hpre hx.common.frame).sub (by bv_omega)
    rw_stk       := by rw [hx.common.sp_eq]; exact HFrameExt.rw_sub_16928 hpre hx.common.frame
    disj_out_stk := by rw [hx.x0_eq, hx.common.sp_eq]; unfold DisjointRegions; bv_omega
    key_read     := by rw [hx.x1_eq, hx2_nat]; exact hsalt_inv.readable
    key_perm     := by
      rw [hx.x1_eq, hx2_nat]
      cases hsr : saltRO
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hp := hsalt_inv.perm_inv; rw [hsr] at hp
        simp only [Bool.false_eq_true, ↓reduceIte] at hp; exact hp.1
      · simp only [↓reduceIte]
        have hp := hsalt_inv.perm_inv; rw [hsr] at hp; simp only [↓reduceIte] at hp
        exact ⟨hpre.salt_ro_le hsr, hp⟩
    out_key_stk  := fun a ha => by
      rw [hx.x1_eq, hx2_nat] at ha
      rw [hx.common.sp_eq]
      have hout := hsalt_inv.out_stk a ha
      unfold OutsideRegion at hout ⊢; bv_omega
    out_key_out  := fun a ha => by
      rw [hx.x1_eq, hx2_nat] at ha
      rw [hx.x0_eq]
      have hout := hsalt_inv.out_stk a ha
      unfold OutsideRegion at hout ⊢; bv_omega
    sp_aligned   := by rw [hx.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).1
  }
  refine (hs.nfs_ok hnpre).mono fun s' ⟨hpc', hrun', hcs, htag, hhm, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq] at htag
  have hx0_8 : s.readReg64 .x0 + 8#64 = hsp s₀ + 40#64 := by rw [hx.x0_eq]; bv_lin
  have hsalt_s : s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat = salt := by
    rw [hx.x1_eq, hx2_nat]; exact hsalt_inv.bytes_eq
  rw [hx0_8, hsalt_s] at hhm; rw [hx.x0_eq, hx.common.sp_eq] at hfr
  exact ⟨hpc', HCommonExt.of_nfs_frameRO hpre hx.common hrun' hcs hfr,
    (hcs.2 .x22 (by simp)).trans hx.x22_eq, (hcs.2 .x23 (by simp)).trans hx.x23_eq,
    (hcs.2 .x24 (by simp)).trans hx.x24_eq, (hcs.2 .x25 (by simp)).trans hx.x25_eq,
    (hcs.2 .x26 (by simp)).trans hx.x26_eq, (hcs.2 .x27 (by simp)).trans hx.x27_eq, htag, hhm⟩

private theorem s2Frame_disj_208_hi {s₀ : State} {n : ℕ} {off : BitVec 64} {sz : ℕ}
    (hn : n < 64) (hoff : decide (272 ≤ off.toNat ∧ 0 < sz ∧ off.toNat + sz ≤ 688) = true) :
    ∀ r ∈ [(hsp s₀ + 208#64, n), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
      DisjointRegions r.1 r.2 (hsp s₀ + off) sz := by
  have ⟨h1, h2, h3⟩ := of_decide_eq_true hoff; intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> (dsimp [extHookStack]; unfold DisjointRegions; bv_omega)

private structure StateE1Lt64Memcpy (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (ikmA infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + bv% (ls_off% "memcpy")
  common   : HCommonExt roRegs okmLen s₀ s
  lr_eq    : s.readReg64 .lr = b + bv% (ls_off% hkdfToSliceName + 188)
  x0_eq    : s.readReg64 .x0 = hsp s₀ + 208#64
  x1_eq    : s.readReg64 .x1 = ikmA
  x2_eq    : s.readReg64 .x2 = BitVec.ofNat 64 ikm.length
  x19_eq   : s.readReg64 .x19 = hsp s₀ + 208#64
  x21_eq   : s.readReg64 .x21 = 0#64
  x22_eq   : s.readReg64 .x22 = okmA
  x24_eq   : s.readReg64 .x24 = BitVec.ofNat 64 ikm.length
  x25_eq   : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq   : s.readReg64 .x27 = infoA
  m16_eq   : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  hmac_208 : HmacSt s.mem (hsp s₀ + 208#64) F (effectiveHmacKey F salt) []

private theorem seg_e1_lt56_pre {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hikm : ikm.length < 64)
    (hx : StateERet1Ext b roRegs F salt ikm info ikmA infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateE1Lt64Memcpy b roRegs F salt ikm info ikmA infoA okmA okmLen s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.common.status
  have hsp_eq := hx.common.sp_eq; have hx29 := hx.common.x29_eq
  have hx22 := hx.x22_eq; have hx23 := hx.x23_eq; have hx24 := hx.x24_eq
  have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  have htag := hx.tag_32; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.common.frame
  have hpos : s.mem.read8 (hsp s₀ + 103#64) = 0#8 := by
    have heq : hsp s₀ + 103#64 = (hsp s₀ + 40#64) + 0x3f#64 := by bv_lin
    rw [heq]; exact hx.hmac_40.2.2.1
  rcases Expand.cmp_lt64_lemmas hikm with ⟨h_ikm_ule, h_ikm_ult, h_ikm_cmp⟩
  iterate 29 kdf_step
  refine RunsTo.refl ?_
  refine ⟨by kdf_reg,
    HCommonExt.of_agreesOutside_hsp (off := 16#64) (sz := 336) hx.common
      (by kdf_reg) (by kdf_reg) (by kdf_reg) (by prove_agrees_hsp) (by decide),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by simp (config := { decide := true }) only [Expand.mem_setMem, arm64_norm],
    ?_⟩
  simp only [Expand.mem_setMem]
  refine HmacSt.of_copy_empty hx.hmac_40 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := { decide := true }) only [arm64_norm]

private theorem seg_e1_lt56_post {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s₁ s₂ : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hikm : ikm.length < 64)
    (hx : StateE1Lt64Memcpy b roRegs F salt ikm info ikmA infoA okmA okmLen s₀ s₁)
    (hpc : s₂.pc = b + bv% (ls_off% hkdfToSliceName + 188)) (hrun : s₂.status = .Running)
    (hcc : CallingConventionPreserved s₁ s₂)
    (hread_ikm : s₂.mem.readBytes (hsp s₀ + 208#64) ikm.length = ikm)
    (hfr : S2FrameRO roRegs s₁.mem s₂.mem
      [(hsp s₀ + 208#64, ikm.length), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    RunsTo (tripleRatchetProgAtExt b ext) s₂
      (StateE3ccExt b roRegs F salt ikm info infoA okmA okmLen s₀) := by
  have hc2 : HCommonExt roRegs okmLen s₀ s₂ :=
    HCommonExt.of_s2FrameRO_hsp (dstOff := 208#64) (dstLen := ikm.length) (stkLen := extHookStack)
      hpre hx.common hrun hcc hfr (by bv_omega) (by decide)
  have hsp_eq := hc2.sp_eq; have hx29 := hc2.x29_eq
  have hx19 : s₂.readReg64 .x19 = hsp s₀ + 208#64 := (cc_x19 hcc).trans hx.x19_eq
  have hx21 : s₂.readReg64 .x21 = 0#64 := (cc_x21 hcc).trans hx.x21_eq
  have hx22 : s₂.readReg64 .x22 = okmA := (cc_x22 hcc).trans hx.x22_eq
  have hx24 : s₂.readReg64 .x24 = BitVec.ofNat 64 ikm.length := (cc_x24 hcc).trans hx.x24_eq
  have hx25 : s₂.readReg64 .x25 = BitVec.ofNat 64 info.length := (cc_x25 hcc).trans hx.x25_eq
  have hx26 : s₂.readReg64 .x26 = BitVec.ofNat 64 okmLen := (cc_x26 hcc).trans hx.x26_eq
  have hx27 : s₂.readReg64 .x27 = infoA := (cc_x27 hcc).trans hx.x27_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw1 : s₁.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.common.frame
  have hrw2 : s₂.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hc2.frame
  have hm16_2 : s₂.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    refine (hfr.read64_eq_of_readable (hrw1.sub (by bv_omega)).readable fun r hr => ?_).trans hx.m16_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (dsimp [extHookStack]; unfold DisjointRegions; bv_omega)
  iterate 3 kdf_step
  refine RunsTo.refl ?_
  have hA : AgreesOutside s₂.mem
      (s₂.mem.write8 (hsp s₀ + 271#64) (BitVec.ofNat 8 ikm.length)) (hsp s₀ + 271#64) 1 :=
    agreesOutside_hsp_write8 (AgreesOutside.rfl' s₂.mem (hsp s₀ + 271#64) 1) (by decide)
  refine ⟨by kdf_reg,
    HCommonExt.of_agreesOutside_hsp (off := 271#64) (sz := 1) hc2
      (by kdf_reg) (by kdf_reg) (by kdf_reg) (by prove_agrees_hsp) (by decide),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [Expand.mem_setMem, hA.read64_eq (by unfold DisjointRegions; bv_omega)]; exact hm16_2,
    ?_⟩
  rw [Expand.mem_setMem]
  refine ⟨[], ikm, rfl, by decide, hikm, ?_⟩
  rcases hx.hmac_208 with ⟨_, _, _, hin, hcnt1, hout, hcnt2⟩
  refine ⟨by decide, hikm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases h0 : ikm.length = 0
    · have hnil : ikm = [] := List.eq_nil_of_length_eq_zero h0
      subst hnil; rfl
    · rw [hA.readBytes_eq (by unfold DisjointRegions; bv_omega) (by omega)]
      exact hread_ikm
  · rw [show (hsp s₀ + 208#64) + 0x3f#64 = hsp s₀ + 271#64 by bv_lin]
    exact Memory.read8_write8_same _ _ _
  · rw [hA.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        show (hsp s₀ + 208#64) + 0x40#64 = hsp s₀ + 272#64 by bv_lin]
    rw [show (hsp s₀ + 208#64) + 0x40#64 = hsp s₀ + 272#64 by bv_lin] at hin
    exact (hfr.readBytes_eq (hrw1.sub (by bv_omega)).readable
      (s2Frame_disj_208_hi hikm (by decide)) (by decide)).trans hin
  · rw [hA.read64_eq (by unfold DisjointRegions; bv_omega),
        show (hsp s₀ + 208#64) + 0x60#64 = hsp s₀ + 304#64 by bv_lin]
    rw [show (hsp s₀ + 208#64) + 0x60#64 = hsp s₀ + 304#64 by bv_lin] at hcnt1
    exact (hfr.read64_eq_of_readable (hrw1.sub (by bv_omega)).readable
      (s2Frame_disj_208_hi hikm (by decide))).trans hcnt1
  · rw [hA.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        show (hsp s₀ + 208#64) + 0x68#64 = hsp s₀ + 312#64 by bv_lin]
    rw [show (hsp s₀ + 208#64) + 0x68#64 = hsp s₀ + 312#64 by bv_lin] at hout
    exact (hfr.readBytes_eq (hrw1.sub (by bv_omega)).readable
      (s2Frame_disj_208_hi hikm (by decide)) (by decide)).trans hout
  · rw [hA.read64_eq (by unfold DisjointRegions; bv_omega),
        show (hsp s₀ + 208#64) + 0x88#64 = hsp s₀ + 344#64 by bv_lin]
    rw [show (hsp s₀ + 208#64) + 0x88#64 = hsp s₀ + 344#64 by bv_lin] at hcnt2
    exact (hfr.read64_eq_of_readable (hrw1.sub (by bv_omega)).readable
      (s2Frame_disj_208_hi hikm (by decide))).trans hcnt2

theorem seg_e1_lt56_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hikm : ikm.length < 64)
    (hx : StateERet1Ext img.base roRegs F salt ikm info ikmA infoA okmA okmLen s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateE3ccExt img.base roRegs F salt ikm info infoA okmA okmLen s₀) := by
  refine RunsTo.trans_toE_inv hfrz hsym (seg_e1_lt56_pre hpre hikm hx) fun s₁ hf₁ hs₁ hx₁ => ?_
  have hx2_nat : (s₁.readReg64 .x2).toNat = ikm.length := by
    rw [hx₁.x2_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hikm_inv := HFrameExt.ikm_inv hpre hx₁.common.frame
  have hsrc_perm : if ikmRO then s₁.mem.Readable ikmA ikm.length ∧
      (∀ a, InRegion ikmA ikm.length a → ∃ r ∈ roRegs, InRegion r.1 r.2 a)
    else RW s₁.mem ikmA ikm.length := by
    cases hir : ikmRO
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hp := hikm_inv.perm_inv; rw [hir] at hp
      simp only [Bool.false_eq_true, ↓reduceIte] at hp; exact hp.1
    · simp only [↓reduceIte]
      have hp := hikm_inv.perm_inv; rw [hir] at hp; simp only [↓reduceIte] at hp
      exact ⟨hikm_inv.readable, hp⟩
  have hmc := memcpy_any_subroutine_runsTo hs.hooks ikmRO roRegs hf₁ hs₁
    hx₁.pc_eq hx₁.common.status hx₁.x0_eq hx₁.x1_eq hx2_nat
    hikm_inv.bytes_eq
    ((HFrameExt.rw_hsp hpre hx₁.common.frame).sub (by bv_omega))
    hsrc_perm
    (by rw [hx₁.common.sp_eq]; exact HFrameExt.rw_ext_stk hpre hx₁.common.frame)
    (Or.inr (by rw [hx₁.common.sp_eq]; dsimp [extHookStack]; unfold DisjointRegions; bv_omega))
    (fun a ha => by have hout := hikm_inv.out_stk a ha; unfold OutsideRegion at hout ⊢; bv_omega)
    (fun a ha => by
      rw [hx₁.common.sp_eq]
      have hout := hikm_inv.out_stk a ha
      dsimp [extHookStack]; unfold OutsideRegion at hout ⊢; bv_omega)
    (by rw [hx₁.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).1)
  refine hmc.trans fun s₂ ⟨hpc₂, hrun₂, hcc₂, _, hread₂, _, hfr₂⟩ => ?_
  rw [hx₁.lr_eq] at hpc₂; rw [hx₁.common.sp_eq] at hfr₂
  exact runsTo_toE (seg_e1_lt56_post hpre hikm hx₁ hpc₂ hrun₂ hcc₂ hread₂ hfr₂)

private structure StateE1Eq64Comp (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (ikmA infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "sha2::sha256::compress256")
  common  : HCommonExt roRegs okmLen s₀ s
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% hkdfToSliceName + 304)
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 272#64
  x1_eq   : s.readReg64 .x1 = ikmA
  x2_eq   : s.readReg64 .x2 = BitVec.ofNat 64 ikm.length >>> 6
  x19_eq  : s.readReg64 .x19 = hsp s₀ + 208#64
  x20_eq  : s.readReg64 .x20 = BitVec.ofNat 64 ikm.length &&& 9223372036854775744#64
  x22_eq  : s.readReg64 .x22 = okmA
  x23_eq  : s.readReg64 .x23 = ikmA
  x24_eq  : s.readReg64 .x24 = BitVec.ofNat 64 ikm.length &&& 63#64
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq  : s.readReg64 .x27 = infoA
  m16_eq  : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  ist_272 : s.mem.readBytes (hsp s₀ + 272#64) 32 =
              shaStateBytes (hmacInnerInit F (effectiveHmacKey F salt))
  cnt_304 : s.mem.read64 (hsp s₀ + 304#64) = 1#64 + (BitVec.ofNat 64 ikm.length >>> 6)
  ost_312 : s.mem.readBytes (hsp s₀ + 312#64) 32 =
              shaStateBytes (hmacOuterInit F (effectiveHmacKey F salt))
  cnt_344 : s.mem.read64 (hsp s₀ + 344#64) = 1#64

private theorem seg_e1_eq64_pre {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hikm : 64 ≤ ikm.length)
    (hx : StateERet1Ext b roRegs F salt ikm info ikmA infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateE1Eq64Comp b roRegs F salt ikm info ikmA infoA okmA okmLen s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.common.status
  have hsp_eq := hx.common.sp_eq; have hx29 := hx.common.x29_eq
  have hx22 := hx.x22_eq; have hx23 := hx.x23_eq; have hx24 := hx.x24_eq
  have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  have htag := hx.tag_32; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.common.frame
  have hpos : s.mem.read8 (hsp s₀ + 103#64) = 0#8 := by
    rw [show hsp s₀ + 103#64 = (hsp s₀ + 40#64) + 0x3f#64 by bv_lin]; exact hx.hmac_40.2.2.1
  have hcnt_136 : s.mem.read64 (hsp s₀ + 136#64) = 1#64 := by
    rw [show hsp s₀ + 136#64 = (hsp s₀ + 40#64) + 0x60#64 by bv_lin]; exact hx.hmac_40.2.2.2.2.1
  rcases cmp_ge64_lemmas hikm hpre.ikm_len with ⟨h_ikm_ule, h_ikm_ult, h_ikm_cmp, h_ikm_cbz⟩
  iterate 35 kdf_step
  refine RunsTo.refl ⟨by kdf_reg,
    HCommonExt.of_agreesOutside_hsp (off := 16#64) (sz := 336) hx.common
      (by kdf_reg) (by kdf_reg) (by kdf_reg) (by prove_agrees_hsp) (by decide),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg,
    by simp (config := { decide := true }) only [Expand.mem_setMem, arm64_norm],
    ?_,
    by simp (config := { decide := true }) only [Expand.mem_setMem, arm64_norm],
    ?_, ?_⟩
  · simp only [Expand.mem_setMem]
    have h40 : s.mem.readBytes (hsp s₀ + 104#64) 32 =
        shaStateBytes (hmacInnerInit F (effectiveHmacKey F salt)) := by
      rw [show hsp s₀ + 104#64 = (hsp s₀ + 40#64) + 0x40#64 by bv_lin]; exact hx.hmac_40.2.2.2.1
    rw [readBytes_32_eq_of_read64_eq (m₂ := s.mem) (a₁ := hsp s₀ + 272#64) (a₂ := hsp s₀ + 104#64)
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm]), h40]
  · simp only [Expand.mem_setMem]
    rw [readBytes_32_eq_of_read64_eq (m₂ := s.mem) (a₁ := hsp s₀ + 312#64) (a₂ := (hsp s₀ + 40#64) + 0x68#64)
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])]
    exact hx.hmac_40.2.2.2.2.2.1
  · simp (config := { decide := true }) only [Expand.mem_setMem, arm64_norm]
    rw [show hsp s₀ + 176#64 = (hsp s₀ + 40#64) + 0x88#64 by bv_lin]
    exact hx.hmac_40.2.2.2.2.2.2

private structure StateE1Eq64Memcpy (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info pfx : List (BitVec 8)) (ikmA infoA okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "memcpy")
  common  : HCommonExt roRegs okmLen s₀ s
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% hkdfToSliceName + 324)
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 208#64
  x1_eq   : s.readReg64 .x1 = ikmA + (BitVec.ofNat 64 ikm.length &&& 9223372036854775744#64)
  x2_eq   : s.readReg64 .x2 = BitVec.ofNat 64 ikm.length &&& 63#64
  x19_eq  : s.readReg64 .x19 = hsp s₀ + 208#64
  x22_eq  : s.readReg64 .x22 = okmA
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 okmLen
  x27_eq  : s.readReg64 .x27 = infoA
  m16_eq  : s.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length
  pos_271 : s.mem.read8 (hsp s₀ + 271#64) = BitVec.truncate 8 (BitVec.ofNat 64 ikm.length &&& 63#64)
  ist_272 : s.mem.readBytes (hsp s₀ + 272#64) 32 =
              shaStateBytes ((chunks64 pfx).foldl F (hmacInnerInit F (effectiveHmacKey F salt)))
  cnt_304 : s.mem.read64 (hsp s₀ + 304#64) = 1#64 + (BitVec.ofNat 64 ikm.length >>> 6)
  ost_312 : s.mem.readBytes (hsp s₀ + 312#64) 32 =
              shaStateBytes (hmacOuterInit F (effectiveHmacKey F salt))
  cnt_344 : s.mem.read64 (hsp s₀ + 344#64) = 1#64

private theorem seg_e1_eq64_mid {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info pfx : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s₁ s₂ : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateE1Eq64Comp b roRegs F salt ikm info ikmA infoA okmA okmLen s₀ s₁)
    (hpc : s₂.pc = b + bv% (ls_off% hkdfToSliceName + 304)) (hrun : s₂.status = .Running)
    (hcc : CallingConventionPreserved s₁ s₂)
    (hist : s₂.mem.readBytes (hsp s₀ + 272#64) 32 =
      shaStateBytes ((chunks64 pfx).foldl F (hmacInnerInit F (effectiveHmacKey F salt))))
    (hfr : S2Frame s₁.mem s₂.mem
      [(hsp s₀ + 272#64, 32), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    RunsTo (tripleRatchetProgAtExt b ext) s₂
      (StateE1Eq64Memcpy b roRegs F salt ikm info pfx ikmA infoA okmA okmLen s₀) := by
  have hc2 : HCommonExt roRegs okmLen s₀ s₂ :=
    HCommonExt.of_s2Frame_hsp (dstOff := 272#64) (dstLen := 32) (stkLen := extHookStack)
      hpre hx.common hrun hcc hfr (by decide) (by decide)
  have hsp_eq := hc2.sp_eq; have hx29 := hc2.x29_eq
  have hx19 : s₂.readReg64 .x19 = hsp s₀ + 208#64 := (cc_x19 hcc).trans hx.x19_eq
  have hx20 : s₂.readReg64 .x20 = BitVec.ofNat 64 ikm.length &&& 9223372036854775744#64 :=
    (cc_x20 hcc).trans hx.x20_eq
  have hx22 : s₂.readReg64 .x22 = okmA := (cc_x22 hcc).trans hx.x22_eq
  have hx23 : s₂.readReg64 .x23 = ikmA := (cc_x23 hcc).trans hx.x23_eq
  have hx24 : s₂.readReg64 .x24 = BitVec.ofNat 64 ikm.length &&& 63#64 := (cc_x24 hcc).trans hx.x24_eq
  have hx25 : s₂.readReg64 .x25 = BitVec.ofNat 64 info.length := (cc_x25 hcc).trans hx.x25_eq
  have hx26 : s₂.readReg64 .x26 = BitVec.ofNat 64 okmLen := (cc_x26 hcc).trans hx.x26_eq
  have hx27 : s₂.readReg64 .x27 = infoA := (cc_x27 hcc).trans hx.x27_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw1 : s₁.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.common.frame
  have hrw2 : s₂.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hc2.frame
  have hm16_2 : s₂.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    refine (hfr.read64_eq (hrw1.sub (by bv_omega)) fun r hr => ?_).trans hx.m16_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (dsimp [extHookStack]; unfold DisjointRegions; bv_omega)
  have hcnt304_2 : s₂.mem.read64 (hsp s₀ + 304#64) = 1#64 + (BitVec.ofNat 64 ikm.length >>> 6) := by
    refine (hfr.read64_eq (hrw1.sub (by bv_omega)) fun r hr => ?_).trans hx.cnt_304
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (dsimp [extHookStack]; unfold DisjointRegions; bv_omega)
  have host312_2 : s₂.mem.readBytes (hsp s₀ + 312#64) 32 =
      shaStateBytes (hmacOuterInit F (effectiveHmacKey F salt)) := by
    refine (hfr.readBytes_eq (hrw1.sub (by bv_omega)) (fun r hr => ?_) (by decide)).trans hx.ost_312
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (dsimp [extHookStack]; unfold DisjointRegions; bv_omega)
  have hcnt344_2 : s₂.mem.read64 (hsp s₀ + 344#64) = 1#64 := by
    refine (hfr.read64_eq (hrw1.sub (by bv_omega)) fun r hr => ?_).trans hx.cnt_344
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (dsimp [extHookStack]; unfold DisjointRegions; bv_omega)
  iterate 5 kdf_step
  have hA : AgreesOutside s₂.mem
      (s₂.mem.write8 (hsp s₀ + 271#64) (BitVec.truncate 8 (BitVec.ofNat 64 ikm.length &&& 63#64)))
      (hsp s₀ + 271#64) 1 :=
    agreesOutside_hsp_write8 (AgreesOutside.rfl' s₂.mem (hsp s₀ + 271#64) 1) (by decide)
  refine RunsTo.refl ⟨by kdf_reg,
    HCommonExt.of_agreesOutside_hsp (off := 271#64) (sz := 1) hc2
      (by kdf_reg) (by kdf_reg) (by kdf_reg) (by prove_agrees_hsp) (by decide),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [Expand.mem_setMem, hA.read64_eq (by unfold DisjointRegions; bv_omega)]; exact hm16_2,
    by rw [Expand.mem_setMem]; exact Memory.read8_write8_same _ _ _,
    by rw [Expand.mem_setMem, hA.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)]; exact hist,
    by rw [Expand.mem_setMem, hA.read64_eq (by unfold DisjointRegions; bv_omega)]; exact hcnt304_2,
    by rw [Expand.mem_setMem, hA.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)]; exact host312_2,
    by rw [Expand.mem_setMem, hA.read64_eq (by unfold DisjointRegions; bv_omega)]; exact hcnt344_2⟩

private theorem seg_e1_eq64_post {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info pfx tail : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s₃ s₄ : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hpfx_tail : pfx ++ tail = ikm)
    (hpfx_len : pfx.length = 64 * (ikm.length / 64))
    (htail_len : tail.length = ikm.length - 64 * (ikm.length / 64))
    (htail_lt : tail.length < 64)
    (hx : StateE1Eq64Memcpy b roRegs F salt ikm info pfx ikmA infoA okmA okmLen s₀ s₃)
    (hpc : s₄.pc = b + bv% (ls_off% hkdfToSliceName + 324)) (hrun : s₄.status = .Running)
    (hcc : CallingConventionPreserved s₃ s₄)
    (hread_tail : s₄.mem.readBytes (hsp s₀ + 208#64) tail.length = tail)
    (hfr : S2Frame s₃.mem s₄.mem
      [(hsp s₀ + 208#64, tail.length), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    RunsTo (tripleRatchetProgAtExt b ext) s₄
      (StateE3ccExt b roRegs F salt ikm info infoA okmA okmLen s₀) := by
  have hc4 : HCommonExt roRegs okmLen s₀ s₄ :=
    HCommonExt.of_s2Frame_hsp (dstOff := 208#64) (dstLen := tail.length) (stkLen := extHookStack)
      hpre hx.common hrun hcc hfr (by bv_omega) (by decide)
  have hsp_eq := hc4.sp_eq; have hx29 := hc4.x29_eq
  have hx19 : s₄.readReg64 .x19 = hsp s₀ + 208#64 := (cc_x19 hcc).trans hx.x19_eq
  have hx22 : s₄.readReg64 .x22 = okmA := (cc_x22 hcc).trans hx.x22_eq
  have hx25 : s₄.readReg64 .x25 = BitVec.ofNat 64 info.length := (cc_x25 hcc).trans hx.x25_eq
  have hx26 : s₄.readReg64 .x26 = BitVec.ofNat 64 okmLen := (cc_x26 hcc).trans hx.x26_eq
  have hx27 : s₄.readReg64 .x27 = infoA := (cc_x27 hcc).trans hx.x27_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw3 : s₃.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.common.frame
  have hrw4 : s₄.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hc4.frame
  have hm16_4 : s₄.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    refine (hfr.read64_eq (hrw3.sub (by bv_omega)) fun r hr => ?_).trans hx.m16_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (dsimp [extHookStack]; unfold DisjointRegions; bv_omega)
  iterate 1 kdf_step
  rcases ikm_split_lemmas hpre.ikm_len with ⟨h_shr_nat, h_cnt_add, h_and_hi, h_and_lo_nat, h_and_lo_tr8⟩
  refine RunsTo.refl ⟨by kdf_reg,
    ⟨by kdf_reg, by kdf_reg, by kdf_reg,
     by simp only [arm64_norm]; exact hc4.saved,
     by simp only [arm64_norm]; exact hc4.frame⟩,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by simp only [arm64_norm]; exact hm16_4, ?_⟩
  simp only [arm64_norm]
  refine ⟨pfx, tail, hpfx_tail, by omega, htail_lt, by omega, htail_lt, hread_tail, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (hsp s₀ + 208#64) + 0x3f#64 = hsp s₀ + 271#64 by bv_lin]
    obtain ⟨hrw_271, hlf_271⟩ := Memory.permNoLazy_eq_some_rw_iff.mp
      (hrw3 (hsp s₀ + 271#64) (by simp only [InRegion]; bv_omega))
    have hr_271 : (s₃.mem.perm (hsp s₀ + 271#64)).r = true := by
      rw [hrw_271]; rfl
    have h271_eq : s₄.mem.read8 (hsp s₀ + 271#64) = s₃.mem.read8 (hsp s₀ + 271#64) := by
      refine hfr.1 _ hr_271 hlf_271 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (dsimp [extHookStack]; unfold OutsideRegion; bv_omega)
    rw [h271_eq, hx.pos_271, h_and_lo_tr8, ← htail_len]
  · rw [show (hsp s₀ + 208#64) + 0x40#64 = hsp s₀ + 272#64 by bv_lin]
    exact (hfr.readBytes_eq (hrw3.sub (by bv_omega))
      (s2Frame_disj_208_hi htail_lt (by decide)) (by decide)).trans hx.ist_272
  · rw [show (hsp s₀ + 208#64) + 0x60#64 = hsp s₀ + 304#64 by bv_lin]
    have h304_eq := hfr.read64_eq (a := hsp s₀ + 304#64) (hrw3.sub (by bv_omega))
      (s2Frame_disj_208_hi (off := 304#64) (sz := 8) htail_lt (by decide))
    have hpfx_div : pfx.length / 64 = ikm.length / 64 := by omega
    rw [h304_eq, hx.cnt_304, h_cnt_add, hpfx_div]
  · rw [show (hsp s₀ + 208#64) + 0x68#64 = hsp s₀ + 312#64 by bv_lin]
    exact (hfr.readBytes_eq (hrw3.sub (by bv_omega))
      (s2Frame_disj_208_hi htail_lt (by decide)) (by decide)).trans hx.ost_312
  · rw [show (hsp s₀ + 208#64) + 0x88#64 = hsp s₀ + 344#64 by bv_lin]
    exact (hfr.read64_eq (hrw3.sub (by bv_omega))
      (s2Frame_disj_208_hi htail_lt (by decide))).trans hx.cnt_344

theorem seg_e1_eq64_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hikm : 64 ≤ ikm.length)
    (hx : StateERet1Ext img.base roRegs F salt ikm info ikmA infoA okmA okmLen s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateE3ccExt img.base roRegs F salt ikm info infoA okmA okmLen s₀) := by
  refine RunsTo.trans_toE_inv hfrz hsym (seg_e1_eq64_pre hpre hikm hx) fun s₁ hf₁ hs₁ hx₁ => ?_
  let nBlocks := ikm.length / 64
  let pfx := ikm.take (64 * nBlocks)
  let tail := ikm.drop (64 * nBlocks)
  have hpfx_len : pfx.length = 64 * nBlocks := by dsimp [pfx, nBlocks]; rw [List.length_take]; omega
  have htail_len : tail.length = ikm.length - 64 * nBlocks := by dsimp [tail, nBlocks]; rw [List.length_drop]
  have htail_lt : tail.length < 64 := by rw [htail_len]; dsimp [nBlocks]; omega
  have hpfx_tail : pfx ++ tail = ikm := List.take_append_drop _ _
  rcases ikm_split_lemmas hpre.ikm_len with ⟨h_shr_nat, h_cnt_add, h_and_hi, h_and_lo_nat, h_and_lo_tr8⟩
  have hx2_comp : 64 * (s₁.readReg64 .x2).toNat = pfx.length := by rw [hx₁.x2_eq, h_shr_nat, hpfx_len]
  have hpfx_m1 : s₁.mem.readBytes ikmA pfx.length = pfx := by
    have hikm_all := HFrameExt.ikm_bytes hpre hx₁.common.frame
    have hslice := Bytes.readBytes_slice_of_readBytes_eq s₁.mem ikmA ikm hikm_all 0 (64 * nBlocks) (by omega)
    rw [hpfx_len]; simpa [pfx] using hslice
  have hrw_pfx : s₁.mem.RW ikmA pfx.length :=
    (HFrameExt.ikm_rw_ge64 hpre hx₁.common.frame hikm).sub (by have := hpre.ikm_len; bv_omega)
  have hd_ikm : DisjointRegions ikmA ikm.length (hsp s₀ - 16928#64) 17616 := by
    rcases hpre.disj_ikm_stk with h0 | hd; · omega
    · exact hd
  have hd_pfx : DisjointRegions ikmA pfx.length (hsp s₀ - 16928#64) 17616 :=
    hd_ikm.sub_left ikmA ⟨by omega, by have := hpre.ikm_len; bv_omega⟩
  have hd_st_blk : DisjointRegions (hsp s₀ + 272#64) 32 ikmA pfx.length :=
    (hd_pfx.sub_right (hsp s₀ + 272#64) ⟨by decide, by bv_omega⟩).symm
  have hd_blk_stk : DisjointRegions ikmA pfx.length (s₁.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hx₁.common.sp_eq]
    exact hd_pfx.sub_right (hsp s₀ - BitVec.ofNat 64 extHookStack)
      ⟨by decide, by dsimp [extHookStack]; bv_omega⟩
  have hcomp := compress256_subroutine_runsTo hs.hooks.compress256 (by decide) hf₁ hs₁
    hx₁.pc_eq hx₁.common.status hx₁.x0_eq hx₁.x1_eq hx2_comp
    (by have := hpre.ikm_len; omega) hx₁.ist_272 hpfx_m1
    ((HFrameExt.rw_hsp hpre hx₁.common.frame).sub (by bv_omega)) hrw_pfx
    (by rw [hx₁.common.sp_eq]; exact HFrameExt.rw_ext_stk hpre hx₁.common.frame)
    hd_st_blk
    (by rw [hx₁.common.sp_eq]; dsimp [extHookStack]; unfold DisjointRegions; bv_omega)
    hd_blk_stk
    (by rw [hx₁.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).1)
  refine RunsToE.trans_inv hf₁ hs₁ hcomp fun s₂ hf₂ hs₂ ⟨hpc₂, hrun₂, hcc₂, hist₂, _, hfr₂⟩ => ?_
  rw [hx₁.lr_eq] at hpc₂; rw [hx₁.common.sp_eq] at hfr₂
  refine RunsTo.trans_toE_inv hf₂ hs₂
    (seg_e1_eq64_mid hpre hx₁ hpc₂ hrun₂ hcc₂ hist₂ hfr₂) fun s₃ hf₃ hs₃ hx₃ => ?_
  have hx2_tail : (s₃.readReg64 .x2).toNat = tail.length := by
    rw [hx₃.x2_eq, h_and_lo_nat, htail_len]
  have htail_m3 : s₃.mem.readBytes
      (ikmA + (BitVec.ofNat 64 ikm.length &&& 9223372036854775744#64)) tail.length = tail := by
    have hikm_all := HFrameExt.ikm_bytes hpre hx₃.common.frame
    have hslice := Bytes.readBytes_slice_of_readBytes_eq s₃.mem ikmA ikm hikm_all
      (64 * nBlocks) tail.length (by omega)
    rw [h_and_hi]
    have htake : List.take tail.length (List.drop (64 * nBlocks) ikm) = tail := by
      dsimp [tail]; rw [List.take_length]
    simpa [nBlocks, htake] using hslice
  have hrw_tail : s₃.mem.RW
      (ikmA + (BitVec.ofNat 64 ikm.length &&& 9223372036854775744#64)) tail.length := by
    rw [h_and_hi]
    exact (HFrameExt.ikm_rw_ge64 hpre hx₃.common.frame hikm).sub (by have := hpre.ikm_len; bv_omega)
  have hd_dst_tail : tail.length = 0 ∨
      DisjointRegions (hsp s₀ + 208#64) tail.length
        (ikmA + (BitVec.ofNat 64 ikm.length &&& 9223372036854775744#64)) tail.length := by
    by_cases h0 : tail.length = 0
    · exact Or.inl h0
    · refine Or.inr ?_; rw [h_and_hi]
      exact ((hd_ikm.sub_left (ikmA + BitVec.ofNat 64 (64 * (ikm.length / 64)))
        ⟨by omega, by have := hpre.ikm_len; bv_omega⟩).sub_right (hsp s₀ + 208#64)
        ⟨by omega, by bv_omega⟩).symm
  have hd_tail_stk : tail.length = 0 ∨
      DisjointRegions (ikmA + (BitVec.ofNat 64 ikm.length &&& 9223372036854775744#64)) tail.length
        (s₃.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    by_cases h0 : tail.length = 0
    · exact Or.inl h0
    · refine Or.inr ?_; rw [h_and_hi, hx₃.common.sp_eq]
      exact (hd_ikm.sub_left (ikmA + BitVec.ofNat 64 (64 * (ikm.length / 64)))
        ⟨by omega, by have := hpre.ikm_len; bv_omega⟩).sub_right
        (hsp s₀ - BitVec.ofNat 64 extHookStack) ⟨by decide, by dsimp [extHookStack]; bv_omega⟩
  have hmc := memcpy_opt_subroutine_runsTo hs.hooks.memcpy hf₃ hs₃
    hx₃.pc_eq hx₃.common.status hx₃.x0_eq hx₃.x1_eq hx2_tail htail_m3
    ((HFrameExt.rw_hsp hpre hx₃.common.frame).sub (by bv_omega)) hrw_tail
    (by rw [hx₃.common.sp_eq]; exact HFrameExt.rw_ext_stk hpre hx₃.common.frame)
    hd_dst_tail
    (Or.inr (by rw [hx₃.common.sp_eq]; dsimp [extHookStack]; unfold DisjointRegions; bv_omega))
    hd_tail_stk
    (by rw [hx₃.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).1)
  refine hmc.trans fun s₄ ⟨hpc₄, hrun₄, hcc₄, _, hread₄, _, hfr₄⟩ => ?_
  rw [hx₃.lr_eq] at hpc₄; rw [hx₃.common.sp_eq] at hfr₄
  exact runsTo_toE (seg_e1_eq64_post hpre hpfx_tail hpfx_len htail_len htail_lt hx₃ hpc₄ hrun₄ hcc₄ hread₄ hfr₄)

/-- Combined segment `E1` (`img.base + hex:632cc` → `img.base + hex:633cc`) for arbitrary `ikm.length < 2 ^ 63`. -/
theorem seg_e1_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hx : StateERet1Ext img.base roRegs F salt ikm info ikmA infoA okmA okmLen s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateE3ccExt img.base roRegs F salt ikm info infoA okmA okmLen s₀) := by
  by_cases hikm : ikm.length < 64
  · exact seg_e1_lt56_runsTo_ext hs hfrz hsym hpre hikm hx
  · exact seg_e1_eq64_runsTo_ext hs hfrz hsym hpre (by omega) hx

end ExtractSegments

end CryptoVerification.SpqrV1.Kdf.HkdfToSliceExtProof
