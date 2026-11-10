/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpandExt
public import LibsignalBinary.Proofs.SpqrV1.Chain.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.HooksExt
import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth

/-!
# `spqr::kdf::hkdf_to_slice`: Contract-Backed Expand Loop and Top-Level `RunsToE`

Proves the `okmLen ∈ {64, 96}` HKDF-Expand loop (`0x636f0 → 0x639e4`) and top-level
`hkdf_to_slice_runsToE_ext` under `HkdfStubsExt` and `S2FrameRO` at stack budget
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

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame frame_of_agreesOutside)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.ChainProofs hiding hkdfToSliceName
open CryptoVerification.SpqrV1.Kdf CryptoVerification.SpqrV1.Kdf.SpqrKdfExt CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local simp, local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes Memory.read8_write64_base_off_disjoint Memory.read64_write8_base_off_disjoint
  extractLsb'_56_8_read64 State.readReg64_setMem State.pc_setMem State.sp_setMem State.status_setMem Expand.mem_setMem
  extractLsb'_0_64_zero128 extractLsb'_64_64_zero128 hsp_592_add_96_eq_sp read8_write64_264_271

@[local simp, local arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [(ls_off% hkdfToSliceName) → (ls_off% hkdfToSliceName + 1808)]

variable {img : Obj.Image} {b : BitVec 64} {F : ShaCompress} {ext : String → Option (State → State)}

/-! ## `okmLen = 32` Exit, Loop Entry (`hex:637b8`), & `HmacStN` Counter Helper -/

theorem b1_done_32_runsTo_ext {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)} {infoA okmA : BitVec 64} {s₀ s : State}
    (hx : StateB1DoneExt b roRegs F salt ikm info infoA okmA 32 s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateDoneExt b roRegs F salt ikm info okmA 32 s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status; have hsp_eq := hx.exp.common.sp_eq
  have hx29 := hx.exp.common.x29_eq; have hsaved := hx.exp.common.saved
  have hframe := hx.exp.common.frame; have hokm := hx.okm_32; have hx26 := hx.x26_eq
  kdf_step
  exact RunsTo.refl ⟨by kdf_reg, ⟨by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [State.mem_setPC]; exact hsaved, by rw [State.mem_setPC]; exact hframe⟩,
    by rw [State.mem_setPC, hkdfExpand_32_eq]; exact hokm⟩

structure StateLoopExt (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64)
    (tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% hkdfToSliceName + 1332)
  exp     : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  x12_eq  : s.readReg64 .x12 = 64#64
  x21_eq  : s.readReg64 .x21 = hsp s₀ + 352#64
  x22_eq  : s.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x27_eq  : s.readReg64 .x27 = BitVec.ofNat 64 i
  x28_eq  : s.readReg64 .x28 = hsp s₀ + 352#64
  t_508   : s.mem.readBytes (hsp s₀ + 508#64) 32 = tPrev
  okm_pre : s.mem.readBytes okmA dstOff = okmSoFar

theorem b1_to_loop_runsTo_ext {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)} {infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s : State} (hokm : okmLen = 64 ∨ okmLen = 96)
    (hx : StateB1DoneExt b roRegs F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopExt b roRegs F salt ikm info infoA okmA
        (Expand.t1 F (hkdfExtractBytes F salt ikm) info)
        (Expand.t1 F (hkdfExtractBytes F salt ikm) info)
        okmLen 1 (okmLen - 32) 32 s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status; have hsp_eq := hx.exp.common.sp_eq
  have hx29 := hx.exp.common.x29_eq; have hx22 := hx.x22_eq; have hx24 := hx.x24_eq
  have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx28 := hx.x28_eq
  have hne0 : (BitVec.ofNat 64 (okmLen - 32) == 0#64) = false := by
    rcases hokm with rfl | rfl <;> rfl
  iterate 6 kdf_step
  exact RunsTo.refl ⟨by kdf_reg,
    { common := ⟨by kdf_reg, by kdf_reg, by kdf_reg, hx.exp.common.saved, hx.exp.common.frame⟩
      m0_eq := hx.exp.m0_eq, m8_eq := hx.exp.m8_eq, m16_eq := hx.exp.m16_eq
      m24_eq := hx.exp.m24_eq, hmac_208 := hx.exp.hmac_208 },
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, hx.t1_508, hx.okm_32⟩

theorem HmacStN.of_s2Frame_tail_counter_352 {m₁ : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key blk tail0 : List (BitVec 8)}
    {c : BitVec 8} (hblk : blk.length = 64) (htail0 : tail0.length < 55)
    (htail_eq : m₁.readBytes (hsp s₀ + 352#64) tail0.length = tail0)
    (hin : m₁.readBytes (hsp s₀ + 416#64) 32 = shaStateBytes (F (hmacInnerInit F key) blk))
    (hcnt1 : m₁.read64 (hsp s₀ + 448#64) = 2#64)
    (hout : m₁.readBytes (hsp s₀ + 456#64) 32 = shaStateBytes (hmacOuterInit F key))
    (hcnt2 : m₁.read64 (hsp s₀ + 488#64) = 1#64) :
    let m₂ := (((m₁.write8 (hsp s₀ + 32#64) c).write8
      (hsp s₀ + 352#64 + BitVec.ofNat 64 tail0.length) c).write8
      (hsp s₀ + 415#64) (BitVec.ofNat 8 (tail0.length + 1)))
    HmacStN m₂ (hsp s₀ + 352#64) F key blk (tail0 ++ [c]) := by
  intro m₂
  have hlen : (tail0 ++ [c]).length = tail0.length + 1 := by simp
  refine HmacStN.mk_block64 hblk (by omega) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hlen, Bytes.readBytes_add m₂ (hsp s₀ + 352#64) tail0.length 1]
    have h_t0 : m₂.readBytes (hsp s₀ + 352#64) tail0.length = tail0 := by
      by_cases ht0 : tail0.length = 0
      · have hnil := List.eq_nil_of_length_eq_zero ht0; subst hnil; rfl
      · dsimp only [m₂]
        rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
              (by unfold DisjointRegions; bv_omega) (by omega),
            (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 tail0.length) 1 |>.write8 (by simp [InRegion])).readBytes_eq
              (by unfold DisjointRegions; bv_omega) (by omega),
            (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
              (by unfold DisjointRegions; bv_omega) (by omega)]
        exact htail_eq
    have h_c : m₂.readBytes (hsp s₀ + 352#64 + BitVec.ofNat 64 tail0.length) 1 = [c] := by
      dsimp only [Memory.readBytes, m₂]
      rw [Memory.read8_write8_ne (by bv_omega), Memory.read8_write8_same]
    rw [h_t0, h_c]
  · rw [hlen, show hsp s₀ + 352#64 + 0x3f#64 = hsp s₀ + 415#64 by bv_omega]
    exact Memory.read8_write8_same _ _ _
  · rw [show hsp s₀ + 352#64 + 0x40#64 = hsp s₀ + 416#64 by bv_omega]; dsimp only [m₂]
    rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 tail0.length) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide), hin]
  · rw [show hsp s₀ + 352#64 + 0x60#64 = hsp s₀ + 448#64 by bv_omega]; dsimp only [m₂]
    rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).read64_eq (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 tail0.length) 1 |>.write8 (by simp [InRegion])).read64_eq (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).read64_eq (by unfold DisjointRegions; bv_omega), hcnt1]
  · rw [show hsp s₀ + 352#64 + 0x68#64 = hsp s₀ + 456#64 by bv_omega]; dsimp only [m₂]
    rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 tail0.length) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide), hout]
  · rw [show hsp s₀ + 352#64 + 0x88#64 = hsp s₀ + 488#64 by bv_omega]; dsimp only [m₂]
    rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).read64_eq (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 tail0.length) 1 |>.write8 (by simp [InRegion])).read64_eq (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).read64_eq (by unfold DisjointRegions; bv_omega), hcnt2]

/-! ## Expand Loop (`hex:637b8 → hex:637b4`) for `okmLen ∈ {64, 96}` -/

structure StateLoopA1Ext (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64)
    (tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ)
    (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + bv% (ls_off% "memcpy")
  exp      : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  lr_eq    : s.readReg64 .lr = b + bv% (ls_off% hkdfToSliceName + 1516)
  x0_eq    : s.readReg64 .x0 = hsp s₀ + 384#64
  x1_eq    : s.readReg64 .x1 = infoA
  x2_eq    : s.readReg64 .x2 = 32#64
  x19_eq   : s.readReg64 .x19 = hsp s₀ + 352#64
  x20_eq   : s.readReg64 .x20 = BitVec.ofNat 64 info.length
  x21_eq   : s.readReg64 .x21 = BitVec.ofNat 64 (info.length - 32)
  x22_eq   : s.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff
  x23_eq   : s.readReg64 .x23 = hsp s₀ + 352#64
  x24_eq   : s.readReg64 .x24 = 32#64
  x25_eq   : s.readReg64 .x25 = infoA + 32#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x27_eq   : s.readReg64 .x27 = BitVec.ofNat 64 i
  x28_eq   : s.readReg64 .x28 = 32#64
  hmac_352 : HmacSt s.mem (hsp s₀ + 352#64) F (hkdfExtractBytes F salt ikm) tPrev
  okm_pre  : s.mem.readBytes okmA dstOff = okmSoFar

private theorem agreesOutside_stk_okm_pre {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA off : BitVec 64} {okmLen dstOff sz : ℕ} {s₀ : State} {m₁ m₂ : Memory}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hdst : dstOff ≤ okmLen) (hokm : m₁.readBytes okmA dstOff = okmSoFar)
    (hA : AgreesOutside m₁ m₂ (hsp s₀ + off) sz)
    (hoff : decide (0 < sz ∧ off.toNat + sz ≤ 592) = true) :
    m₂.readBytes okmA dstOff = okmSoFar := by
  by_cases h0 : dstOff = 0
  · subst h0; exact hokm
  · have ⟨hsz, hle⟩ := of_decide_eq_true hoff
    have hd : DisjointRegions (hsp s₀ + off) sz okmA dstOff :=
      (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + off) ⟨hsz, by bv_omega⟩).sub_right
        okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
    exact (hA.readBytes_eq hd (by have := hpre.okm_len; omega)).trans hokm

private theorem s2FrameRO_stk_okm_pre {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA off : BitVec 64} {okmLen dstOff sz : ℕ} {s₀ : State} {m₁ m₂ : Memory}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf : HFrameExt roRegs okmLen s₀ m₁) (hdst : dstOff ≤ okmLen)
    (hokm : m₁.readBytes okmA dstOff = okmSoFar)
    (hfr : S2FrameRO roRegs m₁ m₂ [(hsp s₀ + off, sz), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hoff : off.toNat + sz ≤ 592) :
    m₂.readBytes okmA dstOff = okmSoFar := by
  by_cases h0 : dstOff = 0
  · subst h0; exact hokm
  · refine (Memory.readBytes_congr_region (by have := hpre.okm_len; omega) fun a ha => ?_).trans hokm
    have ha_rd := (HFrameExt.rw_okm hpre hf).readable a
      (by simp only [InRegion] at ha ⊢; have := hpre.okm_len; bv_omega)
    refine hfr.1 a ha_rd.1 ha_rd.2 fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      (dsimp [extHookStack]; have := hpre.disj_okm_stk; have := hpre.okm_len
       unfold DisjointRegions InRegion OutsideRegion at *; bv_omega)

private theorem s2FrameRO_stk_read64 {roRegs : List (BitVec 64 × ℕ)} {s₀ : State} {m₁ m₂ : Memory}
    {dstOff off : BitVec 64} {dstLen : ℕ}
    (hrw : m₁.RW (hsp s₀) 688)
    (hfr : S2FrameRO roRegs m₁ m₂ [(hsp s₀ + dstOff, dstLen), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (h : (off.toNat + 8 ≤ dstOff.toNat ∨ dstOff.toNat + dstLen ≤ off.toNat) ∧ off.toNat + 8 ≤ 688)
    (hdst : dstOff.toNat + dstLen ≤ 688 ∧ dstOff.toNat ≠ off.toNat := by bv_omega) :
    m₂.read64 (hsp s₀ + off) = m₁.read64 (hsp s₀ + off) := by
  rcases h with ⟨_, _⟩; rcases hdst with ⟨_, _⟩
  refine hfr.read64_eq_of_readable (hrw.sub (by bv_omega)).readable fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> (dsimp [extHookStack]; unfold DisjointRegions; bv_omega)

private theorem s2FrameRO_stk_readBytes {roRegs : List (BitVec 64 × ℕ)} {s₀ : State} {m₁ m₂ : Memory}
    {dstOff off : BitVec 64} {dstLen sz : ℕ}
    (hrw : m₁.RW (hsp s₀) 688)
    (hfr : S2FrameRO roRegs m₁ m₂ [(hsp s₀ + dstOff, dstLen), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (h : 0 < sz ∧ (off.toNat + sz ≤ dstOff.toNat ∨ dstOff.toNat + dstLen ≤ off.toNat) ∧ off.toNat + sz ≤ 688)
    (hdst : dstOff.toNat + dstLen ≤ 688 ∧ dstOff.toNat ≠ off.toNat := by bv_omega) :
    m₂.readBytes (hsp s₀ + off) sz = m₁.readBytes (hsp s₀ + off) sz := by
  rcases h with ⟨_, _, _⟩; rcases hdst with ⟨_, _⟩
  refine hfr.readBytes_eq (hrw.sub (by bv_omega)).readable (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> (dsimp [extHookStack]; unfold DisjointRegions; bv_omega)

set_option maxHeartbeats 1600000 in
theorem iter_a1_runsTo_ext {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (ht_len : tPrev.length = 32) (hrem : rem = 32 ∨ rem = 64) (hdst : dstOff ≤ okmLen)
    (hx : StateLoopExt b roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopA1Ext b roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status
  have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hx12 := hx.x12_eq; have hx21 := hx.x21_eq; have hx22 := hx.x22_eq
  have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx27 := hx.x27_eq; have hx28 := hx.x28_eq
  have hm8 := hx.exp.m8_eq; have hm24 := hx.exp.m24_eq
  have hpos_208 : s.mem.read8 (hsp s₀ + 271#64) = 0#8 := by simpa [BitVec.add_assoc] using hx.exp.hmac_208.2.2.1
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.exp.common.frame
  rcases info_ge32_lemmas hpre.info_ge (by have := hpre.info_lt; omega) with
    ⟨hinfo_c, hinfo_ule, hinfo_ult, hinfo_sub1, hinfo_sub2⟩
  iterate 46 kdf_step
  refine RunsTo.refl ?_
  have hA : AgreesOutside s.mem
      (((((((((((((((((s.mem.write64 (hsp s₀ + 72#64) (s.mem.read64 (hsp s₀ + 312#64))).write64
        (hsp s₀ + 80#64) (s.mem.read64 (hsp s₀ + 320#64))).write64 (hsp s₀ + 88#64) (s.mem.read64 (hsp s₀ + 328#64))).write64
        (hsp s₀ + 96#64) (s.mem.read64 (hsp s₀ + 336#64))).write64 (hsp s₀ + 64#64) (s.mem.read64 (hsp s₀ + 304#64))).write64
        (hsp s₀ + 104#64) (s.mem.read64 (hsp s₀ + 344#64))).write64 (hsp s₀ + 32#64) (s.mem.read64 (hsp s₀ + 272#64))).write64
        (hsp s₀ + 40#64) (s.mem.read64 (hsp s₀ + 280#64))).write64 (hsp s₀ + 48#64) (s.mem.read64 (hsp s₀ + 288#64))).write64
        (hsp s₀ + 56#64) (s.mem.read64 (hsp s₀ + 296#64))).write64 (hsp s₀ + 416#64) (s.mem.read64 (hsp s₀ + 272#64))).write64
        (hsp s₀ + 424#64) (s.mem.read64 (hsp s₀ + 280#64))).write64 (hsp s₀ + 432#64) (s.mem.read64 (hsp s₀ + 288#64))).write64
        (hsp s₀ + 440#64) (s.mem.read64 (hsp s₀ + 296#64))).write64 (hsp s₀ + 448#64) (s.mem.read64 (hsp s₀ + 304#64))).write64
        (hsp s₀ + 456#64) (s.mem.read64 (hsp s₀ + 312#64))).write64 (hsp s₀ + 464#64) (s.mem.read64 (hsp s₀ + 320#64))
        |>.write64 (hsp s₀ + 472#64) (s.mem.read64 (hsp s₀ + 328#64)) |>.write64 (hsp s₀ + 384#64) (s.mem.read64 (hsp s₀ + 240#64))
        |>.write64 (hsp s₀ + 392#64) (s.mem.read64 (hsp s₀ + 248#64)) |>.write64 (hsp s₀ + 400#64) (s.mem.read64 (hsp s₀ + 256#64))
        |>.write64 (hsp s₀ + 408#64) (s.mem.read64 (hsp s₀ + 264#64)) |>.write64 (hsp s₀ + 480#64) (s.mem.read64 (hsp s₀ + 336#64))
        |>.write64 (hsp s₀ + 488#64) (s.mem.read64 (hsp s₀ + 344#64)) |>.write64 (hsp s₀ + 352#64) (s.mem.read64 (hsp s₀ + 208#64))
        |>.write64 (hsp s₀ + 360#64) (s.mem.read64 (hsp s₀ + 216#64)) |>.write64 (hsp s₀ + 368#64) (s.mem.read64 (hsp s₀ + 224#64))
        |>.write64 (hsp s₀ + 376#64) (s.mem.read64 (hsp s₀ + 232#64)) |>.write64 (hsp s₀ + 352#64) (s.mem.read64 (hsp s₀ + 508#64))
        |>.write64 (hsp s₀ + 360#64) (s.mem.read64 (hsp s₀ + 516#64)) |>.write64 (hsp s₀ + 368#64) (s.mem.read64 (hsp s₀ + 524#64))
        |>.write64 (hsp s₀ + 376#64) (s.mem.read64 (hsp s₀ + 532#64)) |>.write8 (hsp s₀ + 415#64) 32#8)
      (hsp s₀ + 32#64) 464 := by prove_agrees_hsp
  refine ⟨by kdf_reg,
    HExpCommonExt.of_agreesOutside_32_560 (off := 32#64) (sz := 464) hx.exp
      (by kdf_reg) (by kdf_reg) (by kdf_reg) hA (by decide) (by prove_hmac_208 hx.exp.hmac_208),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hinfo_sub1, hinfo_sub2],
    by kdf_reg, by kdf_reg,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm]; rcases hrem with rfl | rfl <;> rfl,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, ?_,
    agreesOutside_stk_okm_pre hpre hdst hx.okm_pre hA (by decide)⟩
  simp only [Expand.mem_setMem]
  refine HmacSt.of_copy_208_write32_352 hx.exp.hmac_208 hx.t_508 ht_len
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := { decide := true }) only [arm64_norm]

private structure StateLoopA2Comp (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64)
    (tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "sha2::sha256::compress256")
  exp     : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% hkdfToSliceName + 1544)
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 416#64
  x1_eq   : s.readReg64 .x1 = hsp s₀ + 352#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = hsp s₀ + 352#64
  x21_eq  : s.readReg64 .x21 = BitVec.ofNat 64 (info.length - 32)
  x22_eq  : s.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff
  x23_eq  : s.readReg64 .x23 = hsp s₀ + 352#64
  x24_eq  : s.readReg64 .x24 = 32#64
  x25_eq  : s.readReg64 .x25 = infoA + 32#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x27_eq  : s.readReg64 .x27 = BitVec.ofNat 64 i
  in_416  : s.mem.readBytes (hsp s₀ + 416#64) 32 = shaStateBytes (hmacInnerInit F (hkdfExtractBytes F salt ikm))
  blk_352 : s.mem.readBytes (hsp s₀ + 352#64) 64 = tPrev ++ info.take 32
  cnt_448 : s.mem.read64 (hsp s₀ + 448#64) = 2#64
  out_456 : s.mem.readBytes (hsp s₀ + 456#64) 32 = shaStateBytes (hmacOuterInit F (hkdfExtractBytes F salt ikm))
  cnt_488 : s.mem.read64 (hsp s₀ + 488#64) = 1#64
  okm_pre : s.mem.readBytes okmA dstOff = okmSoFar

private theorem iter_a2_mid_facts {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s s₁ : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (ht_len : tPrev.length = 32) (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA1Ext b roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s)
    (hdst₁ : s₁.mem.readBytes (hsp s₀ + 384#64) 32 = info.take 32)
    (hfr₁ : S2FrameRO roRegs s.mem s₁.mem [(hsp s₀ + 384#64, 32), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    let m₂ := s₁.mem.write64 (hsp s₀ + 448#64) 2#64
    s₁.mem.read64 (hsp s₀ + 448#64) = 1#64 ∧
    AgreesOutside s₁.mem m₂ (hsp s₀ + 448#64) 8 ∧
    m₂.readBytes (hsp s₀ + 416#64) 32 = shaStateBytes (hmacInnerInit F (hkdfExtractBytes F salt ikm)) ∧
    m₂.readBytes (hsp s₀ + 352#64) 64 = tPrev ++ info.take 32 ∧
    m₂.readBytes (hsp s₀ + 456#64) 32 = shaStateBytes (hmacOuterInit F (hkdfExtractBytes F salt ikm)) ∧
    m₂.read64 (hsp s₀ + 488#64) = 1#64 ∧
    m₂.readBytes okmA dstOff = okmSoFar := by
  intro m₂
  have hrw : s.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.exp.common.frame
  have hA2 : AgreesOutside s₁.mem m₂ (hsp s₀ + 448#64) 8 :=
    agreesOutside_hsp_write64 (AgreesOutside.rfl' s₁.mem (hsp s₀ + 448#64) 8) (by decide)
  refine ⟨?_, hA2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [s2FrameRO_stk_read64 hrw hfr₁ (by decide), show hsp s₀ + 448#64 = (hsp s₀ + 352#64) + 0x60#64 by bv_lin]
    exact hx.hmac_352.2.2.2.2.1
  · rw [hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        s2FrameRO_stk_readBytes hrw hfr₁ (by decide), show hsp s₀ + 416#64 = (hsp s₀ + 352#64) + 0x40#64 by bv_lin]
    exact hx.hmac_352.2.2.2.1
  · change m₂.readBytes (hsp s₀ + 352#64) (32 + 32) = tPrev ++ info.take 32
    have ht_m1 : s₁.mem.readBytes (hsp s₀ + 352#64) 32 = tPrev := by
      rw [s2FrameRO_stk_readBytes hrw hfr₁ (by decide), ← ht_len]; exact hx.hmac_352.2.1
    rw [Bytes.readBytes_add _ (hsp s₀ + 352#64) 32 32,
        show (hsp s₀ + 352#64) + BitVec.ofNat 64 32 = hsp s₀ + 384#64 by bv_lin,
        hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide), ht_m1, hdst₁]
  · rw [hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        s2FrameRO_stk_readBytes hrw hfr₁ (by decide), show hsp s₀ + 456#64 = (hsp s₀ + 352#64) + 0x68#64 by bv_lin]
    exact hx.hmac_352.2.2.2.2.2.1
  · rw [hA2.read64_eq (by unfold DisjointRegions; bv_omega),
        s2FrameRO_stk_read64 hrw hfr₁ (by decide), show hsp s₀ + 488#64 = (hsp s₀ + 352#64) + 0x88#64 by bv_lin]
    exact hx.hmac_352.2.2.2.2.2.2
  · exact agreesOutside_stk_okm_pre hpre hdst
      (s2FrameRO_stk_okm_pre hpre hx.exp.common.frame hdst hx.okm_pre hfr₁ (by decide)) hA2 (by decide)

private theorem iter_a2_mid {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s s₁ : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (ht_len : tPrev.length = 32) (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA1Ext b roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s)
    (hpc₁ : s₁.pc = b + bv% (ls_off% hkdfToSliceName + 1516)) (hrun₁ : s₁.status = .Running)
    (hcc₁ : CallingConventionPreserved s s₁)
    (hdst₁ : s₁.mem.readBytes (hsp s₀ + 384#64) 32 = info.take 32)
    (hfr₁ : S2FrameRO roRegs s.mem s₁.mem [(hsp s₀ + 384#64, 32), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    RunsTo (tripleRatchetProgAtExt b ext) s₁
      (StateLoopA2Comp b roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have hc1 : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s₁ :=
    HExpCommonExt.of_s2FrameRO_352_592 (dstOff := 384#64) (dstLen := 32)
      hpre hx.exp hrun₁ hcc₁ hfr₁ ⟨by decide, by decide, by decide⟩
  have hsp₁ := hc1.common.sp_eq; have hx29_1 := hc1.common.x29_eq
  have hx19_1 : s₁.readReg64 .x19 = hsp s₀ + 352#64 := (cc_x19 hcc₁).trans hx.x19_eq
  have hx21_1 : s₁.readReg64 .x21 = BitVec.ofNat 64 (info.length - 32) := (cc_x21 hcc₁).trans hx.x21_eq
  have hx22_1 : s₁.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff := (cc_x22 hcc₁).trans hx.x22_eq
  have hx23_1 : s₁.readReg64 .x23 = hsp s₀ + 352#64 := (cc_x23 hcc₁).trans hx.x23_eq
  have hx24_1 : s₁.readReg64 .x24 = 32#64 := (cc_x24 hcc₁).trans hx.x24_eq
  have hx25_1 : s₁.readReg64 .x25 = infoA + 32#64 := (cc_x25 hcc₁).trans hx.x25_eq
  have hx26_1 : s₁.readReg64 .x26 = BitVec.ofNat 64 rem := (cc_x26 hcc₁).trans hx.x26_eq
  have hx27_1 : s₁.readReg64 .x27 = BitVec.ofNat 64 i := (cc_x27 hcc₁).trans hx.x27_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw1 : s₁.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hc1.common.frame
  have hfacts := iter_a2_mid_facts hpre ht_len hdst hx hdst₁ hfr₁
  have hcnt1_m1 : s₁.mem.read64 (hsp s₀ + 448#64) = 1#64 := hfacts.1
  clear hx hcc₁ hdst₁ hfr₁
  iterate 7 kdf_step
  rcases hfacts with ⟨_, hA2, hin_m1, hblk_m1, hout_m1, hcnt2_m1, hokm_m1⟩
  refine RunsTo.refl ⟨by kdf_reg,
    HExpCommonExt.of_agreesOutside_352_592 (off := 448#64) (sz := 8) hc1
      (by kdf_reg) (by kdf_reg) (by kdf_reg) hA2 (by decide),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [Expand.mem_setMem]; exact hin_m1,
    by rw [Expand.mem_setMem]; exact hblk_m1,
    by simp (config := { decide := true }) only [Expand.mem_setMem, arm64_norm],
    by rw [Expand.mem_setMem]; exact hout_m1,
    by rw [Expand.mem_setMem]; exact hcnt2_m1,
    by rw [Expand.mem_setMem]; exact hokm_m1⟩

structure StateLoopA2Ext (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64)
    (tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% hkdfToSliceName + 1544)
  exp     : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  x19_eq  : s.readReg64 .x19 = hsp s₀ + 352#64
  x21_eq  : s.readReg64 .x21 = BitVec.ofNat 64 (info.length - 32)
  x22_eq  : s.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff
  x23_eq  : s.readReg64 .x23 = hsp s₀ + 352#64
  x24_eq  : s.readReg64 .x24 = 32#64
  x25_eq  : s.readReg64 .x25 = infoA + 32#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x27_eq  : s.readReg64 .x27 = BitVec.ofNat 64 i
  in_416  : s.mem.readBytes (hsp s₀ + 416#64) 32 =
              shaStateBytes (F (hmacInnerInit F (hkdfExtractBytes F salt ikm)) (tPrev ++ info.take 32))
  cnt_448 : s.mem.read64 (hsp s₀ + 448#64) = 2#64
  out_456 : s.mem.readBytes (hsp s₀ + 456#64) 32 =
              shaStateBytes (hmacOuterInit F (hkdfExtractBytes F salt ikm))
  cnt_488 : s.mem.read64 (hsp s₀ + 488#64) = 1#64
  okm_pre : s.mem.readBytes okmA dstOff = okmSoFar

theorem iter_a2_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (ht_len : tPrev.length = 32) (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA1Ext img.base roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateLoopA2Ext img.base roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have htake_len : (info.take 32).length = 32 := List.length_take_of_le hpre.info_ge
  have hx2_nat : (s.readReg64 .x2).toNat = (info.take 32).length := by rw [hx.x2_eq, htake_len]; rfl
  have hinfo_inv := HFrameExt.info_inv hpre hx.exp.common.frame
  have hinfo_take : s.mem.readBytes infoA (info.take 32).length = info.take 32 := by
    have h := Bytes.readBytes_slice_of_readBytes_eq s.mem infoA info hinfo_inv.bytes_eq 0 32 (by have := hpre.info_ge; omega)
    rw [htake_len]; simpa using h
  have hin_info : ∀ a, InRegion infoA (info.take 32).length a → InRegion infoA info.length a := by
    intro a ha; rw [htake_len] at ha
    simp only [InRegion] at ha ⊢; have := hpre.info_ge; have := hpre.info_lt; bv_omega
  have hsrc_perm : if infoRO then s.mem.Readable infoA (info.take 32).length ∧
      (∀ a, InRegion infoA (info.take 32).length a → ∃ r ∈ roRegs, InRegion r.1 r.2 a)
    else RW s.mem infoA (info.take 32).length := by
    cases hro : infoRO
    · have hp := hinfo_inv.perm_inv; rw [hro] at hp
      simp only [Bool.false_eq_true, ↓reduceIte] at hp ⊢
      exact fun a ha => hp.1 a (hin_info a ha)
    · have hp := hinfo_inv.perm_inv; rw [hro] at hp
      simp only [↓reduceIte] at hp ⊢
      exact ⟨fun a ha => hinfo_inv.readable a (hin_info a ha), fun a ha => hp a (hin_info a ha)⟩
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.exp.common.frame
  have hmc := memcpy_any_subroutine_runsTo hs.hooks infoRO roRegs hfrz hsym
    hx.pc_eq hx.exp.common.status hx.x0_eq hx.x1_eq hx2_nat hinfo_take
    (by rw [htake_len]; exact hrw_hsp.sub (by bv_omega))
    hsrc_perm
    (by rw [hx.exp.common.sp_eq]; exact HFrameExt.rw_ext_stk hpre hx.exp.common.frame)
    (by rw [hx.exp.common.sp_eq, htake_len]; exact Or.inr (by dsimp [extHookStack]; unfold DisjointRegions; bv_omega))
    (fun a ha => by
      have ho := hinfo_inv.out_stk a (hin_info a ha)
      rw [htake_len]; unfold OutsideRegion at ho ⊢; bv_omega)
    (fun a ha => by
      rw [hx.exp.common.sp_eq]
      have ho := hinfo_inv.out_stk a (hin_info a ha)
      dsimp [extHookStack]; unfold OutsideRegion at ho ⊢; bv_omega)
    (by rw [hx.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).1)
  refine RunsToE.trans_inv hfrz hsym hmc fun s₁ hf₁ hs₁ ⟨hpc₁, hrun₁, hcc₁, _, hdst₁, _, hfr₁⟩ => ?_
  rw [hx.lr_eq] at hpc₁; rw [htake_len] at hdst₁ hfr₁; rw [hx.exp.common.sp_eq] at hfr₁
  refine RunsTo.trans_toE_inv hf₁ hs₁
    (iter_a2_mid hpre ht_len hdst hx hpc₁ hrun₁ hcc₁ hdst₁ hfr₁) fun s₂ hf₂ hs₂ hx₂ => ?_
  have hrw2_hsp : s₂.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx₂.exp.common.frame
  have hcomp := compress256_one_subroutine_runsTo hs.hooks.compress256 (by decide) hf₂ hs₂
    hx₂.pc_eq hx₂.exp.common.status hx₂.x0_eq hx₂.x1_eq hx₂.x2_eq
    hx₂.in_416 hx₂.blk_352 (hrw2_hsp.sub (by bv_omega)) (hrw2_hsp.sub (by bv_omega))
    (by rw [hx₂.exp.common.sp_eq]; exact HFrameExt.rw_ext_stk hpre hx₂.exp.common.frame)
    (by unfold DisjointRegions; bv_omega)
    (by rw [hx₂.exp.common.sp_eq]; dsimp [extHookStack]; unfold DisjointRegions; bv_omega)
    (by rw [hx₂.exp.common.sp_eq]; dsimp [extHookStack]; unfold DisjointRegions; bv_omega)
    (by rw [hx₂.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).1)
  refine hcomp.mono fun s₃ ⟨hpc₃, hrun₃, hcc₃, hst₃, _, hfr₃⟩ => ?_
  rw [hx₂.lr_eq] at hpc₃; rw [hx₂.exp.common.sp_eq] at hfr₃
  have hfrRO₃ := S2FrameRO.of_s2frame (roRegs := roRegs) hfr₃
  have hc3 : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s₃ :=
    HExpCommonExt.of_s2Frame_352_592 (dstOff := 416#64) (dstLen := 32)
      hpre hx₂.exp hrun₃ hcc₃ hfr₃ ⟨by decide, by decide, by decide⟩
  exact ⟨hpc₃, hc3,
    (cc_x19 hcc₃).trans hx₂.x19_eq, (cc_x21 hcc₃).trans hx₂.x21_eq,
    (cc_x22 hcc₃).trans hx₂.x22_eq, (cc_x23 hcc₃).trans hx₂.x23_eq,
    (cc_x24 hcc₃).trans hx₂.x24_eq, (cc_x25 hcc₃).trans hx₂.x25_eq,
    (cc_x26 hcc₃).trans hx₂.x26_eq, (cc_x27 hcc₃).trans hx₂.x27_eq,
    hst₃,
    (s2FrameRO_stk_read64 hrw2_hsp hfrRO₃ (by decide)).trans hx₂.cnt_448,
    (s2FrameRO_stk_readBytes hrw2_hsp hfrRO₃ (by decide)).trans hx₂.out_456,
    (s2FrameRO_stk_read64 hrw2_hsp hfrRO₃ (by decide)).trans hx₂.cnt_488,
    s2FrameRO_stk_okm_pre hpre hx₂.exp.common.frame hdst hx₂.okm_pre hfrRO₃ (by decide)⟩

private structure StateLoopBMemcpy (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64)
    (tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "memcpy")
  exp     : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% hkdfToSliceName + 1612)
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 352#64
  x1_eq   : s.readReg64 .x1 = infoA + 32#64
  x2_eq   : s.readReg64 .x2 = BitVec.ofNat 64 (info.length - 32)
  x19_eq  : s.readReg64 .x19 = hsp s₀ + 352#64
  x22_eq  : s.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff
  x23_eq  : s.readReg64 .x23 = hsp s₀ + 352#64
  x24_eq  : s.readReg64 .x24 = 32#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x27_eq  : s.readReg64 .x27 = BitVec.ofNat 64 i
  x28_eq  : s.readReg64 .x28 = hsp s₀ + 352#64
  pos_415 : s.mem.read8 (hsp s₀ + 415#64) = BitVec.ofNat 8 (info.length - 32)
  in_416  : s.mem.readBytes (hsp s₀ + 416#64) 32 =
              shaStateBytes (F (hmacInnerInit F (hkdfExtractBytes F salt ikm)) (tPrev ++ info.take 32))
  cnt_448 : s.mem.read64 (hsp s₀ + 448#64) = 2#64
  out_456 : s.mem.readBytes (hsp s₀ + 456#64) 32 =
              shaStateBytes (hmacOuterInit F (hkdfExtractBytes F salt ikm))
  cnt_488 : s.mem.read64 (hsp s₀ + 488#64) = 1#64
  okm_pre : s.mem.readBytes okmA dstOff = okmSoFar

private theorem iter_b_pre_facts {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA2Ext b roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    let m₀ := (s.mem.write8 (hsp s₀ + 415#64) 0#8).write8 (hsp s₀ + 415#64) (BitVec.ofNat 8 (info.length - 32))
    AgreesOutside s.mem m₀ (hsp s₀ + 415#64) 1 ∧
    m₀.readBytes (hsp s₀ + 416#64) 32 = shaStateBytes (F (hmacInnerInit F (hkdfExtractBytes F salt ikm)) (tPrev ++ info.take 32)) ∧
    m₀.read64 (hsp s₀ + 448#64) = 2#64 ∧
    m₀.readBytes (hsp s₀ + 456#64) 32 = shaStateBytes (hmacOuterInit F (hkdfExtractBytes F salt ikm)) ∧
    m₀.read64 (hsp s₀ + 488#64) = 1#64 ∧
    m₀.readBytes okmA dstOff = okmSoFar := by
  intro m₀
  have hA0 : AgreesOutside s.mem m₀ (hsp s₀ + 415#64) 1 := by dsimp only [m₀]; prove_agrees_hsp
  refine ⟨hA0,
    (hA0.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans hx.in_416,
    (hA0.read64_eq (by unfold DisjointRegions; bv_omega)).trans hx.cnt_448,
    (hA0.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans hx.out_456,
    (hA0.read64_eq (by unfold DisjointRegions; bv_omega)).trans hx.cnt_488,
    agreesOutside_stk_okm_pre hpre hdst hx.okm_pre hA0 (by decide)⟩

private theorem iter_b_pre {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA2Ext b roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopBMemcpy b roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status; have hsp_eq := hx.exp.common.sp_eq
  have hx29 := hx.exp.common.x29_eq; have hx19 := hx.x19_eq; have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq; have hx23 := hx.x23_eq; have hx24 := hx.x24_eq
  have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.exp.common.frame
  have hk_lt : info.length - 32 < 23 := by have := hpre.info_lt; omega
  rcases info_sub32_lemmas (by omega : info.length - 32 < 64) with
    ⟨hlsr6_nat, hlsr6, hand_hi, hand_lo, hlsr6_nat_eq, hlsr6_eq⟩
  rcases Expand.cmp_lt64_lemmas (by omega : info.length - 32 < 64) with ⟨h_k_ule, h_k_ult, h_k_cmp⟩
  iterate 11 kdf_step
  rcases iter_b_pre_facts hpre hdst hx with ⟨hA0, hin_0, hcnt1_0, hout_0, hcnt2_0, hokm_0⟩
  refine RunsTo.refl ⟨by kdf_reg,
    HExpCommonExt.of_agreesOutside_352_592 (off := 415#64) (sz := 1) hx.exp
      (by kdf_reg) (by kdf_reg) (by kdf_reg) hA0 (by decide),
    by kdf_reg, by kdf_reg,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, BitVec.add_zero],
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [Expand.mem_setMem]; exact Memory.read8_write8_same _ _ _,
    by rw [Expand.mem_setMem]; exact hin_0,
    by rw [Expand.mem_setMem]; exact hcnt1_0,
    by rw [Expand.mem_setMem]; exact hout_0,
    by rw [Expand.mem_setMem]; exact hcnt2_0,
    by rw [Expand.mem_setMem]; exact hokm_0⟩

structure StateLoopCExt (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64)
    (tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% finalizeFixed3Name)
  exp     : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% hkdfToSliceName + 1280)
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 540#64
  x1_eq   : s.readReg64 .x1 = hsp s₀ + 32#64
  x20_eq  : s.readReg64 .x20 = okmA + BitVec.ofNat 64 (dstOff + 32)
  x21_eq  : s.readReg64 .x21 = hsp s₀ + 352#64
  x22_eq  : s.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff
  x24_eq  : s.readReg64 .x24 = 32#64
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 (rem - 32)
  x27_eq  : s.readReg64 .x27 = BitVec.ofNat 64 i
  x28_eq  : s.readReg64 .x28 = hsp s₀ + 352#64
  hmac_32 : HmacStN s.mem (hsp s₀ + 32#64) F (hkdfExtractBytes F salt ikm)
              (tPrev ++ info.take 32) (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre : s.mem.readBytes okmA dstOff = okmSoFar

private theorem iter_b_s2FrameRO_facts {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s₁ s₂ : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (ht_len : tPrev.length = 32) (hdst : dstOff ≤ okmLen)
    (hx : StateLoopBMemcpy b roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s₁)
    (hdst₂ : s₂.mem.readBytes (hsp s₀ + 352#64) (info.length - 32) = info.drop 32)
    (hfr₂ : S2FrameRO roRegs s₁.mem s₂.mem
      [(hsp s₀ + 352#64, info.length - 32), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    s₂.mem.read8 (hsp s₀ + 415#64) = BitVec.ofNat 8 (info.length - 32) ∧
    HmacStN
      ((((s₂.mem.write8 (hsp s₀ + 32#64) (BitVec.ofNat 8 (i + 1))).write8
        (hsp s₀ + 352#64 + BitVec.ofNat 64 (info.length - 32)) (BitVec.ofNat 8 (i + 1))).write8
        (hsp s₀ + 415#64) (BitVec.ofNat 8 (info.length - 32 + 1))))
      (hsp s₀ + 352#64) F (hkdfExtractBytes F salt ikm) (tPrev ++ info.take 32)
      (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) ∧
    s₂.mem.readBytes okmA dstOff = okmSoFar := by
  have hk_lt : info.length - 32 < 23 := by have := hpre.info_lt; omega
  have hrw1 : s₁.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.exp.common.frame
  refine ⟨?_, ?_, s2FrameRO_stk_okm_pre hpre hx.exp.common.frame hdst hx.okm_pre hfr₂ (by bv_omega)⟩
  · have h415_rd := hrw1.readable (hsp s₀ + 415#64) (by simp only [InRegion]; bv_omega)
    refine (hfr₂.1 _ h415_rd.1 h415_rd.2 fun r hr => ?_).trans hx.pos_415
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (dsimp [extHookStack]; unfold OutsideRegion; bv_omega)
  · have hdrop_len : (info.drop 32).length = info.length - 32 := by simp
    have htake_len : (info.take 32).length = 32 := List.length_take_of_le hpre.info_ge
    have hblk_len : (tPrev ++ info.take 32).length = 64 := by rw [List.length_append, ht_len, htake_len]
    have h := HmacStN.of_s2Frame_tail_counter_352 (c := BitVec.ofNat 8 (i + 1))
      hblk_len (by rw [hdrop_len]; omega : (info.drop 32).length < 55)
      (by simpa only [hdrop_len] using hdst₂)
      ((s2FrameRO_stk_readBytes hrw1 hfr₂ ⟨by decide, Or.inr (by bv_omega), by decide⟩).trans hx.in_416)
      ((s2FrameRO_stk_read64 hrw1 hfr₂ ⟨Or.inr (by bv_omega), by decide⟩).trans hx.cnt_448)
      ((s2FrameRO_stk_readBytes hrw1 hfr₂ ⟨by decide, Or.inr (by bv_omega), by decide⟩).trans hx.out_456)
      ((s2FrameRO_stk_read64 hrw1 hfr₂ ⟨Or.inr (by bv_omega), by decide⟩).trans hx.cnt_488)
    simpa only [hdrop_len] using h

set_option maxHeartbeats 1600000 in
private theorem iter_b_post {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s₁ s₂ : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (ht_len : tPrev.length = 32) (hi : i = 1 ∨ i = 2) (hrem : rem = 32 ∨ rem = 64)
    (hdst : dstOff + 32 ≤ okmLen)
    (hx : StateLoopBMemcpy b roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s₁)
    (hpc₂ : s₂.pc = b + bv% (ls_off% hkdfToSliceName + 1612)) (hrun₂ : s₂.status = .Running)
    (hcc₂ : CallingConventionPreserved s₁ s₂)
    (hdst₂ : s₂.mem.readBytes (hsp s₀ + 352#64) (info.length - 32) = info.drop 32)
    (hfr₂ : S2FrameRO roRegs s₁.mem s₂.mem
      [(hsp s₀ + 352#64, info.length - 32), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    RunsTo (tripleRatchetProgAtExt b ext) s₂
      (StateLoopCExt b roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have hk_lt : info.length - 32 < 23 := by have := hpre.info_lt; omega
  have hdst_le : dstOff ≤ okmLen := by omega
  have hc2 : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s₂ :=
    HExpCommonExt.of_s2FrameRO_352_592 (dstOff := 352#64) (dstLen := info.length - 32)
      hpre hx.exp hrun₂ hcc₂ hfr₂ ⟨by decide, by decide, by change 352 + (info.length - 32) ≤ 592; omega⟩
  have hsp₂ := hc2.common.sp_eq; have hx29_2 := hc2.common.x29_eq
  have hx19_2 : s₂.readReg64 .x19 = hsp s₀ + 352#64 := (cc_x19 hcc₂).trans hx.x19_eq
  have hx22_2 : s₂.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff := (cc_x22 hcc₂).trans hx.x22_eq
  have hx23_2 : s₂.readReg64 .x23 = hsp s₀ + 352#64 := (cc_x23 hcc₂).trans hx.x23_eq
  have hx24_2 : s₂.readReg64 .x24 = 32#64 := (cc_x24 hcc₂).trans hx.x24_eq
  have hx26_2 : s₂.readReg64 .x26 = BitVec.ofNat 64 rem := (cc_x26 hcc₂).trans hx.x26_eq
  have hx27_2 : s₂.readReg64 .x27 = BitVec.ofNat 64 i := (cc_x27 hcc₂).trans hx.x27_eq
  have hx28_2 : s₂.readReg64 .x28 = hsp s₀ + 352#64 := (cc_x28 hcc₂).trans hx.x28_eq
  have hm16_2 : s₂.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := hc2.m16_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw2 : s₂.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hc2.common.frame
  have hfacts := iter_b_s2FrameRO_facts hpre ht_len hdst_le hx hdst₂ hfr₂
  have hpos_415 := hfacts.1
  clear hx hcc₂ hdst₂ hfr₂
  rcases canWrite_hsp_352_add hrw2 (by omega : info.length - 32 < 64) with ⟨hcw_pos1, hcw_pos2⟩
  have hze32 := Expand.zeroExtend32_ofNat8_eq_truncate32 (by omega : info.length - 32 < 64)
  have hze64 := Expand.zeroExtend64_ofNat8 (by omega : info.length - 32 < 64)
  have hze64_32 := zeroExtend64_truncate32_ofNat64 (by omega : info.length - 32 < 64)
  have hand255 := Expand.zeroExtend64_and255_truncate32_ofNat64 (by omega : info.length - 32 < 64)
  have hand64_255 := Expand.and64_255_ofNat64 (by omega : info.length - 32 < 64)
  have hand40 := Expand.and_0xffffffffff_ofNat64 (by omega : info.length - 32 < 64)
  rcases Expand.cmp32_lt63_lemmas (by omega : info.length - 32 < 63) with ⟨hcmp63_eq, hcmp63_ne, hcmp63_z⟩
  have hadd1_k := Expand.zeroExtend64_add1_truncate32_ofNat64 (by omega : info.length - 32 < 63)
  rcases iter_counter_lemmas hi with ⟨hi_eq, hi_ne, hi_z, hi_add1, hi1_ze⟩
  have hdst_add : (okmA + BitVec.ofNat 64 dstOff) + 32#64 = okmA + BitVec.ofNat 64 (dstOff + 32) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hrem_sub : BitVec.ofNat 64 rem - 32#64 = BitVec.ofNat 64 (rem - 32) := by rcases hrem with rfl | rfl <;> rfl
  iterate 31 kdf_step
  refine RunsTo.refl ?_
  rcases hfacts with ⟨_, hhm_352, hokm_2⟩
  refine ⟨by kdf_reg,
    HExpCommonExt.of_agreesOutside_32_560 (off := 32#64) (sz := 464) hc2
      (by kdf_reg) (by kdf_reg) (by kdf_reg) (by prove_agrees_hsp) (by decide) (by prove_hmac_208 hc2.hmac_208),
    by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hdst_add],
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hrem_sub],
    by kdf_reg, by kdf_reg, ?_,
    agreesOutside_stk_okm_pre (off := 32#64) (sz := 464) hpre hdst_le hokm_2 (by prove_agrees_hsp) (by decide)⟩
  simp only [Expand.mem_setMem]
  refine HmacStN.of_copy_352_32 hhm_352
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := { decide := true }) only [arm64_norm]

theorem iter_b_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (ht_len : tPrev.length = 32) (hi : i = 1 ∨ i = 2) (hrem : rem = 32 ∨ rem = 64)
    (hdst : dstOff + 32 ≤ okmLen)
    (hx : StateLoopA2Ext img.base roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateLoopCExt img.base roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  refine RunsTo.trans_toE_inv hfrz hsym (iter_b_pre hpre (by omega) hx) fun s₁ hf₁ hs₁ hx₁ => ?_
  let k := info.length - 32
  have hk_lt : k < 23 := by have := hpre.info_lt; omega
  have hdrop_len : (info.drop 32).length = k := by simp [k]
  have hx2_nat : (s₁.readReg64 .x2).toNat = (info.drop 32).length := by
    rw [hx₁.x2_eq, hdrop_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hinfo_inv := HFrameExt.info_inv hpre hx₁.exp.common.frame
  have hinfo_drop : s₁.mem.readBytes (infoA + 32#64) (info.drop 32).length = info.drop 32 := by
    have h := Bytes.readBytes_slice_of_readBytes_eq s₁.mem infoA info hinfo_inv.bytes_eq 32 k (by have := hpre.info_ge; omega)
    rw [hdrop_len]; simpa [k, List.take_of_length_le (by simp : (info.drop 32).length ≤ info.length - 32)] using h
  have hin_info : ∀ a, InRegion (infoA + 32#64) (info.drop 32).length a → InRegion infoA info.length a := by
    intro a ha; rw [hdrop_len] at ha
    simp only [InRegion, k] at ha ⊢; have := hpre.info_ge; have := hpre.info_lt; bv_omega
  have hsrc_perm : if infoRO then s₁.mem.Readable (infoA + 32#64) (info.drop 32).length ∧
      (∀ a, InRegion (infoA + 32#64) (info.drop 32).length a → ∃ r ∈ roRegs, InRegion r.1 r.2 a)
    else RW s₁.mem (infoA + 32#64) (info.drop 32).length := by
    cases hro : infoRO
    · have hp := hinfo_inv.perm_inv; rw [hro] at hp
      simp only [Bool.false_eq_true, ↓reduceIte] at hp ⊢
      exact fun a ha => hp.1 a (hin_info a ha)
    · have hp := hinfo_inv.perm_inv; rw [hro] at hp
      simp only [↓reduceIte] at hp ⊢
      exact ⟨fun a ha => hinfo_inv.readable a (hin_info a ha), fun a ha => hp a (hin_info a ha)⟩
  have hrw1_hsp : s₁.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx₁.exp.common.frame
  have hd_dst_stk : (info.drop 32).length = 0 ∨
      DisjointRegions (hsp s₀ + 352#64) (info.drop 32).length
        (s₁.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hdrop_len, hx₁.exp.common.sp_eq]
    by_cases hk0 : k = 0
    · exact Or.inl hk0
    · exact Or.inr (by dsimp [extHookStack]; unfold DisjointRegions; bv_omega)
  have hmc := memcpy_any_subroutine_runsTo hs.hooks infoRO roRegs hf₁ hs₁
    hx₁.pc_eq hx₁.exp.common.status hx₁.x0_eq hx₁.x1_eq hx2_nat hinfo_drop
    (by rw [hdrop_len]; exact hrw1_hsp.sub (by bv_omega))
    hsrc_perm
    (by rw [hx₁.exp.common.sp_eq]; exact HFrameExt.rw_ext_stk hpre hx₁.exp.common.frame)
    hd_dst_stk
    (fun a ha => by
      have ho := hinfo_inv.out_stk a (hin_info a ha)
      rw [hdrop_len]; unfold OutsideRegion at ho ⊢; bv_omega)
    (fun a ha => by
      rw [hx₁.exp.common.sp_eq]
      have ho := hinfo_inv.out_stk a (hin_info a ha)
      dsimp [extHookStack]; unfold OutsideRegion at ho ⊢; bv_omega)
    (by rw [hx₁.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).1)
  refine hmc.trans fun s₂ ⟨hpc₂, hrun₂, hcc₂, _, hdst₂, _, hfr₂⟩ => ?_
  rw [hx₁.lr_eq] at hpc₂; rw [hdrop_len] at hdst₂ hfr₂; rw [hx₁.exp.common.sp_eq] at hfr₂
  exact runsTo_toE (iter_b_post hpre ht_len hi hrem hdst hx₁ hpc₂ hrun₂ hcc₂ hdst₂ hfr₂)

structure StateLoopFinExt (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64)
    (tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% hkdfToSliceName + 1280)
  exp     : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  x20_eq  : s.readReg64 .x20 = okmA + BitVec.ofNat 64 (dstOff + 32)
  x21_eq  : s.readReg64 .x21 = hsp s₀ + 352#64
  x22_eq  : s.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff
  x24_eq  : s.readReg64 .x24 = 32#64
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 (rem - 32)
  x27_eq  : s.readReg64 .x27 = BitVec.ofNat 64 i
  x28_eq  : s.readReg64 .x28 = hsp s₀ + 352#64
  t_540   : s.mem.readBytes (hsp s₀ + 540#64) 32 =
              hmacWith F (hkdfExtractBytes F salt ikm) (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre : s.mem.readBytes okmA dstOff = okmSoFar

theorem iter_fin_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (ht_len : tPrev.length = 32) (hdst : dstOff ≤ okmLen)
    (hx : StateLoopCExt img.base roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateLoopFinExt img.base roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have hrw_hsp := HFrameExt.rw_hsp hpre hx.exp.common.frame
  have hrw_sub := HFrameExt.rw_sub_16528 hpre hx.exp.common.frame
  have hpfx_lt : (tPrev ++ info.take 32).length < 2 ^ 63 := by
    rw [List.length_append, ht_len, List.length_take_of_le hpre.info_ge]; decide
  have hkey_eff : effectiveHmacKey F (hkdfExtractBytes F salt ikm) = hkdfExtractBytes F salt ikm :=
    effectiveHmacKey_of_le F (by simp [hkdfExtractBytes, LibsignalTripleRatchet.length_hmacWith])
  have hfin_pre : FinPre3GenExt img F (hkdfExtractBytes F salt ikm)
      (tPrev ++ info.take 32) (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) s :=
    { frz          := hfrz, sym := hsym
      pc_eq        := hx.pc_eq
      status       := hx.exp.common.status, pfx_lt := hpfx_lt
      tail_lt      := by have := hpre.info_lt; simp; omega
      hmac_st      := by rw [hx.x1_eq, hkey_eff]; exact hx.hmac_32
      rw_out       := by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_hm        := by rw [hx.x1_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_fsp       := by rw [hx.exp.common.sp_eq]; exact hrw_sub
      disj_out_hm  := by rw [hx.x0_eq, hx.x1_eq]; unfold DisjointRegions; bv_omega
      disj_out_fsp := by rw [hx.x0_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega
      disj_hm_fsp  := by rw [hx.x1_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega
      sp_aligned   := by rw [hx.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1 }
  refine (hs.fin_ok hfin_pre).mono fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq] at hout; rw [hx.x0_eq, hx.x1_eq, hx.exp.common.sp_eq] at hfr
  have hmsg_eq : (tPrev ++ info.take 32) ++ (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) =
      tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)] := by
    rw [List.append_assoc tPrev (info.take 32), ← List.append_assoc (info.take 32),
        List.take_append_drop, ← List.append_assoc]
  rw [hmsg_eq] at hout
  have hokm' : s'.mem.readBytes okmA dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hrw_okm_pre : s.mem.RW okmA dstOff :=
        (HFrameExt.rw_okm hpre hx.exp.common.frame).sub (by have := hpre.okm_len; bv_omega)
      refine (hfr.readBytes_eq hrw_okm_pre (fun r hr => ?_) (by have := hpre.okm_len; omega)).trans hx.okm_pre
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 32#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ - 16528#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
  exact ⟨hpc', HExpCommonExt.of_fin_frame hpre hx.exp hrun' hcs hfr,
    (cs_x20 hcs).trans hx.x20_eq, (cs_x21 hcs).trans hx.x21_eq,
    (cs_x22 hcs).trans hx.x22_eq, (cs_x24 hcs).trans hx.x24_eq,
    (cs_x25 hcs).trans hx.x25_eq, (cs_x26 hcs).trans hx.x26_eq,
    (cs_x27 hcs).trans hx.x27_eq, (cs_x28 hcs).trans hx.x28_eq, hout, hokm'⟩

private structure StateLoopDMemcpy (b : BitVec 64) (roRegs : List (BitVec 64 × ℕ))
    (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64)
    (tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "memcpy")
  exp     : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% hkdfToSliceName + 1296)
  x0_eq   : s.readReg64 .x0 = okmA + BitVec.ofNat 64 dstOff
  x1_eq   : s.readReg64 .x1 = hsp s₀ + 540#64
  x2_eq   : s.readReg64 .x2 = 32#64
  x20_eq  : s.readReg64 .x20 = okmA + BitVec.ofNat 64 (dstOff + 32)
  x21_eq  : s.readReg64 .x21 = hsp s₀ + 352#64
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 (rem - 32)
  x27_eq  : s.readReg64 .x27 = BitVec.ofNat 64 i
  x28_eq  : s.readReg64 .x28 = hsp s₀ + 352#64
  t_540   : s.mem.readBytes (hsp s₀ + 540#64) 32 =
              hmacWith F (hkdfExtractBytes F salt ikm) (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre : s.mem.readBytes okmA dstOff = okmSoFar

private theorem iter_d_pre {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hx : StateLoopFinExt b roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopDMemcpy b roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status
  have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hx20 := hx.x20_eq; have hx21 := hx.x21_eq; have hx22 := hx.x22_eq
  have hx24 := hx.x24_eq; have hx25 := hx.x25_eq; have hx26 := hx.x26_eq
  have hx27 := hx.x27_eq; have hx28 := hx.x28_eq
  iterate 4 kdf_step
  refine RunsTo.refl ⟨by kdf_reg,
    { common := ⟨by kdf_reg, by kdf_reg, by kdf_reg, hx.exp.common.saved, hx.exp.common.frame⟩
      m0_eq := hx.exp.m0_eq, m8_eq := hx.exp.m8_eq
      m16_eq := hx.exp.m16_eq, m24_eq := hx.exp.m24_eq, hmac_208 := hx.exp.hmac_208 },
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, hx.t_540, hx.okm_pre⟩

private theorem iter_d_continue_facts {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {s₀ s₁ s₂ : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA 96 s₀)
    (hx : StateLoopDMemcpy b roRegs F salt ikm info infoA okmA tPrev okmSoFar 96 1 64 32 s₀ s₁)
    (hfr₂ : S2Frame s₁.mem s₂.mem
      [(okmA + 32#64, 32), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    s₂.mem.readBytes (hsp s₀ + 540#64) 32 =
      hmacWith F (hkdfExtractBytes F salt ikm) (tPrev ++ info ++ [2#8]) ∧
    s₂.mem.readBytes okmA 32 = okmSoFar ∧
    DisjointRegions (hsp s₀ + 508#64) 32 okmA 64 := by
  have hrw1_hsp : s₁.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx.exp.common.frame
  have hrw1_okm : s₁.mem.RW okmA 96 := HFrameExt.rw_okm hpre hx.exp.common.frame
  refine ⟨?_, ?_, (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 508#64) ⟨by decide, by bv_omega⟩).sub_right
    okmA ⟨by decide, by bv_omega⟩⟩
  · refine (hfr₂.readBytes_eq (hrw1_hsp.sub (by bv_omega)) (fun r hr => ?_) (by decide)).trans hx.t_540
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only
    · exact (hpre.disj_okm_stk.sub_left (okmA + 32#64) ⟨by decide, by bv_omega⟩).sub_right
        (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩
    · dsimp [extHookStack]; unfold DisjointRegions; bv_omega
  · refine (hfr₂.readBytes_eq (hrw1_okm.sub (by bv_omega)) (fun r hr => ?_) (by decide)).trans hx.okm_pre
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only
    · unfold DisjointRegions; bv_omega
    · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ - BitVec.ofNat 64 extHookStack)
        ⟨by decide, by dsimp [extHookStack]; bv_omega⟩).sub_right okmA ⟨by decide, by bv_omega⟩

set_option maxHeartbeats 1600000 in
private theorem iter_d_continue_post {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {s₀ s₁ s₂ : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA 96 s₀)
    (hx : StateLoopDMemcpy b roRegs F salt ikm info infoA okmA tPrev okmSoFar 96 1 64 32 s₀ s₁)
    (hpc₂ : s₂.pc = b + bv% (ls_off% hkdfToSliceName + 1296)) (hrun₂ : s₂.status = .Running)
    (hcc₂ : CallingConventionPreserved s₁ s₂)
    (hdst₂ : s₂.mem.readBytes (okmA + 32#64) 32 =
      hmacWith F (hkdfExtractBytes F salt ikm) (tPrev ++ info ++ [2#8]))
    (hfr₂ : S2Frame s₁.mem s₂.mem
      [(okmA + 32#64, 32), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    let tNext := hmacWith F (hkdfExtractBytes F salt ikm) (tPrev ++ info ++ [2#8])
    RunsTo (tripleRatchetProgAtExt b ext) s₂
      (StateLoopExt b roRegs F salt ikm info infoA okmA tNext (okmSoFar ++ tNext) 96 2 32 64 s₀) := by
  intro tNext
  have hfacts := iter_d_continue_facts hpre hx hfr₂
  have hc2 : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA 96 s₀ s₂ :=
    HExpCommonExt.of_s2Frame_okm (okmOff := 32#64) (okmSub := 32)
      hpre hx.exp hrun₂ hcc₂ hfr₂ ⟨by decide, by decide⟩
  have hsp₂ := hc2.common.sp_eq; have hx29_2 := hc2.common.x29_eq
  have hx20_2 : s₂.readReg64 .x20 = okmA + 64#64 := (cc_x20 hcc₂).trans hx.x20_eq
  have hx21_2 : s₂.readReg64 .x21 = hsp s₀ + 352#64 := (cc_x21 hcc₂).trans hx.x21_eq
  have hx25_2 : s₂.readReg64 .x25 = BitVec.ofNat 64 info.length := (cc_x25 hcc₂).trans hx.x25_eq
  have hx26_2 : s₂.readReg64 .x26 = 32#64 := (cc_x26 hcc₂).trans hx.x26_eq
  have hx27_2 : s₂.readReg64 .x27 = 1#64 := (cc_x27 hcc₂).trans hx.x27_eq
  have hx28_2 : s₂.readReg64 .x28 = hsp s₀ + 352#64 := (cc_x28 hcc₂).trans hx.x28_eq
  have hm24_2 : s₂.mem.read64 (hsp s₀ + 24#64) = hsp s₀ + 508#64 := hc2.m24_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw2_hsp : s₂.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hc2.common.frame
  clear hx hcc₂ hfr₂
  iterate 9 kdf_step
  refine RunsTo.refl ?_
  rcases hfacts with ⟨ht_m2, hpre_m2, hd2⟩
  have hA2 : AgreesOutside s₂.mem
      ((((s₂.mem.write64 (hsp s₀ + 508#64) (s₂.mem.read64 (hsp s₀ + 540#64))).write64
        (hsp s₀ + 516#64) (s₂.mem.read64 (hsp s₀ + 548#64))).write64
        (hsp s₀ + 524#64) (s₂.mem.read64 (hsp s₀ + 556#64))).write64
        (hsp s₀ + 532#64) (s₂.mem.read64 (hsp s₀ + 564#64)))
      (hsp s₀ + 508#64) 32 := by prove_agrees_hsp
  refine ⟨by kdf_reg,
    HExpCommonExt.of_agreesOutside_352_592 (off := 508#64) (sz := 32) hc2
      (by kdf_reg) (by kdf_reg) (by kdf_reg) hA2 (by decide),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, ?_, ?_⟩
  · simp only [Expand.mem_setMem]
    exact readBytes_32_hsp_508_of_540 ht_m2
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
  · dsimp only [Expand.mem_setMem, tNext]
    rw [hA2.readBytes_eq hd2 (by decide), show (64 : ℕ) = 32 + 32 from rfl,
        Bytes.readBytes_add s₂.mem okmA 32 32, hpre_m2, hdst₂]

theorem iter_d_continue_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hokm96 : okmLen = 96)
    (hx : StateLoopFinExt img.base roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen 1 64 32 s₀ s) :
    let tNext := hmacWith F (hkdfExtractBytes F salt ikm) (tPrev ++ info ++ [2#8])
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateLoopExt img.base roRegs F salt ikm info infoA okmA tNext (okmSoFar ++ tNext) okmLen 2 32 64 s₀) := by
  intro tNext; subst hokm96
  refine RunsTo.trans_toE_inv hfrz hsym (iter_d_pre hx) fun s₁ hf₁ hs₁ hx₁ => ?_
  have htNext_len : tNext.length = 32 := LibsignalTripleRatchet.length_hmacWith _ _ _
  have hx2_nat : (s₁.readReg64 .x2).toNat = tNext.length := by rw [hx₁.x2_eq, htNext_len]; rfl
  have hrw1_hsp : s₁.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx₁.exp.common.frame
  have hrw1_okm : s₁.mem.RW okmA 96 := HFrameExt.rw_okm hpre hx₁.exp.common.frame
  have hd_dst_src : DisjointRegions (okmA + 32#64) 32 (hsp s₀ + 540#64) 32 :=
    (hpre.disj_okm_stk.sub_left (okmA + 32#64) ⟨by decide, by bv_omega⟩).sub_right
      (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩
  have hd_dst_stk : DisjointRegions (okmA + 32#64) 32 (s₁.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hx₁.exp.common.sp_eq]
    exact (hpre.disj_okm_stk.sub_left (okmA + 32#64) ⟨by decide, by bv_omega⟩).sub_right
      (hsp s₀ - BitVec.ofNat 64 extHookStack) ⟨by decide, by dsimp [extHookStack]; bv_omega⟩
  have hmc := memcpy_opt_subroutine_runsTo hs.hooks.memcpy hf₁ hs₁
    hx₁.pc_eq hx₁.exp.common.status hx₁.x0_eq hx₁.x1_eq hx2_nat
    (by rw [htNext_len]; exact hx₁.t_540)
    (by rw [htNext_len]; exact hrw1_okm.sub (by bv_omega))
    (by rw [htNext_len]; exact hrw1_hsp.sub (by bv_omega))
    (by rw [hx₁.exp.common.sp_eq]; exact HFrameExt.rw_ext_stk hpre hx₁.exp.common.frame)
    (by rw [htNext_len]; exact Or.inr hd_dst_src)
    (by rw [htNext_len]; exact Or.inr hd_dst_stk)
    (Or.inr (by rw [htNext_len, hx₁.exp.common.sp_eq]; dsimp [extHookStack]; unfold DisjointRegions; bv_omega))
    (by rw [hx₁.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).1)
  refine hmc.trans fun s₂ ⟨hpc₂, hrun₂, hcc₂, _, hdst₂, _, hfr₂⟩ => ?_
  rw [hx₁.lr_eq] at hpc₂; rw [htNext_len] at hdst₂ hfr₂; rw [hx₁.exp.common.sp_eq] at hfr₂
  exact runsTo_toE (iter_d_continue_post hpre hx₁ hpc₂ hrun₂ hcc₂ hdst₂ hfr₂)

private theorem iter_d_done_facts {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i dstOff : ℕ} {s₀ s₁ s₂ : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hdst_pos : 0 < dstOff) (hdst_eq : dstOff + 32 = okmLen)
    (hx : StateLoopDMemcpy b roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i 32 dstOff s₀ s₁)
    (hfr₂ : S2Frame s₁.mem s₂.mem
      [(okmA + BitVec.ofNat 64 dstOff, 32), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    s₂.mem.readBytes okmA dstOff = okmSoFar ∧
    DisjointRegions (hsp s₀ + 508#64) 32 okmA okmLen ∧
    okmLen ≤ 2 ^ 64 := by
  have hrw1_okm : s₁.mem.RW okmA okmLen := HFrameExt.rw_okm hpre hx.exp.common.frame
  refine ⟨?_, hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 508#64) ⟨by decide, by bv_omega⟩,
    by have := hpre.okm_len; omega⟩
  refine (hfr₂.readBytes_eq (hrw1_okm.sub (by have := hpre.okm_len; bv_omega))
    (fun r hr => ?_) (by have := hpre.okm_len; omega)).trans hx.okm_pre
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> dsimp only
  · have := hpre.okm_len; unfold DisjointRegions; bv_omega
  · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ - BitVec.ofNat 64 extHookStack)
      ⟨by decide, by dsimp [extHookStack]; bv_omega⟩).sub_right
      okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩

set_option maxHeartbeats 1600000 in
private theorem iter_d_done_post {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i dstOff : ℕ} {s₀ s₁ s₂ : State}
    (hpre : HPreExt b saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hdst_pos : 0 < dstOff) (hdst_eq : dstOff + 32 = okmLen)
    (hokm_eq : okmSoFar ++ hmacWith F (hkdfExtractBytes F salt ikm)
        (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) =
      hkdfExpand F (hkdfExtractBytes F salt ikm) info okmLen)
    (hx : StateLoopDMemcpy b roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i 32 dstOff s₀ s₁)
    (hpc₂ : s₂.pc = b + bv% (ls_off% hkdfToSliceName + 1296)) (hrun₂ : s₂.status = .Running)
    (hcc₂ : CallingConventionPreserved s₁ s₂)
    (hdst₂ : s₂.mem.readBytes (okmA + BitVec.ofNat 64 dstOff) 32 =
      hmacWith F (hkdfExtractBytes F salt ikm) (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]))
    (hfr₂ : S2Frame s₁.mem s₂.mem
      [(okmA + BitVec.ofNat 64 dstOff, 32), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    RunsTo (tripleRatchetProgAtExt b ext) s₂
      (StateDoneExt b roRegs F salt ikm info okmA okmLen s₀) := by
  have hfacts := iter_d_done_facts hpre hdst_pos hdst_eq hx hfr₂
  have hc2 : HExpCommonExt roRegs F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s₂ :=
    HExpCommonExt.of_s2Frame_okm (okmOff := BitVec.ofNat 64 dstOff) (okmSub := 32)
      hpre hx.exp hrun₂ hcc₂ hfr₂
      ⟨by decide, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hpre.okm_len; omega)]; omega⟩
  have hsp₂ := hc2.common.sp_eq; have hx29_2 := hc2.common.x29_eq
  have hx20_2 : s₂.readReg64 .x20 = okmA + BitVec.ofNat 64 (dstOff + 32) := (cc_x20 hcc₂).trans hx.x20_eq
  have hx21_2 : s₂.readReg64 .x21 = hsp s₀ + 352#64 := (cc_x21 hcc₂).trans hx.x21_eq
  have hx25_2 : s₂.readReg64 .x25 = BitVec.ofNat 64 info.length := (cc_x25 hcc₂).trans hx.x25_eq
  have hx26_2 : s₂.readReg64 .x26 = 0#64 := (cc_x26 hcc₂).trans hx.x26_eq
  have hx27_2 : s₂.readReg64 .x27 = BitVec.ofNat 64 i := (cc_x27 hcc₂).trans hx.x27_eq
  have hx28_2 : s₂.readReg64 .x28 = hsp s₀ + 352#64 := (cc_x28 hcc₂).trans hx.x28_eq
  have hm0_2 : s₂.mem.read64 (hsp s₀) = BitVec.ofNat 64 okmLen := by simpa [BitVec.add_zero] using hc2.m0_eq
  have hm0_2' : s₂.mem.read64 (hsp s₀ + 0#64) = BitVec.ofNat 64 okmLen := hc2.m0_eq
  have hm24_2 : s₂.mem.read64 (hsp s₀ + 24#64) = hsp s₀ + 508#64 := hc2.m24_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw2_hsp : s₂.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hc2.common.frame
  clear hx hcc₂ hfr₂
  rcases okmLen_lt_8161_lemmas hpre.okm_len with ⟨hokm_c, hokm_ule, hokm_ult⟩
  iterate 13 kdf_step
  refine RunsTo.refl ?_
  rcases hfacts with ⟨hpre_m2, hd2, hokm_le⟩
  have hA2 : AgreesOutside s₂.mem
      ((((s₂.mem.write64 (hsp s₀ + 508#64) (s₂.mem.read64 (hsp s₀ + 540#64))).write64
        (hsp s₀ + 516#64) (s₂.mem.read64 (hsp s₀ + 548#64))).write64
        (hsp s₀ + 524#64) (s₂.mem.read64 (hsp s₀ + 556#64))).write64
        (hsp s₀ + 532#64) (s₂.mem.read64 (hsp s₀ + 564#64)))
      (hsp s₀ + 508#64) 32 := by prove_agrees_hsp
  refine ⟨by kdf_reg,
    HCommonExt.of_agreesOutside_hsp (off := 508#64) (sz := 32) hc2.common
      (by kdf_reg) (by kdf_reg) (by kdf_reg) hA2 (by decide), ?_⟩
  dsimp only [Expand.mem_setMem]
  rw [hA2.readBytes_eq hd2 hokm_le, ← hdst_eq,
      Bytes.readBytes_add s₂.mem okmA dstOff 32, hpre_m2, hdst₂, hokm_eq, hdst_eq]

theorem iter_d_done_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i dstOff : ℕ} {s₀ s : State}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hdst_pos : 0 < dstOff) (hdst_eq : dstOff + 32 = okmLen)
    (hokm_eq : okmSoFar ++ hmacWith F (hkdfExtractBytes F salt ikm)
        (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) =
      hkdfExpand F (hkdfExtractBytes F salt ikm) info okmLen)
    (hx : StateLoopFinExt img.base roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i 32 dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateDoneExt img.base roRegs F salt ikm info okmA okmLen s₀) := by
  refine RunsTo.trans_toE_inv hfrz hsym (iter_d_pre hx) fun s₁ hf₁ hs₁ hx₁ => ?_
  let tNext := hmacWith F (hkdfExtractBytes F salt ikm) (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])
  have htNext_len : tNext.length = 32 := LibsignalTripleRatchet.length_hmacWith _ _ _
  have hx2_nat : (s₁.readReg64 .x2).toNat = tNext.length := by rw [hx₁.x2_eq, htNext_len]; rfl
  have hrw1_hsp : s₁.mem.RW (hsp s₀) 688 := HFrameExt.rw_hsp hpre hx₁.exp.common.frame
  have hrw1_okm : s₁.mem.RW okmA okmLen := HFrameExt.rw_okm hpre hx₁.exp.common.frame
  have hd_dst_src : DisjointRegions (okmA + BitVec.ofNat 64 dstOff) 32 (hsp s₀ + 540#64) 32 :=
    (hpre.disj_okm_stk.sub_left (okmA + BitVec.ofNat 64 dstOff)
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right
      (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩
  have hd_dst_stk : DisjointRegions (okmA + BitVec.ofNat 64 dstOff) 32
      (s₁.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hx₁.exp.common.sp_eq]
    exact (hpre.disj_okm_stk.sub_left (okmA + BitVec.ofNat 64 dstOff)
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right
      (hsp s₀ - BitVec.ofNat 64 extHookStack) ⟨by decide, by dsimp [extHookStack]; bv_omega⟩
  have hmc := memcpy_opt_subroutine_runsTo hs.hooks.memcpy hf₁ hs₁
    hx₁.pc_eq hx₁.exp.common.status hx₁.x0_eq hx₁.x1_eq hx2_nat
    (by rw [htNext_len]; exact hx₁.t_540)
    (by rw [htNext_len]; exact hrw1_okm.sub (by have := hpre.okm_len; bv_omega))
    (by rw [htNext_len]; exact hrw1_hsp.sub (by bv_omega))
    (by rw [hx₁.exp.common.sp_eq]; exact HFrameExt.rw_ext_stk hpre hx₁.exp.common.frame)
    (by rw [htNext_len]; exact Or.inr hd_dst_src)
    (by rw [htNext_len]; exact Or.inr hd_dst_stk)
    (Or.inr (by rw [htNext_len, hx₁.exp.common.sp_eq]; dsimp [extHookStack]; unfold DisjointRegions; bv_omega))
    (by rw [hx₁.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).1)
  refine hmc.trans fun s₂ ⟨hpc₂, hrun₂, hcc₂, _, hdst₂, _, hfr₂⟩ => ?_
  rw [hx₁.lr_eq] at hpc₂; rw [htNext_len] at hdst₂ hfr₂; rw [hx₁.exp.common.sp_eq] at hfr₂
  exact runsTo_toE (iter_d_done_post hpre hdst_pos hdst_eq hokm_eq hx₁ hpc₂ hrun₂ hcc₂ hdst₂ hfr₂)

/-- One full loop iteration (`img.base + hex:637b8` → `img.base + hex:63784`, `A1 + A2 + B + Fin`):
computes `T(i + 1)` at `hsp s₀ + 540#64`. -/
theorem iter_step_runsTo_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (ht_len : tPrev.length = 32) (hi : i = 1 ∨ i = 2) (hrem : rem = 32 ∨ rem = 64) (hdst : dstOff + 32 ≤ okmLen)
    (hx : StateLoopExt img.base roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateLoopFinExt img.base roRegs F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) :=
  RunsTo.trans_toE_inv hfrz hsym (iter_a1_runsTo_ext hpre ht_len hrem (by omega) hx) fun _ hf1 hs1 hx1 =>
  RunsToE.trans_inv hf1 hs1 (iter_a2_runsTo_ext hs hf1 hs1 hpre ht_len (by omega) hx1) fun _ hf2 hs2 hx2 =>
  RunsToE.trans_inv hf2 hs2 (iter_b_runsTo_ext hs hf2 hs2 hpre ht_len hi hrem hdst hx2) fun _ hf3 hs3 hx3 =>
  iter_fin_runsTo_ext hs hf3 hs3 hpre ht_len (by omega) hx3

/-! ## Full `RunsToE` Theorem & Stack/FnAddr Helpers for `spqr::kdf::hkdf_to_slice` (`hex:63284`) -/

theorem hkdf_to_slice_runsToE_ext (hs : HkdfStubsExt img F ext)
    {saltRO ikmRO infoRO : Bool} {roRegs : List (BitVec 64 × ℕ)}
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hfrz : img.FrozenLoaded s₀) (hsym : s₀.symtab = img.symtab)
    (hpre : HPreExt img.base saltRO ikmRO infoRO roRegs salt ikm info saltA ikmA infoA okmA okmLen s₀) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s₀
      (HPostCSExt roRegs F salt ikm info okmA okmLen s₀) := by
  refine RunsToE.trans_inv hfrz hsym (block1_phase_runsTo_ext hs hfrz hsym hpre) fun s₁ hf1 hs1 hx₁ => ?_
  rcases hpre.okm_len with rfl | rfl | rfl
  · exact runsTo_toE ((b1_done_32_runsTo_ext hx₁).trans fun _ hdone => epilogue_runsTo_ext hpre hdone)
  · refine RunsTo.trans_toE_inv hf1 hs1 (b1_to_loop_runsTo_ext (Or.inl rfl) hx₁) fun s₂ hf2 hs2 hloop1 => ?_
    refine RunsToE.trans_inv hf2 hs2
      (iter_step_runsTo_ext hs hf2 hs2 hpre (Expand.t1_length _ _ _) (Or.inl rfl) (Or.inl rfl) (by decide) hloop1)
      fun s₃ hf3 hs3 hfin1 => ?_
    refine RunsToE.trans_inv hf3 hs3
      (iter_d_done_runsTo_ext hs hf3 hs3 hpre (by decide) rfl
        (hkdfExpand_64_eq F (hkdfExtractBytes F salt ikm) info).symm hfin1)
      fun _ _ _ hdone => runsTo_toE (epilogue_runsTo_ext hpre hdone)
  · refine RunsTo.trans_toE_inv hf1 hs1 (b1_to_loop_runsTo_ext (Or.inr rfl) hx₁) fun s₂ hf2 hs2 hloop1 => ?_
    refine RunsToE.trans_inv hf2 hs2
      (iter_step_runsTo_ext hs hf2 hs2 hpre (Expand.t1_length _ _ _) (Or.inl rfl) (Or.inr rfl) (by decide) hloop1)
      fun s₃ hf3 hs3 hfin1 => ?_
    refine RunsToE.trans_inv hf3 hs3 (iter_d_continue_runsTo_ext hs hf3 hs3 hpre rfl hfin1) fun s₄ hf4 hs4 hloop2 => ?_
    refine RunsToE.trans_inv hf4 hs4
      (iter_step_runsTo_ext hs hf4 hs4 hpre (LibsignalTripleRatchet.length_hmacWith _ _ _) (Or.inr rfl) (Or.inl rfl) (by decide) hloop2)
      fun s₅ hf5 hs5 hfin2 => ?_
    refine RunsToE.trans_inv hf5 hs5
      (iter_d_done_runsTo_ext hs hf5 hs5 hpre (by decide) rfl
        (hkdfExpand_96_eq F (hkdfExtractBytes F salt ikm) info).symm hfin2)
      fun _ _ _ hdone => runsTo_toE (epilogue_runsTo_ext hpre hdone)

theorem stackAt_hkdfToSlice_ext (s₀ : State) :
    stackAt s₀.sp hkdfToSliceStackExt = memRegion (hsp s₀ - 16928#64) 17616 := by
  unfold stackAt hkdfToSliceStackExt extHookStack hsp; congr 1; bv_omega

theorem hkdfToSlice_fnAddr_lsoff (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.SpqrV1.ChainProofs.hkdfToSliceName =
      b + bv% (ls_off% hkdfToSliceName) := by
  unfold tripleRatchetProgAtExt CryptoVerification.SpqrV1.ChainProofs.hkdfToSliceName
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "spqr::kdf::hkdf_to_slice")]

end CryptoVerification.SpqrV1.Kdf.HkdfToSliceExtProof
