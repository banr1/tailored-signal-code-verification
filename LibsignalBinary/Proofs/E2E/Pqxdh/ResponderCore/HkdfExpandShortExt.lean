/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfStubsExt
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfFinGenExt
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand

/-!
# `.inImage`-Free `expand_multi_info` (`64` B and `80` B) on `tripleRatchetProgAtExt`

Proves `expand_multi_info_ok_ro_ext` on `tripleRatchetProgAtExt img.base ext` from
`HkdfStubsExt img.base F ext` (`17024` B stack, `info.length < 23`, `okmLen ∈ {64, 80}`) by reusing
the straight-line `RunsTo` segments against a vacuous `emptyImg b` symbol table, together with
`pqxdhHkdfExpand_8_ok_of_stubsExt` and `pqxdhHkdfExpand_10_ok_of_stubsExt`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Expand
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
open CryptoVerification.LibsignalTripleRatchet.HkdfExt.ExpandExt
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.E2E.Pqxdh.Initiator

attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint
  sp_sub_496_eq_esp sp_add_neg496_eq_esp esp_add_496_sub_496
  read8_write64_120_127 CryptoVerification.LibsignalTripleRatchet.Expand.truncate8_ofNat64
  bv32_zero_add bv8_zero_add
  t1_length t2_length t3_length

/-! ## 1. Vacuous Reference `Obj.Image` & Hook Step Bridges -/

private def emptyImg (b : BitVec 64) : Obj.Image :=
  { base := b
    code := []
    dataAddr := 0#64
    data := []
    roData := []
    externData := []
    gotAddr := 0#64
    got := []
    symbols := []
    objSymbols := []
    stubs := [] }

private def s0Ref (b : BitVec 64) (s₀ : State) : State :=
  { s₀ with symtab := (emptyImg b).symtab }

private theorem emptyImg_frozenLoaded {b : BitVec 64} (hb : b.toNat % 4 = 0) (s : State) :
    (emptyImg b).FrozenLoaded s := by
  unfold Obj.Image.FrozenLoaded Program.CodeLoaded emptyImg Obj.HoldsBytes Obj.Image.gotBytes
  refine ⟨⟨hb, ?_, ?_⟩, ?_, ?_⟩
  · simp [Program.ofImageWithSvc, Program.ofImage]
    exact Nat.le_of_lt b.isLt
  · intro i hi; simp [Program.ofImageWithSvc, Program.ofImage] at hi
  · intro i hi; simp at hi
  · intro r hr; simp at hr

private theorem memsetStep_of_stubs {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)} (hS : HkdfStubsExt b F ext) :
    MemsetStepExt b ext :=
  fun hpc hstat hx0 hx1 hx2 hrw_dst hrw_stk hd_dst_stk hsp_al =>
    memset_stub_runsTo hS.memset hpc hstat hx0 hx1 hx2 hrw_dst hrw_stk hd_dst_stk hsp_al

private theorem compressOneStep_of_stubs {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)} (hS : HkdfStubsExt b F ext) :
    CompressOneStepExt b F ext :=
  fun hpc hstat hx0 hx1 hx2 hst hblk hrw_st hrw_blk hrw_stk hd_sb hd_ss hd_bs hsp_al =>
    compress256_one_stub_runsTo hS.compress256 (by decide)
      hpc hstat hx0 hx1 hx2 hst hblk hrw_st hrw_blk hrw_stk hd_sb hd_ss hd_bs hsp_al

private theorem fin_side_conditions_ro {img : Obj.Image} {F : ShaCompress}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hf : ExpandFrameX infoPtr info.length okmLen s₀ s.mem) :
    RW s.mem (esp s₀ + 208#64) 32 ∧
    RW s.mem (esp s₀ + 240#64) 0x90 ∧
    RW s.mem (esp s₀ - 16528#64) 16528 ∧
    DisjointRegions (esp s₀ + 208#64) 32 (esp s₀ + 240#64) 0x90 ∧
    DisjointRegions (esp s₀ + 208#64) 32 (esp s₀ - 16528#64) 16528 ∧
    DisjointRegions (esp s₀ + 240#64) 0x90 (esp s₀ - 16528#64) 16528 := by
  have hrw_stack : s.mem.RW (s₀.sp - 17024#64) 17024 := ExpandFrameX.rw_stkX hpre hf
  have hrw_esp : s.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hf
  refine ⟨hrw_esp.sub (by bv_omega), hrw_esp.sub (by bv_omega),
    hrw_stack.sub (by unfold esp; bv_omega),
    by unfold DisjointRegions; bv_omega,
    by unfold DisjointRegions esp at *; bv_omega,
    by unfold DisjointRegions esp at *; bv_omega⟩

/-! ## 2. `.inImage`-Free Prologue & External Call Wrappers -/

section SegmentsRO

variable {b : BitVec 64} {F : ShaCompress} {ext : String → Option (State → State)}

private theorem seg0_ro_x_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen : ℕ} {s₀ : State}
    (hpre : ExpandPreX (emptyImg b) F prk info infoPtr okmLen (s0Ref b s₀)) :
    RunsTo (tripleRatchetProgAtExt b ext) s₀
      (StateX0pX b infoPtr info.length okmLen (s0Ref b s₀)) := by
  have hpc : s₀.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info") :=
    hpre.pc_eq
  have hrun : s₀.status = .Running := hpre.status
  have hx3 : s₀.readReg64 .x3 = BitVec.ofNat 64 okmLen := hpre.x3_eq
  have hsp_al : (s₀.sp &&& 15#64) = 0#64 := hpre.sp_aligned
  have hesp : (esp s₀ &&& 15#64) = 0#64 := esp_aligned hsp_al
  have hrw : s₀.mem.RW (esp s₀) 496 :=
    ExpandFrameX.rw_esp (s₀ := s0Ref b s₀) hpre (S2FrameRO.refl infoPtr info.length s₀.mem _)
  iterate 8 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc], hrun,
    by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm]; rfl,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm]; rfl,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm]; rfl,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm]; rfl,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm]; rfl,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx3], ?_, ?_⟩
  · simp only [Expand.mem_setMem]
    have hesp_ref : esp (s0Ref b s₀) = esp s₀ := rfl
    have hreg_ref : ∀ r, (s0Ref b s₀).readReg64 r = s₀.readReg64 r := fun _ => rfl
    exact
      { m400 := by rw [hesp_ref, hreg_ref]; simp (config := { decide := true }) only [arm64_norm]
        m408 := by rw [hesp_ref, hreg_ref]; simp (config := { decide := true }) only [arm64_norm]
        m416 := by rw [hesp_ref, hreg_ref]; simp (config := { decide := true }) only [arm64_norm]
        m424 := by rw [hesp_ref, hreg_ref]; simp (config := { decide := true }) only [arm64_norm]
        m432 := by rw [hesp_ref, hreg_ref]; simp (config := { decide := true }) only [arm64_norm]
        m440 := by rw [hesp_ref, hreg_ref]; simp (config := { decide := true }) only [arm64_norm]
        m448 := by rw [hesp_ref, hreg_ref]; simp (config := { decide := true }) only [arm64_norm]
        m456 := by rw [hesp_ref, hreg_ref]; simp (config := { decide := true }) only [arm64_norm]
        m464 := by rw [hesp_ref, hreg_ref]; simp (config := { decide := true }) only [arm64_norm]
        m472 := by rw [hesp_ref, hreg_ref]; simp (config := { decide := true }) only [arm64_norm]
        m480 := by rw [hesp_ref, hreg_ref]; simp (config := { decide := true }) only [arm64_norm]
        m488 := by rw [hesp_ref, hreg_ref]; simp (config := { decide := true }) only [arm64_norm] }
  · exact ExpandFrameX.of_agreesOutside_esp (s₀ := s0Ref b s₀) (off := 400#64) (sz := 96)
      (S2FrameRO.refl infoPtr info.length s₀.mem _)
      (by change AgreesOutside _ _ (esp s₀ + 400#64) 96; prove_agrees_esp) (by decide)

private theorem seg2a_ro_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPreX (emptyImg b) F prk info infoPtr okmLen s₀)
    (hx : StateX1X b F prk info infoPtr okmLen s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s (StateX1bX b F prk info infoPtr okmLen s₀) := by
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
  have hmc := memcpyRO_stub_runsTo hS.memcpyRO
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
  exact Extract.RunsTo.toE (seg2a_tail_x_runsTo hpre (hpc₁.trans hx.lr_eq) hc1
    ((Extract.CallingConventionPreserved.x19 hcc₁).trans hx.x19_eq)
    ((Extract.CallingConventionPreserved.x22 hcc₁).trans hx.x22_eq)
    ((CallingConventionPreserved.x23 hcc₁).trans hx.x23_eq)
    ((CallingConventionPreserved.x24 hcc₁).trans hx.x24_eq)
    ((CallingConventionPreserved.x26 hcc₁).trans hx.x26_eq)
    hhm₁ hdst₁)

private theorem fin1_ro_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPreX (emptyImg b) F prk info infoPtr okmLen s₀)
    (hx : StateX2X b F prk info infoPtr okmLen s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s
      (StateX2rX b F prk info infoPtr okmLen s₀) := by
  rcases fin_side_conditions_ro hpre hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hfin := finalize_fixed_single_runsToE_base
    (memsetStep_of_stubs hS) (compressOneStep_of_stubs hS)
    hx.pc_eq hx.common.status hx.x0_eq hx.x1_eq
    hpre.prk_le (by have := hpre.info_lt; simp; omega)
    hx.hmac_240 hrw_x0 hrw_x1
    (by rw [hx.common.sp_eq]; exact hrw_sp)
    hd_x0_x1
    (by rw [hx.common.sp_eq]; exact hd_x0_sp)
    (by rw [hx.common.sp_eq]; exact hd_x1_sp)
    (by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned)
  refine hfin.mono fun s' ⟨hpc', hstat', hcc, ht1, hfr⟩ => ?_
  rw [hx.common.sp_eq] at hfr
  exact ⟨hpc'.trans hx.lr_eq,
    ExpandCommonX.of_fin_frame_x hpre hx.common hstat' hcc hfr,
    (Extract.CallingConventionPreserved.x22 hcc).trans hx.x22_eq,
    (CallingConventionPreserved.x23 hcc).trans hx.x23_eq,
    (CallingConventionPreserved.x26 hcc).trans hx.x26_eq,
    ht1⟩

private theorem seg3_ro_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPreX (emptyImg b) F prk info infoPtr okmLen s₀)
    (hx : StateX2rX b F prk info infoPtr okmLen s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s
      (StateLoopX b infoPtr info.length okmLen
        (t1 F prk info) (t1 F prk info) 1 (okmLen - 32) 32 s₀) := by
  refine (Extract.RunsTo.toE (seg3_head_x_runsTo (img := emptyImg b) hx)).trans fun s_mc h_mc => ?_
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
  have hmc := memcpy_stub_runsTo hS.memcpy
    (bs := t1 F prk info)
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
  exact Extract.RunsTo.toE (seg3_tail_x_runsTo hpre (hpc₁.trans hlr_mc) hc1
    ((Extract.CallingConventionPreserved.x22 hcc₁).trans hx22_mc)
    ((CallingConventionPreserved.x23 hcc₁).trans hx23_mc)
    ((CallingConventionPreserved.x26 hcc₁).trans hx26_mc)
    ht1_x2 ht1_208)

private theorem iter_b_ro_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPreX (emptyImg b) F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA2X b F prk info infoPtr tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s
      (StateLoopBX b F prk info tPrev okmSoFar infoPtr okmLen i rem dstOff s₀) := by
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
  have hmc := memcpyRO_stub_runsTo hS.memcpyRO
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
  exact Extract.RunsTo.toE (iter_b_tail_x_runsTo hpre ht_len hi hdst (hpc₁.trans hx.lr_eq) hc1
    ((Extract.CallingConventionPreserved.x19 hcc₁).trans hx.x19_eq)
    ((Extract.CallingConventionPreserved.x21 hcc₁).trans hx.x21_eq)
    ((Extract.CallingConventionPreserved.x22 hcc₁).trans hx.x22_eq)
    ((CallingConventionPreserved.x23 hcc₁).trans hx.x23_eq)
    ((CallingConventionPreserved.x25 hcc₁).trans hx.x25_eq)
    ((CallingConventionPreserved.x26 hcc₁).trans hx.x26_eq)
    ((CallingConventionPreserved.x28 hcc₁).trans hx.x28_eq)
    hhm₁ hdst₁ hokm₁)

private theorem iter_fin_ro_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPreX (emptyImg b) F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopCX b F prk info tPrev okmSoFar infoPtr okmLen i rem dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s
      (StateLoopFinX b F prk info tPrev okmSoFar infoPtr okmLen i rem dstOff s₀) := by
  rcases fin_side_conditions_ro hpre hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) okmLen := ExpandFrameX.rw_x2 hpre hx.common.frame
  have hfin := finalize_fixed_single_runsToE_base
    (memsetStep_of_stubs hS) (compressOneStep_of_stubs hS)
    hx.pc_eq hx.common.status hx.x0_eq hx.x1_eq
    hpre.prk_le (by have := hpre.info_lt; simp [ht_len]; omega)
    hx.hmac_240 hrw_x0 hrw_x1
    (by rw [hx.common.sp_eq]; exact hrw_sp)
    hd_x0_x1
    (by rw [hx.common.sp_eq]; exact hd_x0_sp)
    (by rw [hx.common.sp_eq]; exact hd_x1_sp)
    (by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned)
  refine hfin.mono fun s' ⟨hpc', hstat', hcc, ht, hfr⟩ => ?_
  rw [hx.common.sp_eq] at hfr
  have hokm' : s'.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · refine (hfr.readBytes_eq (hrw_x2.sub (by have := hpre.okm_len; bv_omega)) (fun r hr => ?_)
        (by have := hpre.okm_len; omega)).trans hx.okm_pre
      have hd_stk : DisjointRegions (s₀.sp - 17024#64) 17024 (s₀.readReg64 .x2) dstOff :=
        hpre.disj_x2_stack.symm.sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact hd_stk.sub_left _ ⟨by simp, by unfold esp; bv_omega⟩
  exact ⟨hpc'.trans hx.lr_eq,
    ExpandCommonX.of_fin_frame_x hpre hx.common hstat' hcc hfr,
    (Extract.CallingConventionPreserved.x19 hcc).trans hx.x19_eq,
    (Extract.CallingConventionPreserved.x21 hcc).trans hx.x21_eq,
    (Extract.CallingConventionPreserved.x22 hcc).trans hx.x22_eq,
    (CallingConventionPreserved.x23 hcc).trans hx.x23_eq,
    (CallingConventionPreserved.x24 hcc).trans hx.x24_eq,
    (CallingConventionPreserved.x26 hcc).trans hx.x26_eq,
    (CallingConventionPreserved.x28 hcc).trans hx.x28_eq,
    ht, hokm'⟩

private theorem iter_to_fin_ro_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s_start s₀ : State}
    (hpre : ExpandPreX (emptyImg b) F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 32 ∨ rem = 48 ∨ rem = 16)
    (hdst : dstOff ≤ okmLen)
    (hloop : RunsToE (tripleRatchetProgAtExt b ext) s_start
      (StateLoopX b infoPtr info.length okmLen tPrev okmSoFar i rem dstOff s₀)) :
    RunsToE (tripleRatchetProgAtExt b ext) s_start
      (StateLoopFinX b F prk info tPrev okmSoFar infoPtr okmLen i rem dstOff s₀) := by
  have h1 := hloop.trans fun s hs => Extract.RunsTo.toE (iter_a1_x_runsTo hpre hrem hdst hs)
  have h2 := h1.trans fun s hs => Extract.RunsTo.toE (iter_a2_x_runsTo hpre ht_len hdst hs)
  have h3 := h2.trans fun s hs => iter_b_ro_x_runsTo hS hpre ht_len hi hdst hs
  have h4 := h3.trans fun s hs => Extract.RunsTo.toE (iter_c_x_runsTo hpre hrem hdst hs)
  exact h4.trans fun s hs => iter_fin_ro_x_runsTo hS hpre ht_len hdst hs

private theorem iter_d_continue_ro_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info tPrev okmSoFar tNext : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPreX (emptyImg b) F prk info infoPtr okmLen s₀)
    (hi : i = 1)
    (hdst : dstOff + 32 ≤ okmLen)
    (htNext : tNext = hmacWith F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]))
    (hx : StateLoopFinX b F prk info tPrev okmSoFar infoPtr okmLen i 48 dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s
      (StateLoopX b infoPtr info.length okmLen tNext (okmSoFar ++ tNext) (i + 1) 16 (dstOff + 32) s₀) := by
  subst hi
  have ht_208 : s.mem.readBytes (esp s₀ + 208#64) 32 = tNext := htNext ▸ hx.t_208
  have ht_len : tNext.length = 32 := by rw [htNext, length_hmacWith]
  clear htNext
  refine (Extract.RunsTo.toE (iter_d_head_x_runsTo (img := emptyImg b) hx)).trans fun s_mc h_mc => ?_
  rcases h_mc with ⟨hpc_mc, hstat_mc, hsp_mc, hlr_mc, hx0_mc, hx1_mc, hx2_mc,
    hx19_mc, hx20_mc, hx21_mc, hx22_mc, hx23_mc, hx24_mc, hx26_mc, hx27_mc, hx28_mc, hx29_mc, hmem_mc⟩
  have hrw_stk : s_mc.mem.RW (s₀.sp - 17024#64) 17024 := by
    rw [hmem_mc]; exact ExpandFrameX.rw_stkX hpre hx.common.frame
  have hrw_esp : s_mc.mem.RW (esp s₀) 496 := by
    rw [hmem_mc]; exact ExpandFrameX.rw_esp hpre hx.common.frame
  have hrw_x2 : s_mc.mem.RW (s₀.readReg64 .x2) okmLen := by
    rw [hmem_mc]; exact ExpandFrameX.rw_x2 hpre hx.common.frame
  have hrw_dst : s_mc.mem.RW (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 :=
    hrw_x2.sub (by have := hpre.okm_len; bv_omega)
  have hrw_src : s_mc.mem.RW (esp s₀ + 208#64) 32 := hrw_esp.sub (by bv_omega)
  have hrw_ext : s_mc.mem.RW (s_mc.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_mc]
    change s_mc.mem.RW (esp s₀ - 16384#64) 16384
    exact hrw_stk.sub (by unfold esp; bv_omega)
  have hd_dst_src : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 (esp s₀ + 208#64) 32 :=
    (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ + 208#64)
      ⟨by decide, by unfold esp; bv_omega⟩
  have hd_dst_ext : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32
      (s_mc.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_mc]
    change DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 (esp s₀ - 16384#64) 16384
    exact (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ - 16384#64)
      ⟨by decide, by unfold esp; bv_omega⟩
  have hd_src_ext : DisjointRegions (esp s₀ + 208#64) 32
      (s_mc.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_mc]
    change DisjointRegions (esp s₀ + 208#64) 32 (esp s₀ - 16384#64) 16384
    unfold DisjointRegions; bv_omega
  have hc_mc : ExpandCommonX infoPtr info.length okmLen s₀ s_mc :=
    ⟨hstat_mc, hsp_mc, hx29_mc, hx27_mc, hx20_mc,
     by rw [hmem_mc]; exact hx.common.m8_eq,
     by rw [hmem_mc]; exact hx.common.m16_eq,
     by rw [hmem_mc]; exact hx.common.saved,
     by rw [hmem_mc]; exact hx.common.frame⟩
  have hmc := memcpy_stub_runsTo hS.memcpy
    (bs := tNext)
    hpc_mc hstat_mc hx0_mc hx1_mc
    (by rw [hx2_mc, ht_len]; rfl)
    (by rw [ht_len, hmem_mc]; exact ht_208)
    (by rw [ht_len]; exact hrw_dst)
    (by rw [ht_len]; exact hrw_src)
    hrw_ext
    (by rw [ht_len]; exact hd_dst_src)
    (by rw [ht_len]; exact hd_dst_ext)
    (by rw [ht_len]; exact hd_src_ext)
    (by rw [hsp_mc]; exact esp_aligned hpre.sp_aligned)
  refine hmc.trans fun s₁ hs₁ => ?_
  rcases hs₁ with ⟨hpc₁, hstat₁, hcc₁, _, hdst₁, hsrc₁, hfr_mc⟩
  rw [hsp_mc, ht_len] at hfr_mc
  rw [ht_len] at hdst₁ hsrc₁
  have hoff_lt : dstOff < 2 ^ 64 := by have := hpre.okm_len; omega
  have hc1 : ExpandCommonX infoPtr info.length okmLen s₀ s₁ :=
    ExpandCommonX.of_memcpy_x2_frame hpre hc_mc
      ⟨by decide, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt]; exact hdst⟩
      hstat₁ hcc₁ hfr_mc
  have hleft : s₁.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · refine (hfr_mc.readBytes_eq (hrw_x2.sub (by have := hpre.okm_len; bv_omega)) (fun r hr => ?_)
        (by have := hpre.okm_len; omega)).trans (by rw [hmem_mc]; exact hx.okm_pre)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · unfold DisjointRegions; have := hpre.okm_len; bv_omega
      · change DisjointRegions (esp s₀ - 16384#64) 16384 (s₀.readReg64 .x2) dstOff
        exact (hpre.disj_x2_stack.symm.sub_left (esp s₀ - 16384#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
  have hokm_next : s₁.mem.readBytes (s₀.readReg64 .x2) (dstOff + 32) = okmSoFar ++ tNext := by
    rw [Bytes.readBytes_add s₁.mem (s₀.readReg64 .x2) dstOff 32, hleft, hdst₁]
  exact Extract.RunsTo.toE (iter_d_continue_tail_x_runsTo hpre hdst (hpc₁.trans hlr_mc) hc1
    ((Extract.CallingConventionPreserved.x19 hcc₁).trans hx19_mc)
    ((Extract.CallingConventionPreserved.x21 hcc₁).trans hx21_mc)
    ((CallingConventionPreserved.x24 hcc₁).trans hx24_mc)
    ((CallingConventionPreserved.x26 hcc₁).trans hx26_mc)
    ((CallingConventionPreserved.x28 hcc₁).trans hx28_mc)
    hsrc₁ hokm_next)

private theorem iter_d_done_ro_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPreX (emptyImg b) F prk info infoPtr okmLen s₀)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 32 ∨ rem = 16)
    (hdst : dstOff + rem = okmLen)
    (hokm : okmSoFar ++ (hmacWith F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])).take rem =
              hkdfExpand F prk info okmLen)
    (hx : StateLoopFinX b F prk info tPrev okmSoFar infoPtr okmLen i rem dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s
      (StateDoneX b F prk info infoPtr okmLen s₀) := by
  let tNext := hmacWith F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])
  have hmin : min rem 32 = rem := by rcases hrem with rfl | rfl <;> rfl
  have hrem_pos : 0 < rem := by rcases hrem with rfl | rfl <;> decide
  have htake_len : (tNext.take rem).length = rem := by
    rw [List.length_take, length_hmacWith]; omega
  have hread_rem : s.mem.readBytes (esp s₀ + 208#64) rem = tNext.take rem := by
    have hslice := Bytes.readBytes_slice_of_readBytes_eq s.mem (esp s₀ + 208#64) tNext
      (by rw [length_hmacWith]; exact hx.t_208) 0 rem (by rw [length_hmacWith]; omega)
    simpa using hslice
  refine (Extract.RunsTo.toE (iter_d_head_x_runsTo (img := emptyImg b) hx)).trans fun s_mc h_mc => ?_
  rcases h_mc with ⟨hpc_mc, hstat_mc, hsp_mc, hlr_mc, hx0_mc, hx1_mc, hx2_mc,
    hx19_mc, hx20_mc, hx21_mc, _, _, _, hx26_mc, hx27_mc, _, hx29_mc, hmem_mc⟩
  rw [hmin] at hx2_mc hx21_mc
  rw [hmin, Nat.sub_self] at hx26_mc
  have hrw_stk : s_mc.mem.RW (s₀.sp - 17024#64) 17024 := by
    rw [hmem_mc]; exact ExpandFrameX.rw_stkX hpre hx.common.frame
  have hrw_esp : s_mc.mem.RW (esp s₀) 496 := by
    rw [hmem_mc]; exact ExpandFrameX.rw_esp hpre hx.common.frame
  have hrw_x2 : s_mc.mem.RW (s₀.readReg64 .x2) okmLen := by
    rw [hmem_mc]; exact ExpandFrameX.rw_x2 hpre hx.common.frame
  have hrw_dst : s_mc.mem.RW (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem :=
    hrw_x2.sub (by have := hpre.okm_len; bv_omega)
  have hrw_src : s_mc.mem.RW (esp s₀ + 208#64) rem := hrw_esp.sub (by bv_omega)
  have hrw_ext : s_mc.mem.RW (s_mc.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_mc]
    change s_mc.mem.RW (esp s₀ - 16384#64) 16384
    exact hrw_stk.sub (by unfold esp; bv_omega)
  have hd_dst_src : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem (esp s₀ + 208#64) rem :=
    (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
      ⟨hrem_pos, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ + 208#64)
      ⟨hrem_pos, by unfold esp; bv_omega⟩
  have hd_dst_ext : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem
      (s_mc.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_mc]
    change DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem (esp s₀ - 16384#64) 16384
    exact (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
      ⟨hrem_pos, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ - 16384#64)
      ⟨by decide, by unfold esp; bv_omega⟩
  have hd_src_ext : DisjointRegions (esp s₀ + 208#64) rem
      (s_mc.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_mc]
    change DisjointRegions (esp s₀ + 208#64) rem (esp s₀ - 16384#64) 16384
    unfold DisjointRegions; bv_omega
  have hc_mc : ExpandCommonX infoPtr info.length okmLen s₀ s_mc :=
    ⟨hstat_mc, hsp_mc, hx29_mc, hx27_mc, hx20_mc,
     by rw [hmem_mc]; exact hx.common.m8_eq,
     by rw [hmem_mc]; exact hx.common.m16_eq,
     by rw [hmem_mc]; exact hx.common.saved,
     by rw [hmem_mc]; exact hx.common.frame⟩
  have hmc := memcpy_stub_runsTo hS.memcpy
    (bs := tNext.take rem)
    hpc_mc hstat_mc hx0_mc hx1_mc
    (by rw [hx2_mc, htake_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    (by rw [htake_len, hmem_mc]; exact hread_rem)
    (by rw [htake_len]; exact hrw_dst)
    (by rw [htake_len]; exact hrw_src)
    hrw_ext
    (by rw [htake_len]; exact hd_dst_src)
    (by rw [htake_len]; exact hd_dst_ext)
    (by rw [htake_len]; exact hd_src_ext)
    (by rw [hsp_mc]; exact esp_aligned hpre.sp_aligned)
  refine hmc.trans fun s₁ hs₁ => ?_
  rcases hs₁ with ⟨hpc₁, hstat₁, hcc₁, _, hdst₁, _, hfr_mc⟩
  rw [hsp_mc, htake_len] at hfr_mc
  rw [htake_len] at hdst₁
  have hoff_lt : dstOff < 2 ^ 64 := by have := hpre.okm_len; omega
  have hc1 : ExpandCommonX infoPtr info.length okmLen s₀ s₁ :=
    ExpandCommonX.of_memcpy_x2_frame hpre hc_mc
      ⟨hrem_pos, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt]; omega⟩
      hstat₁ hcc₁ hfr_mc
  have hleft : s₁.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · refine (hfr_mc.readBytes_eq (hrw_x2.sub (by have := hpre.okm_len; bv_omega)) (fun r hr => ?_)
        (by have := hpre.okm_len; omega)).trans (by rw [hmem_mc]; exact hx.okm_pre)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · unfold DisjointRegions; have := hpre.okm_len; bv_omega
      · change DisjointRegions (esp s₀ - 16384#64) 16384 (s₀.readReg64 .x2) dstOff
        exact (hpre.disj_x2_stack.symm.sub_left (esp s₀ - 16384#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
  have hokm_done : s₁.mem.readBytes (s₀.readReg64 .x2) okmLen = hkdfExpand F prk info okmLen := by
    rw [← hdst, Bytes.readBytes_add s₁.mem (s₀.readReg64 .x2) dstOff rem, hleft, hdst₁, hokm, hdst]
  exact Extract.RunsTo.toE (iter_d_done_tail_x_runsTo hpre (hpc₁.trans hlr_mc) hc1
    ((Extract.CallingConventionPreserved.x19 hcc₁).trans hx19_mc)
    ((Extract.CallingConventionPreserved.x21 hcc₁).trans hx21_mc)
    ((CallingConventionPreserved.x26 hcc₁).trans hx26_mc)
    hokm_done)

private theorem expand_multi_info_runsTo_ro_ext_x (hS : HkdfStubsExt b F ext)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : ExpandPreX (emptyImg b) F prk info infoPtr okmLen (s0Ref b s₀)) :
    RunsToE (tripleRatchetProgAtExt b ext) s₀
      (ExpandPostX F prk info infoPtr okmLen s₀) := by
  have h0 := Extract.RunsTo.toE (seg0_ro_x_runsTo (ext := ext) hpre)
  have h1 := h0.trans fun s hs => Extract.RunsTo.toE (seg1_x_runsTo hpre hs)
  have h2a := h1.trans fun s hs => seg2a_ro_x_runsTo hS hpre hs
  have h2b := h2a.trans fun s hs => Extract.RunsTo.toE (seg2b_x_runsTo hpre hs)
  have hfin1 := h2b.trans fun s hs => fin1_ro_x_runsTo hS hpre hs
  have hloop1 := hfin1.trans fun s hs => seg3_ro_x_runsTo hS hpre hs
  rcases hpre.okm_len with rfl | rfl
  · have hlf1 := iter_to_fin_ro_x_runsTo hS hpre
      (t1_length F prk info) (Or.inl rfl) (Or.inl rfl) (by decide) hloop1
    have hokm64 : t1 F prk info ++ (hmacWith F prk (t1 F prk info ++ info ++ [2#8])).take 32 =
        hkdfExpand F prk info 64 := by
      rw [show hmacWith F prk (t1 F prk info ++ info ++ [2#8]) = t2 F prk info from rfl,
          List.take_of_length_le (by simp), hkdfExpand_64_eq]
    have hdone := hlf1.trans fun s hs =>
      iter_d_done_ro_x_runsTo hS hpre (Or.inl rfl) (Or.inl rfl) rfl hokm64 hs
    exact hdone.trans fun s hs => Extract.RunsTo.toE (epilogue_x_runsTo hpre hs)
  · have hlf1 := iter_to_fin_ro_x_runsTo hS hpre
      (t1_length F prk info) (Or.inl rfl) (Or.inr (Or.inl rfl)) (by decide) hloop1
    have hloop2 := hlf1.trans fun s hs =>
      iter_d_continue_ro_x_runsTo (tNext := t2 F prk info) hS hpre rfl (by decide) rfl hs
    have hlf2 := iter_to_fin_ro_x_runsTo hS hpre
      (t2_length F prk info) (Or.inr rfl) (Or.inr (Or.inr rfl)) (by decide) hloop2
    have hokm80 : (t1 F prk info ++ t2 F prk info) ++
        (hmacWith F prk (t2 F prk info ++ info ++ [3#8])).take 16 =
        hkdfExpand F prk info 80 := by
      rw [show hmacWith F prk (t2 F prk info ++ info ++ [3#8]) = t3 F prk info from rfl,
          hkdfExpand_80_eq]
    have hdone := hlf2.trans fun s hs =>
      iter_d_done_ro_x_runsTo hS hpre (Or.inr rfl) (Or.inr rfl) rfl hokm80 hs
    exact hdone.trans fun s hs => Extract.RunsTo.toE (epilogue_x_runsTo hpre hs)

end SegmentsRO

/-! ## 3. Top-Level `.inImage`-Free `subroutine_ok` for `expand_multi_info` (`64` / `80` B) -/

private theorem fnAddr_hkdfExpandMultiInfoSym (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr hkdfExpandMultiInfoSym =
      b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info") := by
  unfold tripleRatchetProgAtExt hkdfExpandMultiInfoSym
  rw [Program.fnAddr_rebase,
    (ls_lemma% fnOff "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info")]

/-- `.inImage`-free `subroutine_ok` for `expandMultiInfoSpecExt F` on `tripleRatchetProgAtExt b ext`
from `HkdfStubsExt b F ext`. -/
theorem expand_multi_info_ok_ro_ext_base {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hS : HkdfStubsExt b F ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr hkdfExpandMultiInfoSym)
      (expandMultiInfoSpecExt F) := by
  rw [fnAddr_hkdfExpandMultiInfoSym]
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [expandMultiInfoSpecExt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, hokm_len⟩, hsep⟩
  change s0.mem ⊨ (hmacCoreAt F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ memRegion x.okmA x.okmLen ∗
      memRegion (s0.sp - 17024#64) 17024) ∗ R at hsep
  have hb_hm := isBlock_hmacCoreAt F x.hkdfA x.prk [] (by decide)
  have hb_hdr0 := IsBlock.pointsTo64 x.infoHdrA x.infoA
  have hb_hdr8 := IsBlock.pointsTo64 (x.infoHdrA + 8#64) (BitVec.ofNat 64 x.info.length)
  have hb_hdr : IsBlock ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length))
      x.infoHdrA 16
      (fun m => m.read64 x.infoHdrA = x.infoA ∧
        m.read64 (x.infoHdrA + 8#64) = BitVec.ofNat 64 x.info.length) :=
    hb_hdr0.sepConj hb_hdr8 rfl (by decide)
  have hro_info := IsBlockRO.pointsToBytesRO x.infoA x.info (by omega)
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (s0.sp - 17024#64) 17024
  let R_inv : SepProp :=
    hmacCoreAt F x.hkdfA x.prk [] ∗
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗ R
  have hsep_okm_stk_ro : s0.mem ⊨ memRegion x.okmA x.okmLen ∗
      (memRegion (s0.sp - 17024#64) 17024 ∗ ((x.infoA ↦ᵣ x.info) ∗ R_inv)) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 17024#64) 17024 ∗
      (memRegion x.okmA x.okmLen ∗ ((x.infoA ↦ᵣ x.info) ∗ R_inv)) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_hm_stk : s0.mem ⊨ hmacCoreAt F x.hkdfA x.prk [] ∗
      (memRegion (s0.sp - 17024#64) 17024 ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hm_okm : s0.mem ⊨ hmacCoreAt F x.hkdfA x.prk [] ∗
      (memRegion x.okmA x.okmLen ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 17024#64) 17024 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_stk : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (memRegion (s0.sp - 17024#64) 17024 ∗
        (hmacCoreAt F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_okm : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (memRegion x.okmA x.okmLen ∗
        (hmacCoreAt F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 17024#64) 17024 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion (s0.sp - 17024#64) 17024 ∗
        (hmacCoreAt F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
            (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion x.okmA x.okmLen ∗
        (hmacCoreAt F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
            (memRegion (s0.sp - 17024#64) 17024 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hokm_pos : 0 < x.okmLen := by omega
  have hruns : RunsToE (tripleRatchetProgAtExt b ext) s0
      (ExpandPostX F x.prk x.info x.infoA x.okmLen (s0Ref b s0)) := by
    intro hL
    have hb_al : b.toNat % 4 = 0 := hL.aligned
    have h_exp_pre : ExpandPreX (emptyImg b) F x.prk x.info x.infoA x.okmLen (s0Ref b s0) :=
      { frozen := emptyImg_frozenLoaded hb_al (s0Ref b s0)
        symtab_eq := rfl
        pc_eq := hpc
        status := hrun
        x3_eq := hx3
        prk_le := hprk_le
        info_lt := hinfo_lt
        okm_len := hokm_len
        hmac_st := by change HmacSt s0.mem (s0.readReg64 .x0) F x.prk []; rw [hx0]; exact hb_hm.read hsep_hm_stk
        info_ptr := by change s0.mem.read64 (s0.readReg64 .x1) = x.infoA; rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).1
        info_len := by change s0.mem.read64 (s0.readReg64 .x1 + 8#64) = _; rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).2
        info_bytes := hro_info.read hsep_info_stk
        read_info := fun a ha => ⟨hro_info.perm_r hsep_info_stk ha, hro_info.isLazyFree_false hsep_info_stk ha⟩
        read_x0 := by change s0.mem.Readable (s0.readReg64 .x0) 0x90; rw [hx0]; exact Memory.RW.readable (fun a ha => hb_hm.permNoLazy_rw hsep_hm_stk ha)
        read_x1 := by change s0.mem.Readable (s0.readReg64 .x1) 16; rw [hx1]; exact Memory.RW.readable (fun a ha => hb_hdr.permNoLazy_rw hsep_hdr_stk ha)
        rw_x2 := by change RW s0.mem (s0.readReg64 .x2) x.okmLen; rw [hx2]; exact fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk_ro ha
        rw_stack := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
        disj_x2_stack := by change DisjointRegions (s0.readReg64 .x2) _ _ _; rw [hx2]; exact hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk_ro
        disj_x0_stack := by change DisjointRegions (s0.readReg64 .x0) _ _ _; rw [hx0]; exact hb_hm.disjoint hb_stk (by decide) (by decide) hsep_hm_stk
        disj_x0_x2 := by change DisjointRegions (s0.readReg64 .x0) _ (s0.readReg64 .x2) _; rw [hx0, hx2]; exact hb_hm.disjoint hb_okm (by decide) hokm_pos hsep_hm_okm
        disj_x1_stack := by change DisjointRegions (s0.readReg64 .x1) _ _ _; rw [hx1]; exact hb_hdr.disjoint hb_stk (by decide) (by decide) hsep_hdr_stk
        disj_x1_x2 := by change DisjointRegions (s0.readReg64 .x1) _ (s0.readReg64 .x2) _; rw [hx1, hx2]; exact hb_hdr.disjoint hb_okm (by decide) hokm_pos hsep_hdr_okm
        out_info_stk := ro_outside_rw_shared_lb hro_info hb_stk hsep_info_stk
        out_info_x2 := by change ∀ a, _ → OutsideRegion (s0.readReg64 .x2) _ a; rw [hx2]; exact ro_outside_rw_shared_lb hro_info hb_okm hsep_info_okm
        sp_aligned := by simpa [State.spAligned, s0Ref] using hsp }
    exact expand_multi_info_runsTo_ro_ext_x hS h_exp_pre hL
  refine hruns.to_reaches_pc fun sf hpost _ _ htr => ?_
  change ExpandPostX F x.prk x.info x.infoA x.okmLen s0 sf at hpost
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_,
    LibsignalTripleRatchet.CallingConventionPreserved_of_calleeSaved hcallee htr⟩
  dsimp only [expandMultiInfoSpecExt]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExpandFrameX at hframe_sf
  rw [hx2] at hokm_sf hframe_sf
  have h_exp_len : (hkdfExpand F x.prk x.info x.okmLen).length = x.okmLen := by
    rcases hokm_len with h64 | h80
    · rw [h64, Expand.hkdfExpand_64_eq]
      simp [Expand.t1_length, Expand.t2_length]
    · rw [h80, Expand.hkdfExpand_80_eq]
      simp [Expand.t1_length, Expand.t2_length, Expand.t3_length]
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ hkdfExpand F x.prk x.info x.okmLen) ∗
      (memRegion (s0.sp - 17024#64) 17024 ∗ ((x.infoA ↦ᵣ x.info) ∗ R_inv)) :=
    S2FrameRO.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hro_info hsep_okm_stk_ro hframe_sf
      ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  change sf.mem ⊨ (hmacCoreAt F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ (x.okmA ↦ₛ hkdfExpand F x.prk x.info x.okmLen) ∗
      memRegion (s0.sp - 17024#64) 17024) ∗ R
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

/-- `.inImage`-free `subroutine_ok` for `expandMultiInfoSpecExt F` on
`tripleRatchetProgAtExt img.base ext` from `HkdfStubsExt img.base F ext`. -/
theorem expand_multi_info_ok_ro_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hS : HkdfStubsExt img.base F ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExpandMultiInfoSym)
      (expandMultiInfoSpecExt F) :=
  expand_multi_info_ok_ro_ext_base hS

/-- `pqxdhHkdfExpandCellsSpecExt P img 8` (`64` B, `info = INFO_RATCHET`) from `HkdfStubsExt`. -/
theorem pqxdhHkdfExpand_8_ok_of_stubsExt
    {P : CryptoVerification.E2E.Pqxdh.Initiator.Primitives} {C : Crypto}
    {img : Obj.Image} {ext : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (hS : HkdfStubsExt img.base C.F ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExpandMultiInfoSym)
      (pqxdhHkdfExpandCellsSpecExt P img 8) :=
  pqxdhHkdfExpand_8_ok_ext hP (expand_multi_info_ok_ro_ext hS)

/-- `pqxdhHkdfExpandCellsSpecExt P img 10` (`80` B, `info = INFO_MSG_KEYS`) from `HkdfStubsExt`. -/
theorem pqxdhHkdfExpand_10_ok_of_stubsExt
    {P : CryptoVerification.E2E.Pqxdh.Initiator.Primitives} {C : Crypto}
    {img : Obj.Image} {ext : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (hS : HkdfStubsExt img.base C.F ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExpandMultiInfoSym)
      (pqxdhHkdfExpandCellsSpecExt P img 10) :=
  pqxdhHkdfExpand_10_ok_ext hP (expand_multi_info_ok_ro_ext hS)

end CryptoVerification.E2E.Pqxdh.ResponderCore
