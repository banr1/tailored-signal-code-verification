/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfStubsExt
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfFinGenExt
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLong
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCallees -- shake: keep

/-!
# `.inImage`-Free `expand_multi_info` (`okmLen = 96`, `info.length = 46`): Preconditions and Block 1

Defines `ExpandPre96_46X`, `S2FrameRO` preservation helpers, multi-block loop cut-point structures,
and Block 1 (`T(1)`) segment proofs for `expand_multi_info` on `tripleRatchetProgAtExt b ext` at
`expandMultiInfoStackExt` (`17024` B).
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

attribute [local simp, local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint
  sp_sub_496_eq_esp sp_add_neg496_eq_esp esp_add_496_sub_496
  read8_write64_120_127 CryptoVerification.LibsignalTripleRatchet.Expand.truncate8_ofNat64
  bv32_zero_add bv8_zero_add
  t1_length t2_length t3_length

namespace HkdfLongExt

theorem runsTo_toE {prog : Program} {s₀ : State} {P : State → Prop}
    (h : RunsTo prog s₀ P) : RunsToE prog s₀ P :=
  fun hL => by
    obtain ⟨sf, hst, htr, hP, hLf⟩ := h hL
    exact ⟨sf, hst, htr, hP, hLf⟩

theorem memsetStep_of_stubs {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)} (hS : HkdfStubsExt b F ext) :
    MemsetStepExt b ext :=
  fun hpc hstat hx0 hx1 hx2 hrw_dst hrw_stk hd_dst_stk hsp_al =>
    memset_stub_runsTo hS.memset hpc hstat hx0 hx1 hx2 hrw_dst hrw_stk hd_dst_stk hsp_al

theorem compressOneStep_of_stubs {b : BitVec 64} {F : ShaCompress}
    {ext : String → Option (State → State)} (hS : HkdfStubsExt b F ext) :
    CompressOneStepExt b F ext :=
  fun hpc hstat hx0 hx1 hx2 hst hblk hrw_st hrw_blk hrw_stk hd1 hd2 hd3 hsp_al =>
    compress256_one_stub_runsTo hS.compress256 (by decide)
      hpc hstat hx0 hx1 hx2 hst hblk hrw_st hrw_blk hrw_stk hd1 hd2 hd3 hsp_al

/-- Enlarging the read-only source region preserves `S2FrameRO`. -/
theorem S2FrameRO_widen_ro {ro₁ ro₂ : BitVec 64} {len₁ len₂ : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (h : S2FrameRO ro₁ len₁ m₁ m₂ regs)
    (hsub : ∀ a, OutsideRegion ro₂ len₂ a → OutsideRegion ro₁ len₁ a) :
    S2FrameRO ro₂ len₂ m₁ m₂ regs :=
  ⟨h.1, ⟨⟨fun a ha hnl => h.2.1.1.1 a (hsub a ha) hnl,
          fun a ha hrw => h.2.1.1.2 a (hsub a ha) hrw⟩, h.2.1.2⟩, h.2.2⟩

/-! ## Precondition `ExpandPre96_46X` and Frame Helpers -/

/-- `.inImage`-free preconditions of `expand_multi_info` for `okmLen = 96`, `info.length = 46`,
at `expandMultiInfoStackExt = 17024` B stack. -/
structure ExpandPre96_46X (b : BitVec 64) (F : ShaCompress)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (s₀ : State) : Prop where
  pc_eq         : s₀.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info")
  status        : s₀.status = .Running
  x3_eq         : s₀.readReg64 .x3 = 96#64
  prk_le        : prk.length ≤ 64
  info_len_eq   : info.length = 46
  hmac_st       : HmacSt s₀.mem (s₀.readReg64 .x0) F prk []
  info_ptr      : s₀.mem.read64 (s₀.readReg64 .x1) = infoPtr
  info_len      : s₀.mem.read64 (s₀.readReg64 .x1 + 8#64) = 46#64
  info_bytes    : s₀.mem.readBytes infoPtr info.length = info
  read_info     : s₀.mem.Readable infoPtr info.length
  read_x0       : s₀.mem.Readable (s₀.readReg64 .x0) 0x90
  read_x1       : s₀.mem.Readable (s₀.readReg64 .x1) 16
  rw_x2         : RW s₀.mem (s₀.readReg64 .x2) 96
  rw_stack      : RW s₀.mem (s₀.sp - 17024#64) 17024
  disj_x2_stack : DisjointRegions (s₀.readReg64 .x2) 96 (s₀.sp - 17024#64) 17024
  disj_x0_stack : DisjointRegions (s₀.readReg64 .x0) 0x90 (s₀.sp - 17024#64) 17024
  disj_x0_x2    : DisjointRegions (s₀.readReg64 .x0) 0x90 (s₀.readReg64 .x2) 96
  disj_x1_stack : DisjointRegions (s₀.readReg64 .x1) 16 (s₀.sp - 17024#64) 17024
  disj_x1_x2    : DisjointRegions (s₀.readReg64 .x1) 16 (s₀.readReg64 .x2) 96
  out_info_stk  : ∀ a, InRegion infoPtr info.length a → OutsideRegion (s₀.sp - 17024#64) 17024 a
  out_info_x2   : ∀ a, InRegion infoPtr info.length a → OutsideRegion (s₀.readReg64 .x2) 96 a
  sp_aligned    : (s₀.sp &&& 15#64) = 0#64

namespace ExpandPre96_46X

variable {b : BitVec 64} {F : ShaCompress}
  {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ : State} {m : Memory}

/-- Project `ExpandPre96_46X` (`17024` B stack) to `ExpandPre96_46` (`640` B stack) for shared
register-vs-stack read/write disjointness helpers. -/
theorem toExpandPre96_46 (hpre : ExpandPre96_46X b F prk info infoPtr s₀) :
    ExpandPre96_46 b F prk info infoPtr s₀ :=
  have hsub640 : 0 < 640 ∧ ((s₀.sp - 640#64) - (s₀.sp - 17024#64)).toNat + 640 ≤ 17024 := by
    have heq : (s₀.sp - 640#64) - (s₀.sp - 17024#64) = 16384#64 := by bv_lin
    rw [heq]; decide
  { pc_eq         := hpre.pc_eq
    status        := hpre.status
    x3_eq         := hpre.x3_eq
    prk_le        := hpre.prk_le
    info_len_eq   := hpre.info_len_eq
    hmac_st       := hpre.hmac_st
    info_ptr      := hpre.info_ptr
    info_len      := hpre.info_len
    info_bytes    := hpre.info_len_eq ▸ hpre.info_bytes
    read_x0       := hpre.read_x0
    read_x1       := hpre.read_x1
    rw_x2         := hpre.rw_x2
    rw_stack      := hpre.rw_stack.sub hsub640.2
    disj_x2_stack := hpre.disj_x2_stack.sub_right _ hsub640
    disj_x0_stack := hpre.disj_x0_stack.sub_right _ hsub640
    disj_x0_x2    := hpre.disj_x0_x2
    disj_x1_stack := hpre.disj_x1_stack.sub_right _ hsub640
    disj_x1_x2    := hpre.disj_x1_x2
    out_info_stk  := fun a ha => by
      have hout := hpre.out_info_stk a (hpre.info_len_eq.symm ▸ ha)
      simp only [OutsideRegion] at hout ⊢
      bv_omega
    out_info_x2   := fun a ha => hpre.out_info_x2 a (hpre.info_len_eq.symm ▸ ha)
    sp_aligned    := hpre.sp_aligned }

theorem rw_stkX (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hf : ExpandFrameX infoPtr info.length 96 s₀ m) : m.RW (s₀.sp - 17024#64) 17024 :=
  hf.rw_of_rw _ _ hpre.out_info_stk hpre.rw_stack

theorem rw_esp (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hf : ExpandFrameX infoPtr info.length 96 s₀ m) : m.RW (esp s₀) 496 := by
  have hrw := hpre.rw_stkX hf; unfold esp; exact hrw.sub (by bv_omega)

theorem rw_x2_frame (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hf : ExpandFrameX infoPtr info.length 96 s₀ m) : m.RW (s₀.readReg64 .x2) 96 :=
  hf.rw_of_rw _ _ hpre.out_info_x2 hpre.rw_x2

theorem readable_info (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hf : ExpandFrameX infoPtr info.length 96 s₀ m) : m.Readable infoPtr info.length :=
  hf.readable_of_readable _ _ hpre.read_info

theorem readable_x0 (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hf : ExpandFrameX infoPtr info.length 96 s₀ m) : m.Readable (s₀.readReg64 .x0) 0x90 :=
  hf.readable_of_readable _ _ hpre.read_x0

theorem readable_x1 (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hf : ExpandFrameX infoPtr info.length 96 s₀ m) : m.Readable (s₀.readReg64 .x1) 16 :=
  hf.readable_of_readable _ _ hpre.read_x1

theorem rw_extStack {s : State} (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hf : ExpandFrameX infoPtr info.length 96 s₀ s.mem) (hsp : s.sp = esp s₀) :
    s.mem.RW (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
  rw [hsp]; change s.mem.RW (esp s₀ - 16384#64) 16384
  exact (hpre.rw_stkX hf).sub (by unfold esp; bv_omega)

theorem disj_esp_extStack {s : State} {off : BitVec 64} {sz : ℕ}
    (hsp : s.sp = esp s₀) (hoff : 0 < sz ∧ off.toNat + sz ≤ 496) :
    DisjointRegions (esp s₀ + off) sz (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
  rw [hsp]; change DisjointRegions (esp s₀ + off) sz (esp s₀ - 16384#64) 16384
  unfold DisjointRegions; bv_omega

theorem hmac_x0 (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hf : ExpandFrameX infoPtr info.length 96 s₀ m) : HmacSt m (s₀.readReg64 .x0) F prk [] := by
  have hd : ∀ r ∈ [(s₀.readReg64 .x2, 96), (s₀.sp - 17024#64, 17024)],
      DisjointRegions r.1 r.2 (s₀.readReg64 .x0) 0x90 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl; exacts [hpre.disj_x0_x2.symm, hpre.disj_x0_stack.symm]
  rcases hpre.hmac_st with ⟨hlen, _, hpos, hin, hcnt1, hout, hcnt2⟩
  refine ⟨hlen, rfl,
    (hf.1 _ (hpre.read_x0 _ (by unfold InRegion; bv_omega)).1
      (hpre.read_x0 _ (by unfold InRegion; bv_omega)).2
      (fun r hr => (hd r hr).outside (by unfold InRegion; bv_omega) (by decide))).trans hpos,
    (hf.readBytes_eq_of_readable (readable_sub hpre.read_x0 (by bv_omega))
      (fun r hr => (hd r hr).sub_right _ ⟨by decide, by bv_omega⟩) (by decide)).trans hin,
    (hf.read64_eq_of_readable (readable_sub hpre.read_x0 (by bv_omega))
      (fun r hr => (hd r hr).sub_right _ ⟨by decide, by bv_omega⟩)).trans hcnt1,
    (hf.readBytes_eq_of_readable (readable_sub hpre.read_x0 (by bv_omega))
      (fun r hr => (hd r hr).sub_right _ ⟨by decide, by bv_omega⟩) (by decide)).trans hout,
    (hf.read64_eq_of_readable (readable_sub hpre.read_x0 (by bv_omega))
      (fun r hr => (hd r hr).sub_right _ ⟨by decide, by bv_omega⟩)).trans hcnt2⟩

theorem info_ptr_eq (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hf : ExpandFrameX infoPtr info.length 96 s₀ m) : m.read64 (s₀.readReg64 .x1) = infoPtr := by
  rw [hf.read64_eq_of_readable (readable_sub hpre.read_x1 (by bv_omega))]; · exact hpre.info_ptr
  intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hpre.disj_x1_x2.symm.sub_right _ ⟨by decide, by bv_omega⟩
  · exact hpre.disj_x1_stack.symm.sub_right _ ⟨by decide, by bv_omega⟩

theorem info_len_eq_46 (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hf : ExpandFrameX infoPtr info.length 96 s₀ m) :
    m.read64 (s₀.readReg64 .x1 + 8#64) = 46#64 := by
  rw [hf.read64_eq_of_readable (readable_sub hpre.read_x1 (by bv_omega))]; · exact hpre.info_len
  intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hpre.disj_x1_x2.symm.sub_right _ ⟨by decide, by bv_omega⟩
  · exact hpre.disj_x1_stack.symm.sub_right _ ⟨by decide, by bv_omega⟩

theorem info_bytes_eq (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hf : ExpandFrameX infoPtr info.length 96 s₀ m) : m.readBytes infoPtr info.length = info := by
  refine (List.ext_getElem (by simp) fun i h1 h2 => ?_).trans hpre.info_bytes
  rw [Bytes.readBytes_getElem _ _ _ i h1, Bytes.readBytes_getElem _ _ _ i h2]
  have hi : i < info.length := by simpa using h1
  have hin : InRegion infoPtr info.length (infoPtr + BitVec.ofNat 64 i) :=
    inRegion_base_add infoPtr info.length i hi (by have := hpre.info_len_eq; omega)
  refine hf.1 _ (hpre.read_info _ hin).1 (hpre.read_info _ hin).2 (fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl; exacts [hpre.out_info_x2 _ hin, hpre.out_info_stk _ hin]

theorem out_info_esp_off (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    {off : BitVec 64} {sz : ℕ} (hoff : off.toNat + sz ≤ 496) :
    ∀ a, InRegion infoPtr info.length a → OutsideRegion (esp s₀ + off) sz a := by
  intro a ha; have hout := hpre.out_info_stk a ha; unfold OutsideRegion esp at *; bv_omega

theorem out_info_extStack (hpre : ExpandPre96_46X b F prk info infoPtr s₀) :
    ∀ a, InRegion infoPtr info.length a →
      OutsideRegion (esp s₀ - BitVec.ofNat 64 extHookStack) extHookStack a := by
  intro a ha; have hout := hpre.out_info_stk a ha
  change OutsideRegion (esp s₀ - 16384#64) 16384 a; unfold OutsideRegion esp at *; bv_omega

theorem okm_of_s2frameRO_esp {m₁ m₂ : Memory} {off : BitVec 64} {sz dstOff : ℕ}
    {okmSoFar : List (BitVec 8)}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hf : ExpandFrameX infoPtr info.length 96 s₀ m₁)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ 496) (hdst : dstOff ≤ 96)
    (hfr : S2FrameRO infoPtr info.length m₁ m₂
      [(esp s₀ + off, sz), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hokm : m₁.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar) :
    m₂.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
  by_cases h0 : dstOff = 0
  · subst h0; exact hokm
  · refine (hfr.readBytes_eq ((hpre.rw_x2_frame hf).sub (by bv_omega)) (fun r hr => ?_)
      (by omega)).trans hokm
    have hd_stk : DisjointRegions (s₀.sp - 17024#64) 17024 (s₀.readReg64 .x2) dstOff :=
      hpre.disj_x2_stack.symm.sub_right (s₀.readReg64 .x2) ⟨by omega, by bv_omega⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd_stk.sub_left (esp s₀ + off) ⟨hoff.1, by unfold esp; bv_omega⟩
    · change DisjointRegions (esp s₀ - 16384#64) 16384 (s₀.readReg64 .x2) dstOff
      exact hd_stk.sub_left (esp s₀ - 16384#64) ⟨by decide, by unfold esp; bv_omega⟩

theorem fin_side_conditions_x {s : State} (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hf : ExpandFrameX infoPtr info.length 96 s₀ s.mem) :
    RW s.mem (esp s₀ + 208#64) 32 ∧ RW s.mem (esp s₀ + 240#64) 0x90 ∧
    RW s.mem (esp s₀ - 16528#64) 16528 ∧
    DisjointRegions (esp s₀ + 208#64) 32 (esp s₀ + 240#64) 0x90 ∧
    DisjointRegions (esp s₀ + 208#64) 32 (esp s₀ - 16528#64) 16528 ∧
    DisjointRegions (esp s₀ + 240#64) 0x90 (esp s₀ - 16528#64) 16528 := by
  have hrw_stack := hpre.rw_stkX hf; have hrw_esp := hpre.rw_esp hf
  refine ⟨hrw_esp.sub (by bv_omega), hrw_esp.sub (by bv_omega),
    hrw_stack.sub (by unfold esp; bv_omega), by unfold DisjointRegions; bv_omega,
    by unfold DisjointRegions esp at *; bv_omega, by unfold DisjointRegions esp at *; bv_omega⟩

theorem common_of_fin_frame_x {s s' : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hc : ExpandCommonX infoPtr info.length 96 s₀ s) (hstat : s'.status = .Running)
    (hcc : CallingConventionPreserved s s')
    (hfr : S2Frame s.mem s'.mem
      [(esp s₀ + 208#64, 32), (esp s₀ + 240#64, 0x90), (esp s₀ - 16528#64, 16528)]) :
    ExpandCommonX infoPtr info.length 96 s₀ s' := by
  have hrw_esp := hpre.rw_esp hc.frame
  have hd_low : ∀ r ∈ [(esp s₀ + 208#64, (32 : ℕ)), (esp s₀ + 240#64, 0x90), (esp s₀ - 16528#64, 16528)],
      DisjointRegions r.1 r.2 (esp s₀) 32 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions esp; bv_omega)
  have hd_saved : ∀ r ∈ [(esp s₀ + 208#64, (32 : ℕ)), (esp s₀ + 240#64, 0x90), (esp s₀ - 16528#64, 16528)],
      DisjointRegions r.1 r.2 (esp s₀ + 400#64) 96 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions esp; bv_omega)
  exact ⟨hstat, (Extract.CallingConventionPreserved.sp_eq hcc).trans hc.sp_eq,
    (Extract.CallingConventionPreserved.x29 hcc).trans hc.x29_eq,
    (Extract.CallingConventionPreserved.x27 hcc).trans hc.x27_eq,
    (Extract.CallingConventionPreserved.x20 hcc).trans hc.x20_eq,
    (hfr.read64_eq (hrw_esp.sub (by bv_omega))
      (fun r hr => (hd_low r hr).sub_right _ ⟨by decide, by bv_omega⟩)).trans hc.m8_eq,
    (hfr.read64_eq (hrw_esp.sub (by bv_omega))
      (fun r hr => (hd_low r hr).sub_right _ ⟨by decide, by bv_omega⟩)).trans hc.m16_eq,
    ExpandSaved_of_s2frame_disj hc.saved hrw_esp hfr hd_saved,
    ExpandFrameX.of_fin_frame_x hc.frame hfr⟩

theorem common_of_s2frameRO_esp {s s' : State} {off : BitVec 64} {sz : ℕ}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hc : ExpandCommonX infoPtr info.length 96 s₀ s)
    (hoff : 32 ≤ off.toNat ∧ off.toNat + sz ≤ 300) (hstat : s'.status = .Running)
    (hcc : CallingConventionPreserved s s')
    (hfr : S2FrameRO infoPtr info.length s.mem s'.mem
      [(esp s₀ + off, sz), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    ExpandCommonX infoPtr info.length 96 s₀ s' := by
  have hrw_esp := hpre.rw_esp hc.frame
  have hd_low : ∀ r ∈ [(esp s₀ + off, sz), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
      DisjointRegions r.1 r.2 (esp s₀) 32 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold DisjointRegions; bv_omega
    · change DisjointRegions (esp s₀ - 16384#64) 16384 (esp s₀) 32; unfold DisjointRegions; bv_omega
  have hd_saved : ∀ r ∈ [(esp s₀ + off, sz), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
      DisjointRegions r.1 r.2 (esp s₀ + 400#64) 96 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold DisjointRegions; bv_omega
    · change DisjointRegions (esp s₀ - 16384#64) 16384 (esp s₀ + 400#64) 96
      unfold DisjointRegions; bv_omega
  have hframe' : ExpandFrameX infoPtr info.length 96 s₀ s'.mem := by
    refine hc.frame.trans (hfr.mono fun a ha r hr => ?_)
    have hstack := ha (s₀.sp - 17024#64, 17024) (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold OutsideRegion esp at *; bv_omega
    · change OutsideRegion (esp s₀ - 16384#64) 16384 a; unfold OutsideRegion esp at *; bv_omega
  exact ⟨hstat, (Extract.CallingConventionPreserved.sp_eq hcc).trans hc.sp_eq,
    (Extract.CallingConventionPreserved.x29 hcc).trans hc.x29_eq,
    (Extract.CallingConventionPreserved.x27 hcc).trans hc.x27_eq,
    (Extract.CallingConventionPreserved.x20 hcc).trans hc.x20_eq,
    (hfr.read64_eq (hrw_esp.sub (by bv_omega))
      (fun r hr => (hd_low r hr).sub_right _ ⟨by decide, by bv_omega⟩)).trans hc.m8_eq,
    (hfr.read64_eq (hrw_esp.sub (by bv_omega))
      (fun r hr => (hd_low r hr).sub_right _ ⟨by decide, by bv_omega⟩)).trans hc.m16_eq,
    ExpandSaved_of_s2frameRO_disj hc.saved hrw_esp hfr hd_saved, hframe'⟩

theorem common_of_s2frame_esp {s s' : State} {off : BitVec 64} {sz : ℕ}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hc : ExpandCommonX infoPtr info.length 96 s₀ s)
    (hoff : 32 ≤ off.toNat ∧ off.toNat + sz ≤ 300) (hstat : s'.status = .Running)
    (hcc : CallingConventionPreserved s s')
    (hfr : S2Frame s.mem s'.mem
      [(esp s₀ + off, sz), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    ExpandCommonX infoPtr info.length 96 s₀ s' :=
  hpre.common_of_s2frameRO_esp hc hoff hstat hcc (S2FrameRO.of_s2frame hfr)

theorem common_of_memcpy_x2_frame {s s' : State} {off : BitVec 64} {sz : ℕ}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hc : ExpandCommonX infoPtr info.length 96 s₀ s)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ 96) (hstat : s'.status = .Running)
    (hcc : CallingConventionPreserved s s')
    (hfr : S2Frame s.mem s'.mem
      [(s₀.readReg64 .x2 + off, sz), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    ExpandCommonX infoPtr info.length 96 s₀ s' := by
  have hrw_esp := hpre.rw_esp hc.frame
  have hd_x2_esp : DisjointRegions (s₀.readReg64 .x2 + off) sz (esp s₀) 496 := by
    have hd1 := hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + off)
      ⟨hoff.1, by have := hoff.2; bv_omega⟩
    unfold esp; exact hd1.sub_right (s₀.sp - 496#64) ⟨by decide, by bv_omega⟩
  have hd_low : ∀ r ∈ [(s₀.readReg64 .x2 + off, sz), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
      DisjointRegions r.1 r.2 (esp s₀) 32 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd_x2_esp.sub_right (esp s₀) ⟨by decide, by bv_omega⟩
    · change DisjointRegions (esp s₀ - 16384#64) 16384 (esp s₀) 32; unfold DisjointRegions; bv_omega
  have hd_saved : ∀ r ∈ [(s₀.readReg64 .x2 + off, sz), (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)],
      DisjointRegions r.1 r.2 (esp s₀ + 400#64) 96 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd_x2_esp.sub_right (esp s₀ + 400#64) ⟨by decide, by bv_omega⟩
    · change DisjointRegions (esp s₀ - 16384#64) 16384 (esp s₀ + 400#64) 96
      unfold DisjointRegions; bv_omega
  exact ⟨hstat, (Extract.CallingConventionPreserved.sp_eq hcc).trans hc.sp_eq,
    (Extract.CallingConventionPreserved.x29 hcc).trans hc.x29_eq,
    (Extract.CallingConventionPreserved.x27 hcc).trans hc.x27_eq,
    (Extract.CallingConventionPreserved.x20 hcc).trans hc.x20_eq,
    (hfr.read64_eq (hrw_esp.sub (by bv_omega))
      (fun r hr => (hd_low r hr).sub_right _ ⟨by decide, by bv_omega⟩)).trans hc.m8_eq,
    (hfr.read64_eq (hrw_esp.sub (by bv_omega))
      (fun r hr => (hd_low r hr).sub_right _ ⟨by decide, by bv_omega⟩)).trans hc.m16_eq,
    ExpandSaved_of_s2frame_disj hc.saved hrw_esp hfr hd_saved,
    ExpandFrameX.of_memcpy_x2_frame hc.frame hoff.2 hfr⟩

theorem common_of_write64_esp0_and_low64 {s s' : State} {v : BitVec 64} {m_mid : Memory}
    (hc : ExpandCommonX infoPtr info.length 96 s₀ s) (hstat : s'.status = .Running)
    (hsp : s'.sp = esp s₀) (hx29 : s'.readReg64 .x29 = esp s₀ + 400#64)
    (hx27 : s'.readReg64 .x27 = esp s₀ + 64#64) (hx20 : s'.readReg64 .x20 = s₀.readReg64 .x0)
    (hmid : AgreesOutside s.mem m_mid (esp s₀ + 64#64) 64)
    (hmem' : s'.mem = m_mid.write64 (esp s₀) v) :
    ExpandCommonX infoPtr info.length 96 s₀ s' := by
  have hc_mid : ExpandCommonX infoPtr info.length 96 s₀ (s.setMem m_mid) :=
    ExpandCommonX.of_agreesOutside_low32 (off := 64#64) (sz := 64) hc
      (by rw [State.status_setMem]; exact hc.status) (by rw [State.sp_setMem]; exact hc.sp_eq)
      (by rw [State.readReg64_setMem]; exact hc.x29_eq)
      (by rw [State.readReg64_setMem]; exact hc.x27_eq)
      (by rw [State.readReg64_setMem]; exact hc.x20_eq)
      (by rw [Expand.mem_setMem]; exact hmid) (by decide)
  have hA0 : AgreesOutside m_mid s'.mem (esp s₀ + 0#64) 8 := by
    rw [hmem', BitVec.add_zero]
    exact (AgreesOutside.rfl' m_mid (esp s₀) 8).write64 (by bv_omega) (by decide)
  exact ⟨hstat, hsp, hx29, hx27, hx20,
    (hA0.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc_mid.m8_eq,
    (hA0.read64_eq (by unfold DisjointRegions; bv_omega)).trans hc_mid.m16_eq,
    ExpandSaved.of_agreesOutside_low hc_mid.saved hA0 (by decide),
    ExpandFrameX.of_agreesOutside_esp hc_mid.frame hA0 (by decide)⟩

end ExpandPre96_46X

/-! ## `HmacSt` and `HmacStGen` Post-`S2FrameRO` Helpers -/

theorem hmacSt_of_memcpyRO_46 {m₀ m₁ : Memory} {s₀ : State} {infoPtr : BitVec 64}
    {F : ShaCompress} {key info : List (BitVec 8)}
    (h₀ : HmacSt m₀ (esp s₀ + 64#64) F key [])
    (hrw_esp : m₀.RW (esp s₀) 496)
    (hinfo : info.length = 46)
    (hfr : S2FrameRO infoPtr info.length m₀ m₁
      [(esp s₀ + 64#64, info.length),
       (esp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    HmacSt m₁ (esp s₀ + 64#64) F key [] := by
  let a := esp s₀ + 64#64
  rcases h₀ with ⟨hlen, _, hpos, hin, hcnt1, hout, hcnt2⟩
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
  refine ⟨hlen, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · refine (hfr.1 (a + 0x3f#64) (hrw_esp.readable _ (by unfold InRegion; dsimp [a]; bv_omega)).1
      (hrw_esp.readable _ (by unfold InRegion; dsimp [a]; bv_omega)).2
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

theorem hmacSt_of_counter_writes_46 {m₁ : Memory} {s₀ : State}
    {F : ShaCompress} {key info : List (BitVec 8)}
    (h₀ : HmacSt m₁ (esp s₀ + 64#64) F key [])
    (hinfo_m₁ : m₁.readBytes (esp s₀ + 64#64) 46 = info) (hinfo : info.length = 46) :
    HmacSt ((((m₁.write8 (esp s₀ + 127#64) 46#8).write8 (esp s₀ + 240#64) 1#8).write8
      (esp s₀ + 110#64) 1#8).write8 (esp s₀ + 127#64) 47#8)
      (esp s₀ + 64#64) F key (info ++ [1#8]) := by
  let a := esp s₀ + 64#64
  let m₂ := (((m₁.write8 (a + 63#64) 46#8).write8 (a + 176#64) 1#8).write8
    (a + 46#64) 1#8).write8 (a + 63#64) 47#8
  rw [show esp s₀ + 127#64 = a + 63#64 by dsimp [a]; bv_lin,
      show esp s₀ + 240#64 = a + 176#64 by dsimp [a]; bv_lin,
      show esp s₀ + 110#64 = a + 46#64 by dsimp [a]; bv_lin]
  change HmacSt m₂ a F key (info ++ [1#8])
  rcases h₀ with ⟨_, _, _, hin, hcnt1, hout, hcnt2⟩
  have hlen : (info ++ [1#8]).length = 47 := by simp [hinfo]
  have hag_w : AgreesOutside m₁ m₂ (a + 46#64) 177 := by
    dsimp only [m₂]
    refine AgreesOutside.write8 (AgreesOutside.write8 (AgreesOutside.write8 ?_
      (by simp only [InRegion]; bv_omega)) (by simp only [InRegion]; bv_omega))
      (by simp only [InRegion]; bv_omega)
    exact AgreesOutside.write8 (AgreesOutside.rfl' _ _ _) (by simp only [InRegion]; bv_omega)
  have h_ag_st : ∀ (off : BitVec 64) (sz : ℕ), 0 < sz → 64 ≤ off.toNat → off.toNat + sz ≤ 144 →
      m₂.readBytes (a + off) sz = m₁.readBytes (a + off) sz := by
    intro off sz hsz0 h64 h144; dsimp only [m₂]
    rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
          (by unfold DisjointRegions; bv_omega) (by omega),
        (AgreesOutside.rfl' _ (a + 46#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
          (by unfold DisjointRegions; bv_omega) (by omega),
        (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
          (by unfold DisjointRegions; bv_omega) (by omega),
        (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
          (by unfold DisjointRegions; bv_omega) (by omega)]
  have h_ag_64 : ∀ (off : BitVec 64), 64 ≤ off.toNat → off.toNat + 8 ≤ 144 →
      m₂.read64 (a + off) = m₁.read64 (a + off) := by
    intro off h64 h144; dsimp only [m₂]
    rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 46#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega)]
  refine ⟨by omega, ?_, ?_,
    (h_ag_st 0x40#64 32 (by decide) (by decide) (by decide)).trans hin,
    (h_ag_64 0x60#64 (by decide) (by decide)).trans hcnt1,
    (h_ag_st 0x68#64 32 (by decide) (by decide) (by decide)).trans hout,
    (h_ag_64 0x88#64 (by decide) (by decide)).trans hcnt2⟩
  · have h_info : m₂.readBytes a 46 = info :=
      (hag_w.readBytes_eq (by unfold DisjointRegions; dsimp [a]; bv_omega) (by decide)).trans hinfo_m₁
    rw [hlen, show (47 : ℕ) = 46 + 1 from rfl, Bytes.readBytes_add m₂ a 46 1, h_info]
    dsimp only [Memory.readBytes, m₂]
    rw [Memory.read8_write8_ne (by bv_omega), Memory.read8_write8_same]
  · rw [hlen, show (0x3f#64 : BitVec 64) = 63#64 from rfl]; exact Memory.read8_write8_same _ _ _

theorem hmacStGen_of_counter_writes_14 {m₁ : Memory} {s₀ : State}
    {F : ShaCompress} {key tPrev info : List (BitVec 8)} {i : ℕ}
    (ht_len : tPrev.length = 32) (hinfo_len : info.length = 46)
    (hdrop_m₁ : m₁.readBytes (esp s₀ + 64#64) 14 = info.drop 32)
    (hist : m₁.readBytes (esp s₀ + 128#64) 32 =
      shaStateBytes (F (hmacInnerInit F key) (tPrev ++ info.take 32)))
    (hcnt1 : m₁.read64 (esp s₀ + 160#64) = 2#64)
    (hout : m₁.readBytes (esp s₀ + 168#64) 32 = shaStateBytes (hmacOuterInit F key))
    (hcnt2 : m₁.read64 (esp s₀ + 200#64) = 1#64) :
    let c := BitVec.ofNat 8 (i + 1)
    let m₂ :=
      ((m₁.write8 (esp s₀ + 240#64) c).write8 (esp s₀ + 78#64) c).write8 (esp s₀ + 127#64) 15#8
    HmacStGen m₂ (esp s₀ + 64#64) F key (tPrev ++ info.take 32) (info.drop 32 ++ [c]) := by
  intro c m₂
  have hblk_len : (tPrev ++ info.take 32).length = 64 := by simp [ht_len, hinfo_len]
  have hdrop_len : (info.drop 32).length = 14 := by simp [hinfo_len]
  have hrem_len : (info.drop 32 ++ [c]).length = 15 := by simp [hdrop_len]
  have hag_w : AgreesOutside m₁ m₂ (esp s₀ + 78#64) 163 := by
    dsimp only [m₂]
    exact AgreesOutside.write8 (AgreesOutside.write8
      (AgreesOutside.write8 (AgreesOutside.rfl' _ _ _) (by simp only [InRegion]; bv_omega))
      (by simp only [InRegion]; bv_omega)) (by simp only [InRegion]; bv_omega)
  have h_ag_st : ∀ (off : BitVec 64) (sz : ℕ), 0 < sz → 128 ≤ off.toNat → off.toNat + sz ≤ 208 →
      m₂.readBytes (esp s₀ + off) sz = m₁.readBytes (esp s₀ + off) sz := by
    intro off sz hsz0 h128 h208; dsimp only [m₂]
    rw [(AgreesOutside.rfl' _ (esp s₀ + 127#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
          (by unfold DisjointRegions; bv_omega) (by omega),
        (AgreesOutside.rfl' _ (esp s₀ + 78#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
          (by unfold DisjointRegions; bv_omega) (by omega),
        (AgreesOutside.rfl' _ (esp s₀ + 240#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
          (by unfold DisjointRegions; bv_omega) (by omega)]
  have h_ag_64 : ∀ (off : BitVec 64), 128 ≤ off.toNat → off.toNat + 8 ≤ 208 →
      m₂.read64 (esp s₀ + off) = m₁.read64 (esp s₀ + off) := by
    intro off h128 h208; dsimp only [m₂]
    rw [(AgreesOutside.rfl' _ (esp s₀ + 127#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (esp s₀ + 78#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (esp s₀ + 240#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega)]
  refine ⟨by rw [hblk_len], by rw [hblk_len]; decide, by rw [hrem_len]; decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrem_len, show (15 : ℕ) = 14 + 1 from rfl, Bytes.readBytes_add m₂ (esp s₀ + 64#64) 14 1,
        show esp s₀ + 64#64 + BitVec.ofNat 64 14 = esp s₀ + 78#64 by bv_lin,
        (hag_w.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans hdrop_m₁]
    dsimp only [Memory.readBytes, m₂]
    rw [Memory.read8_write8_ne (by bv_omega), Memory.read8_write8_same]
  · rw [hrem_len, show esp s₀ + 64#64 + 0x3f#64 = esp s₀ + 127#64 by bv_lin]
    exact Memory.read8_write8_same _ _ _
  · rw [show esp s₀ + 64#64 + 0x40#64 = esp s₀ + 128#64 by bv_lin, chunks64_single hblk_len, List.foldl]
    exact (h_ag_st 128#64 32 (by decide) (by decide) (by decide)).trans hist
  · rw [show esp s₀ + 64#64 + 0x60#64 = esp s₀ + 160#64 by bv_lin, hblk_len]
    exact (h_ag_64 160#64 (by decide) (by decide)).trans hcnt1
  · rw [show esp s₀ + 64#64 + 0x68#64 = esp s₀ + 168#64 by bv_lin]
    exact (h_ag_st 168#64 32 (by decide) (by decide) (by decide)).trans hout
  · rw [show esp s₀ + 64#64 + 0x88#64 = esp s₀ + 200#64 by bv_lin]
    exact (h_ag_64 200#64 (by decide) (by decide)).trans hcnt2

/-! ## Multi-Block Loop Cut-Point Structures -/

/-- Cut `LoopA2_96X` at `memcpy(esp + 96, infoPtr, 32)` (`lr = entry + 892`). -/
structure StateLoopA2_96X (b : BitVec 64) (F : ShaCompress)
    (prk info tPrev okmSoFar : List (BitVec 8)) (infoPtr : BitVec 64)
    (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "memcpy")
  common  : ExpandCommonX infoPtr info.length 96 s₀ s
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 892)
  x0_eq   : s.readReg64 .x0 = esp s₀ + 96#64
  x1_eq   : s.readReg64 .x1 = infoPtr
  x2_eq   : s.readReg64 .x2 = 32#64
  x19_eq  : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq  : s.readReg64 .x23 = 32#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x28_eq  : s.readReg64 .x28 = 14#64
  m0_eq   : s.mem.read64 (esp s₀) = infoPtr + 32#64
  hmac_64 : HmacSt s.mem (esp s₀ + 64#64) F prk tPrev
  okm_pre : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Cut `LoopB1_96X` at `compress256(esp + 128, esp + 64, 1)` (`lr = entry + 920`). -/
structure StateLoopB1_96X (b : BitVec 64) (F : ShaCompress)
    (prk info tPrev okmSoFar : List (BitVec 8)) (infoPtr : BitVec 64)
    (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + bv% (ls_off% "sha2::sha256::compress256")
  common   : ExpandCommonX infoPtr info.length 96 s₀ s
  lr_eq    : s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 920)
  x0_eq    : s.readReg64 .x0 = esp s₀ + 128#64
  x1_eq    : s.readReg64 .x1 = esp s₀ + 64#64
  x2_eq    : s.readReg64 .x2 = 1#64
  x19_eq   : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq   : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq   : s.readReg64 .x23 = 32#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x28_eq   : s.readReg64 .x28 = 14#64
  m0_eq    : s.mem.read64 (esp s₀) = infoPtr + 32#64
  blk_64   : s.mem.readBytes (esp s₀ + 64#64) 64 = tPrev ++ info.take 32
  ist_128  : s.mem.readBytes (esp s₀ + 128#64) 32 = shaStateBytes (hmacInnerInit F prk)
  cnt1_160 : s.mem.read64 (esp s₀ + 160#64) = 2#64
  ost_168  : s.mem.readBytes (esp s₀ + 168#64) 32 = shaStateBytes (hmacOuterInit F prk)
  cnt2_200 : s.mem.read64 (esp s₀ + 200#64) = 1#64
  okm_pre  : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Cut `LoopB2_96X` at `memcpy(esp + 64, infoPtr + 32, 14)` (`lr = entry + 988`). -/
structure StateLoopB2_96X (b : BitVec 64) (F : ShaCompress)
    (prk info tPrev okmSoFar : List (BitVec 8)) (infoPtr : BitVec 64)
    (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + bv% (ls_off% "memcpy")
  common   : ExpandCommonX infoPtr info.length 96 s₀ s
  lr_eq    : s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 988)
  x0_eq    : s.readReg64 .x0 = esp s₀ + 64#64
  x1_eq    : s.readReg64 .x1 = infoPtr + 32#64
  x2_eq    : s.readReg64 .x2 = 14#64
  x19_eq   : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq   : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq   : s.readReg64 .x23 = 32#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 rem
  pos_127  : s.mem.read8 (esp s₀ + 127#64) = 14#8
  ist_128  : s.mem.readBytes (esp s₀ + 128#64) 32 =
               shaStateBytes (F (hmacInnerInit F prk) (tPrev ++ info.take 32))
  cnt1_160 : s.mem.read64 (esp s₀ + 160#64) = 2#64
  ost_168  : s.mem.readBytes (esp s₀ + 168#64) 32 = shaStateBytes (hmacOuterInit F prk)
  cnt2_200 : s.mem.read64 (esp s₀ + 200#64) = 1#64
  okm_pre  : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Cut `LoopB_96X` at `entry + 604` (after `memcpy` of `info.drop 32` and appending `(i + 1)#8`). -/
structure StateLoopB_96X (b : BitVec 64) (F : ShaCompress)
    (prk info tPrev okmSoFar : List (BitVec 8)) (infoPtr : BitVec 64)
    (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 604)
  common  : ExpandCommonX infoPtr info.length 96 s₀ s
  x19_eq  : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq  : s.readReg64 .x23 = 32#64
  x24_eq  : s.readReg64 .x24 = 64#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x28_eq  : s.readReg64 .x28 = esp s₀ + 64#64
  hmac_64 : HmacStGen s.mem (esp s₀ + 64#64) F prk (tPrev ++ info.take 32)
              (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Cut `LoopC_96X` at `finalize_fixed` entry in loop (`lr = entry + 672`). -/
structure StateLoopC_96X (b : BitVec 64) (F : ShaCompress)
    (prk info tPrev okmSoFar : List (BitVec 8)) (infoPtr : BitVec 64)
    (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]")
  common   : ExpandCommonX infoPtr info.length 96 s₀ s
  lr_eq    : s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 672)
  x0_eq    : s.readReg64 .x0 = esp s₀ + 208#64
  x1_eq    : s.readReg64 .x1 = esp s₀ + 240#64
  x19_eq   : s.readReg64 .x19 = BitVec.ofNat 64 i
  x21_eq   : s.readReg64 .x21 = s₀.readReg64 .x2 + BitVec.ofNat 64 (dstOff + 32)
  x22_eq   : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq   : s.readReg64 .x23 = 32#64
  x24_eq   : s.readReg64 .x24 = 64#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 (rem - 32)
  x28_eq   : s.readReg64 .x28 = esp s₀ + 64#64
  hmac_240 : HmacStGen s.mem (esp s₀ + 240#64) F prk (tPrev ++ info.take 32)
               (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre  : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-! ## Block 1 (`T(1)`) Segments -/

section Block1

variable {b : BitVec 64} {F : ShaCompress}
  {ext : String → Option (State → State)}

theorem seg0_96_x_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀) :
    RunsTo (tripleRatchetProgAtExt b ext) s₀ (StateX0pX b infoPtr info.length 96 s₀) := by
  have hpc := hpre.pc_eq; have hrun := hpre.status; have hx3 := hpre.x3_eq
  have hsp_al := hpre.sp_aligned; have hesp := esp_aligned hpre.sp_aligned
  have hrw : s₀.mem.RW (esp s₀) 496 :=
    hpre.rw_esp (S2FrameRO.refl infoPtr info.length s₀.mem _)
  iterate 8 s2_step
  refine RunsTo.refl ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc],
    hrun, by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx3],
    ?_, ExpandFrameX.of_agreesOutside_esp (off := 400#64) (sz := 96)
      (S2FrameRO.refl infoPtr info.length s₀.mem _) (by prove_agrees_esp) (by decide)⟩
  simp only [Expand.mem_setMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (config := { decide := true }) only [arm64_norm]

theorem seg1_96_x_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hx : StateX0pX b infoPtr info.length 96 s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateX1X b F prk info infoPtr 96 s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.status; have hsp := hx.sp_eq; have hx29 := hx.x29_eq
  have hx0 := hx.x0_eq; have hx1 := hx.x1_eq; have hx2 := hx.x2_eq; have hx3 := hx.x3_eq
  have hesp := esp_aligned hpre.sp_aligned; have hrw := hpre.rw_esp hx.frame
  have hread_x0 := hpre.readable_x0 hx.frame; have hread_x1 := hpre.readable_x1 hx.frame
  rcases hpre.toExpandPre96_46.read64_x0_write64_esp with ⟨h_x0_w0, h_x0_w⟩
  rcases hpre.toExpandPre96_46.read64_x1_write_esp with ⟨h_x1_w0, h_x1_w8, _, _⟩
  have hx1_val0 := hpre.info_ptr_eq hx.frame; have hx1_val8 := hpre.info_len_eq_46 hx.frame
  have hpos_x0 : s.mem.read8 (s₀.readReg64 .x0 + 63#64) = 0#8 := (hpre.hmac_x0 hx.frame).2.2.1
  iterate 40 s2_step
  refine RunsTo.refl ⟨rfl,
    ⟨hrun, hsp, hx29, rfl, rfl,
     by simp (config := { decide := true }) only [arm64_norm],
     by simp (config := { decide := true }) only [arm64_norm],
     ExpandSaved.of_agreesOutside_low (off := 8#64) (sz := 312) hx.saved (by prove_agrees_esp) (by decide),
     ExpandFrameX.of_agreesOutside_esp (off := 8#64) (sz := 312) hx.frame (by prove_agrees_esp) (by decide)⟩,
    rfl, rfl, rfl, by rw [hpre.info_len_eq]; rfl, rfl, rfl, rfl, rfl,
    by rw [hpre.info_len_eq]; rfl, ?_⟩
  simp only [Expand.mem_setMem]
  refine HmacSt.of_copy_empty_esp_64 (hpre.hmac_x0 hx.frame)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w]

theorem seg2a_96_tail_x_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s₁ : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hpc : s₁.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 192))
    (hc1 : ExpandCommonX infoPtr info.length 96 s₀ s₁)
    (hx19 : s₁.readReg64 .x19 = 0#64) (hx22 : s₁.readReg64 .x22 = s₀.readReg64 .x2)
    (hx23 : s₁.readReg64 .x23 = 32#64) (hx24 : s₁.readReg64 .x24 = 96#64)
    (hx26 : s₁.readReg64 .x26 = 46#64) (hhm : HmacSt s₁.mem (esp s₀ + 64#64) F prk [])
    (hinfo_m₁ : s₁.mem.readBytes (esp s₀ + 64#64) 46 = info) :
    RunsTo (tripleRatchetProgAtExt b ext) s₁ (StateX1bX b F prk info infoPtr 96 s₀) := by
  have hrun := hc1.status; have hsp := hc1.sp_eq; have hx29 := hc1.x29_eq
  have hx27 := hc1.x27_eq; have hx20 := hc1.x20_eq
  have hesp := esp_aligned hpre.sp_aligned; have hrw_esp := hpre.rw_esp hc1.frame
  iterate 13 s2_step
  refine RunsTo.refl ⟨by rw [State.pc_setMem]; simp only [arm64_norm, hpc],
    ExpandCommonX.of_agreesOutside_low32 (off := 64#64) (sz := 177) hc1
      (by rw [State.status_setMem]; simp only [arm64_norm, hrun])
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm], ?_⟩
  rw [Expand.mem_setMem]
  exact hmacSt_of_counter_writes_46 hhm hinfo_m₁ hpre.info_len_eq

theorem seg2a_96_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hx : StateX1X b F prk info infoPtr 96 s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s (StateX1bX b F prk info infoPtr 96 s₀) := by
  have hlen46 := hpre.info_len_eq; have hrw_esp := hpre.rw_esp hx.common.frame
  have hmc := memcpyRO_stub_runsTo hS.memcpyRO
    hx.pc_eq hx.common.status hx.x0_eq hx.x1_eq (by rw [hx.x2_eq, hlen46]; rfl) (by omega)
    (hpre.info_bytes_eq hx.common.frame) (hrw_esp.sub (by bv_omega))
    (hpre.readable_info hx.common.frame) (hpre.rw_extStack hx.common.frame hx.common.sp_eq)
    (ExpandPre96_46X.disj_esp_extStack hx.common.sp_eq ⟨by omega, by bv_omega⟩)
    (hpre.out_info_esp_off (by simp; omega))
    (by rw [hx.common.sp_eq]; exact hpre.out_info_extStack)
    (by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned)
  refine hmc.trans fun s₁ ⟨hpc₁, hstat₁, hcc₁, _, hdst₁, _, hfr_mc⟩ => ?_
  rw [hx.common.sp_eq] at hfr_mc
  exact runsTo_toE (seg2a_96_tail_x_runsTo hpre (hpc₁.trans hx.lr_eq)
    (hpre.common_of_s2frameRO_esp hx.common ⟨by decide, by simp; omega⟩ hstat₁ hcc₁ hfr_mc)
    ((Extract.CallingConventionPreserved.x19 hcc₁).trans hx.x19_eq)
    ((Extract.CallingConventionPreserved.x22 hcc₁).trans hx.x22_eq)
    ((CallingConventionPreserved.x23 hcc₁).trans hx.x23_eq)
    ((CallingConventionPreserved.x24 hcc₁).trans hx.x24_eq)
    ((CallingConventionPreserved.x26 hcc₁).trans (by rw [hx.x26_eq, hlen46]))
    (hmacSt_of_memcpyRO_46 hx.hmac_64 hrw_esp hlen46 hfr_mc) (by rwa [hlen46] at hdst₁))

theorem seg2b_96_x_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hx : StateX1bX b F prk info infoPtr 96 s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateX2X b F prk info infoPtr 96 s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq; have hx27 := hx.common.x27_eq; have hx20 := hx.common.x20_eq
  have hx22 := hx.x22_eq; have hx23 := hx.x23_eq; have hx26 := hx.x26_eq
  have hesp := esp_aligned hpre.sp_aligned; have hrw := hpre.rw_esp hx.common.frame
  iterate 13 s2_step
  refine RunsTo.refl ⟨rfl,
    ExpandCommonX.of_agreesOutside_low32 (off := 240#64) (sz := 0x90) hx.common
      hrun hsp hx29 hx27 hx20 (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl, hx22, hx23, hx26, ?_⟩
  simp only [Expand.mem_setMem]
  refine HmacSt.of_copy_esp_64_240 hx.hmac_64
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := { decide := true }) only [arm64_norm]

theorem fin1_96_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hx : StateX2X b F prk info infoPtr 96 s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s (StateX2rX b F prk info infoPtr 96 s₀) := by
  rcases hpre.fin_side_conditions_x hx.common.frame with
    ⟨hrw_out, hrw_hm, hrw_sp, hd_out_hm, hd_out_sp, hd_hm_sp⟩
  refine (finalize_fixed_single_runsToE_base
    (memsetStep_of_stubs hS) (compressOneStep_of_stubs hS)
    hx.pc_eq hx.common.status hx.x0_eq hx.x1_eq hpre.prk_le (by simp [hpre.info_len_eq])
    hx.hmac_240 hrw_out hrw_hm (by rw [hx.common.sp_eq]; exact hrw_sp) hd_out_hm
    (by rw [hx.common.sp_eq]; exact hd_out_sp) (by rw [hx.common.sp_eq]; exact hd_hm_sp)
    (by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned)).mono
    fun s' ⟨hpc', hstat', hcc, ht1, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.common.sp_eq] at hfr
  exact ⟨hpc', hpre.common_of_fin_frame_x hx.common hstat' hcc hfr,
    (Extract.CallingConventionPreserved.x22 hcc).trans hx.x22_eq,
    (CallingConventionPreserved.x23 hcc).trans hx.x23_eq,
    (CallingConventionPreserved.x26 hcc).trans hx.x26_eq, ht1⟩

theorem memcpy_208_to_x2_runsTo (hS : HkdfStubsExt b F ext)
    {prk info okmSoFar bs : List (BitVec 8)} {infoPtr : BitVec 64} {dstOff : ℕ} {s₀ s_mc : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hdst : dstOff + 32 ≤ 96) (hbs_len : bs.length = 32)
    (hpc_mc : s_mc.pc = b + bv% (ls_off% "memcpy"))
    (hc_mc : ExpandCommonX infoPtr info.length 96 s₀ s_mc)
    (hx0_mc : s_mc.readReg64 .x0 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
    (hx1_mc : s_mc.readReg64 .x1 = esp s₀ + 208#64)
    (hx2_mc : s_mc.readReg64 .x2 = 32#64)
    (hsrc_mc : s_mc.mem.readBytes (esp s₀ + 208#64) 32 = bs)
    (hokm_mc : s_mc.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar) :
    RunsToE (tripleRatchetProgAtExt b ext) s_mc (fun s₁ =>
      s₁.pc = s_mc.readReg64 .lr ∧
      ExpandCommonX infoPtr info.length 96 s₀ s₁ ∧
      CallingConventionPreserved s_mc s₁ ∧
      s₁.mem.readBytes (esp s₀ + 208#64) 32 = bs ∧
      s₁.mem.readBytes (s₀.readReg64 .x2) (dstOff + 32) = okmSoFar ++ bs) := by
  have hd_off : (BitVec.ofNat 64 dstOff).toNat = dstOff := Nat.mod_eq_of_lt (by omega)
  have hrw_x2 := hpre.rw_x2_frame hc_mc.frame; have hrw_esp := hpre.rw_esp hc_mc.frame
  have hrw_dst : s_mc.mem.RW (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 :=
    hrw_x2.sub (by bv_omega)
  have hd_dst_src : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32
      (esp s₀ + 208#64) 32 :=
    (hpre.disj_x2_stack.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _
      ⟨by decide, by unfold esp; bv_omega⟩
  have hd_dst_ext : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32
      (s_mc.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hc_mc.sp_eq]; change DisjointRegions _ 32 (esp s₀ - 16384#64) 16384
    exact (hpre.disj_x2_stack.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _
      ⟨by decide, by unfold esp; bv_omega⟩
  refine (memcpy_stub_runsTo hS.memcpy (bs := bs) hpc_mc hc_mc.status hx0_mc hx1_mc
    (by rw [hx2_mc, hbs_len]; rfl) (by rw [hbs_len]; exact hsrc_mc)
    (by rw [hbs_len]; exact hrw_dst) (by rw [hbs_len]; exact hrw_esp.sub (by bv_omega))
    (hpre.rw_extStack hc_mc.frame hc_mc.sp_eq)
    (by rw [hbs_len]; exact hd_dst_src) (by rw [hbs_len]; exact hd_dst_ext)
    (by rw [hbs_len]; exact ExpandPre96_46X.disj_esp_extStack hc_mc.sp_eq ⟨by decide, by decide⟩)
    (by rw [hc_mc.sp_eq]; exact esp_aligned hpre.sp_aligned)).mono
    fun s₁ ⟨hpc₁, hstat₁, hcc₁, _, hdst₁, hsrc₁, hfr_mc⟩ => ?_
  rw [hc_mc.sp_eq, hbs_len] at hfr_mc; rw [hbs_len] at hdst₁ hsrc₁
  have hleft : s₁.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hokm_mc
    · refine (hfr_mc.readBytes_eq (hrw_x2.sub (by bv_omega)) (fun r hr => ?_)
        (by omega)).trans hokm_mc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · unfold DisjointRegions; bv_omega
      · change DisjointRegions (esp s₀ - 16384#64) 16384 (s₀.readReg64 .x2) dstOff
        exact (hpre.disj_x2_stack.symm.sub_left _ ⟨by decide, by unfold esp; bv_omega⟩).sub_right _
          ⟨by omega, by bv_omega⟩
  refine ⟨hpc₁, hpre.common_of_memcpy_x2_frame hc_mc ⟨by decide, by omega⟩ hstat₁ hcc₁ hfr_mc,
    hcc₁, hsrc₁, ?_⟩
  rw [Bytes.readBytes_add s₁.mem (s₀.readReg64 .x2) dstOff 32, hleft, hdst₁]

theorem seg3_96_head_x_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hx : StateX2rX b F prk info infoPtr 96 s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (fun s_mc =>
      s_mc.pc = b + bv% (ls_off% "memcpy") ∧
      ExpandCommonX infoPtr info.length 96 s₀ s_mc ∧
      s_mc.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 516) ∧
      s_mc.readReg64 .x0 = s₀.readReg64 .x2 ∧ s_mc.readReg64 .x1 = esp s₀ + 208#64 ∧
      s_mc.readReg64 .x2 = 32#64 ∧ s_mc.readReg64 .x22 = s₀.readReg64 .x2 ∧
      s_mc.readReg64 .x23 = 32#64 ∧ s_mc.readReg64 .x26 = 64#64 ∧ s_mc.mem = s.mem) := by
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq; have hx27 := hx.common.x27_eq; have hx20 := hx.common.x20_eq
  have hx22 := hx.x22_eq; have hx23 := hx.x23_eq; have hx26 := hx.x26_eq
  iterate 4 s2_step
  exact RunsTo.refl ⟨rfl, ⟨hrun, hsp, hx29, hx27, hx20, hx.common.m8_eq, hx.common.m16_eq,
    hx.common.saved, hx.common.frame⟩, rfl, rfl, rfl, rfl, hx22, hx23, hx26, rfl⟩

theorem seg3_96_tail_x_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s₁ : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hpc₁ : s₁.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 516))
    (hc1 : ExpandCommonX infoPtr info.length 96 s₀ s₁)
    (hx22 : s₁.readReg64 .x22 = s₀.readReg64 .x2) (hx23 : s₁.readReg64 .x23 = 32#64)
    (hx26 : s₁.readReg64 .x26 = 64#64)
    (ht1_x2 : s₁.mem.readBytes (s₀.readReg64 .x2) 32 = t1 F prk info)
    (ht1_208 : s₁.mem.readBytes (esp s₀ + 208#64) 32 = t1 F prk info) :
    RunsTo (tripleRatchetProgAtExt b ext) s₁
      (StateLoopX b infoPtr info.length 96 (t1 F prk info) (t1 F prk info) 1 64 32 s₀) := by
  have hrun := hc1.status; have hsp := hc1.sp_eq; have hx29 := hc1.x29_eq
  have hx27 := hc1.x27_eq; have hx20 := hc1.x20_eq; have hm16_1 := hc1.m16_eq
  have hesp := esp_aligned hpre.sp_aligned; have hrw1_esp := hpre.rw_esp hc1.frame
  iterate 9 s2_step
  refine RunsTo.refl ⟨rfl,
    ExpandCommonX.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    rfl, ?_, ?_⟩
  · simp only [Expand.mem_setMem]
    refine readBytes_32_esp_32_of_208 ht1_208 ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm]
  · have hd : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) 32 :=
      (hpre.disj_x2_stack.symm.sub_left _ ⟨by decide, by unfold esp; bv_omega⟩).sub_right _
        ⟨by decide, by bv_omega⟩
    dsimp only [Expand.mem_setMem]
    exact readBytes_eq_of_agreesOutside_esp s₀ s₁.mem 32#64 32 hd (by prove_agrees_esp) (by decide) ht1_x2

theorem seg3_96_x_runsTo (hS : HkdfStubsExt b F ext)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46X b F prk info infoPtr s₀)
    (hx : StateX2rX b F prk info infoPtr 96 s₀ s) :
    RunsToE (tripleRatchetProgAtExt b ext) s
      (StateLoopX b infoPtr info.length 96 (t1 F prk info) (t1 F prk info) 1 64 32 s₀) := by
  refine (runsTo_toE (seg3_96_head_x_runsTo hx)).trans fun s_mc
    ⟨hpc_mc, hc_mc, hlr_mc, hx0_mc, hx1_mc, hx2_mc, hx22_mc, hx23_mc, hx26_mc, hmem_mc⟩ => ?_
  refine (memcpy_208_to_x2_runsTo hS hpre (dstOff := 0) (okmSoFar := []) (bs := t1 F prk info)
    (by decide) (t1_length F prk info) hpc_mc hc_mc
    (by rw [BitVec.add_zero]; exact hx0_mc) hx1_mc hx2_mc
    (by rw [hmem_mc]; exact hx.t1_208) rfl).trans
    fun s₁ ⟨hpc₁, hc1, hcc₁, ht1_208, ht1_x2⟩ => ?_
  exact runsTo_toE (seg3_96_tail_x_runsTo hpre (hpc₁.trans hlr_mc) hc1
    ((Extract.CallingConventionPreserved.x22 hcc₁).trans hx22_mc)
    ((CallingConventionPreserved.x23 hcc₁).trans hx23_mc)
    ((CallingConventionPreserved.x26 hcc₁).trans hx26_mc) ht1_x2 ht1_208)

end Block1

end HkdfLongExt

end CryptoVerification.E2E.Pqxdh.ResponderCore
