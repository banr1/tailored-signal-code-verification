/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlacedSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLongPlacedASat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Specifications.LibsignalE2E.State -- shake: keep

/-!
# Relocatable `expand_multi_info` (`okmLen = 96`, `info.length = 46`) — Assembly under `HkdfPlacedHooksSat`

Proves the remaining loop segments, epilogue, and `expand_multi_info_96_46_placed_runsToE_sat` for
Block `53` under `[HkdfPlacedHooksSat C.F H]`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLongPlacedSat

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState hmacWith)
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_8_eq readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved Frame HmacSt RW RunsTo RunsTo.lsProg_svc TraceEq blkPC_53 blkPl_53 expPlacedFakeB
   finPlacedFakeB finPlacedFakeB_off_0 hmacInnerInit hmacOuterInit length_hmacWith lsMemcpySym
   rw_of_perm_eq shaStateBytes_length)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (ExpandCommon ExpandFrame ExpandPost ExpandSaved StateDone StateLoop
   StateLoopFin StateX2Placed StateX2r agreesOutside_esp_write8 agreesOutside_writeBytes_le esp
   esp_aligned esp_eq_add mem_setMem readBytes_32_esp_32_of_208 readBytes_eq_of_agreesOutside_esp t1
   t1_length t2 t2_length t3)
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsTo.toE RunsToE S2Frame)
open CryptoVerification.LibsignalTripleRatchet.FinalizeFixedProof (FinPre)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (ExpandPre96_46 FinGenPre HmacStGen.of_copy_esp_64_240 HmacStGen.of_memcpy14_counter
   StateLoopB1_96Placed StateLoopB2_96Placed StateLoopB_96 StateLoopC_96Placed hkdfExpand_96_eq)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (applyMemcpyClobber)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlacedSat
  (finalize_fixed_gen_placed_runsTo_of_other_block_sat)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLongPlacedASat
  (iter_a1_96_placed_runsTo_sat iter_a2_96_placed_runsTo_sat iter_b1_96_placed_runsTo_sat
   seg0_96_placed_runsTo_sat seg1_96_placed_runsTo_sat seg2a_96_placed_runsTo_sat
   seg2b_96_placed_runsTo_sat seg3_96_placed_runsTo_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (s2_memcpy_step_placed_of_exact)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (HkdfPlacedHooksExactSat s2_compress256_step_placed_sat_exact)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSat (ExpandFrameS2)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat
  (finalize_fixed_placed_runsTo_of_other_block_sat)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

/-! ## `S2Frame` and Ghost-State Reset Helpers -/

@[local simp]
private theorem esp_setMem (s₀ : State) (m : Memory) : esp (s₀.setMem m) = esp s₀ := rfl

structure ExpandPre96_46Base [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (s₀ : State) : Prop where
  pre       : ExpandPre96_46 expPlacedFakeB F prk info infoPtr s₀
  read_info : s₀.mem.Readable infoPtr 46

private theorem s2_readBytes_eq_of_readable {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (hf : S2Frame m₁ m₂ regs) {p : BitVec 64} {n : ℕ} (hn : n ≤ 2 ^ 64)
    (hrd : m₁.Readable p n)
    (hout : ∀ a, InRegion p n a → ∀ r ∈ regs, OutsideRegion r.1 r.2 a) :
    m₂.readBytes p n = m₁.readBytes p n := by
  refine Memory.readBytes_congr_region hn fun a ha => ?_
  obtain ⟨hr, hlf⟩ := hrd a ha
  exact hf.1 a hr hlf (hout a ha)

private theorem s2_read64_eq_of_readable {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (hf : S2Frame m₁ m₂ regs) {p : BitVec 64}
    (hrd : m₁.Readable p 8)
    (hout : ∀ a, InRegion p 8 a → ∀ r ∈ regs, OutsideRegion r.1 r.2 a) :
    m₂.read64 p = m₁.read64 p := by
  have hbytes := s2_readBytes_eq_of_readable hf (by decide) hrd hout
  rw [readBytes_8_eq, readBytes_8_eq] at hbytes
  simp only [List.cons.injEq, and_true] at hbytes
  rcases hbytes with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  dsimp only [Memory.read64]
  simp only [BitVec.add_zero, h0, h1, h2, h3, h4, h5, h6, h7]

private theorem readable_sub {m : Memory} {b b' : BitVec 64} {n n' : ℕ}
    (hr : m.Readable b n) (h : ∀ a, InRegion b' n' a → InRegion b n a) :
    m.Readable b' n' :=
  fun a ha => hr a (h a ha)

private theorem ExpandPre96_46Base.at_mem [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ : State}
    (hb : ExpandPre96_46Base F prk info infoPtr s₀)
    (m : Memory) (hf : ExpandFrameS2 96 s₀ m) :
    ExpandPre96_46 expPlacedFakeB F prk info infoPtr (s₀.setMem m) := by
  have hout_pair {p : BitVec 64} {n : ℕ}
      (ho_x2 : ∀ a, InRegion p n a → OutsideRegion (s₀.readReg64 .x2) 96 a)
      (ho_stk : ∀ a, InRegion p n a → OutsideRegion (s₀.sp - 640#64) 640 a) :
      ∀ a, InRegion p n a →
        ∀ r ∈ [(s₀.readReg64 .x2, 96), (s₀.sp - 640#64, 640)], OutsideRegion r.1 r.2 a := by
    intro a ha r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ho_x2 a ha
    · exact ho_stk a ha
  have hhmac_m : HmacSt m (s₀.readReg64 .x0) F prk [] := by
    have hout_x0 := hout_pair
      (fun a ha => hb.pre.disj_x0_x2.symm.outside ha (by decide))
      (fun a ha => hb.pre.disj_x0_stack.symm.outside ha (by decide))
    rcases hb.pre.hmac_st with ⟨hlen, _, hpos, hin, hcnt1, hout, hcnt2⟩
    refine ⟨hlen, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · have ha : InRegion (s₀.readReg64 .x0) 144 (s₀.readReg64 .x0 + 63#64) := by
        unfold InRegion; bv_omega
      obtain ⟨hr, hlf⟩ := hb.pre.read_x0 _ ha
      exact (hf.1 _ hr hlf (hout_x0 _ ha)).trans hpos
    · refine (s2_readBytes_eq_of_readable hf (by decide)
        (readable_sub hb.pre.read_x0 (fun a ha => by unfold InRegion at ha ⊢; bv_omega))
        (fun a ha => hout_x0 a ?_)).trans hin
      unfold InRegion at ha ⊢; bv_omega
    · refine (s2_read64_eq_of_readable hf
        (readable_sub hb.pre.read_x0 (fun a ha => by unfold InRegion at ha ⊢; bv_omega))
        (fun a ha => hout_x0 a ?_)).trans hcnt1
      unfold InRegion at ha ⊢; bv_omega
    · refine (s2_readBytes_eq_of_readable hf (by decide)
        (readable_sub hb.pre.read_x0 (fun a ha => by unfold InRegion at ha ⊢; bv_omega))
        (fun a ha => hout_x0 a ?_)).trans hout
      unfold InRegion at ha ⊢; bv_omega
    · refine (s2_read64_eq_of_readable hf
        (readable_sub hb.pre.read_x0 (fun a ha => by unfold InRegion at ha ⊢; bv_omega))
        (fun a ha => hout_x0 a ?_)).trans hcnt2
      unfold InRegion at ha ⊢; bv_omega
  have hout_x1 := hout_pair
    (fun a ha => hb.pre.disj_x1_x2.symm.outside ha (by decide))
    (fun a ha => hb.pre.disj_x1_stack.symm.outside ha (by decide))
  exact
    { pc_eq         := hb.pre.pc_eq
      status        := hb.pre.status
      x3_eq         := hb.pre.x3_eq
      prk_le        := hb.pre.prk_le
      info_len_eq   := hb.pre.info_len_eq
      hmac_st       := hhmac_m
      info_ptr      := show m.read64 (s₀.readReg64 .x1) = infoPtr from
        (s2_read64_eq_of_readable hf
          (readable_sub hb.pre.read_x1 (fun a ha => by unfold InRegion at ha ⊢; bv_omega))
          (fun a ha => hout_x1 a (by unfold InRegion at ha ⊢; bv_omega))).trans hb.pre.info_ptr
      info_len      := show m.read64 (s₀.readReg64 .x1 + 8#64) = 46#64 from
        (s2_read64_eq_of_readable hf
          (readable_sub hb.pre.read_x1 (fun a ha => by unfold InRegion at ha ⊢; bv_omega))
          (fun a ha => hout_x1 a (by unfold InRegion at ha ⊢; bv_omega))).trans hb.pre.info_len
      info_bytes    := (s2_readBytes_eq_of_readable hf (by decide)
        hb.read_info (hout_pair hb.pre.out_info_x2 hb.pre.out_info_stk)).trans hb.pre.info_bytes
      read_x0       := fun a ha => let ⟨hr, hlf⟩ := hb.pre.read_x0 a ha; hf.2.2 a hr hlf
      read_x1       := fun a ha => let ⟨hr, hlf⟩ := hb.pre.read_x1 a ha; hf.2.2 a hr hlf
      rw_x2         := hf.rw_of_rw (s₀.readReg64 .x2) 96 hb.pre.rw_x2
      rw_stack      := hf.rw_of_rw (s₀.sp - 640#64) 640 hb.pre.rw_stack
      disj_x2_stack := hb.pre.disj_x2_stack
      disj_x0_stack := hb.pre.disj_x0_stack
      disj_x0_x2    := hb.pre.disj_x0_x2
      disj_x1_stack := hb.pre.disj_x1_stack
      disj_x1_x2    := hb.pre.disj_x1_x2
      out_info_stk  := hb.pre.out_info_stk
      out_info_x2   := hb.pre.out_info_x2
      sp_aligned    := hb.pre.sp_aligned }

private theorem expandCommon96_reset_of_fin [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {prk info : List (BitVec 8)}
    {infoPtr : BitVec 64} {s₀ s s' : State} {m_ref : Memory}
    (hb : ExpandPre96_46Base F prk info infoPtr s₀)
    (hf_ref : ExpandFrameS2 96 s₀ m_ref)
    (hc : ExpandCommon 96 (s₀.setMem m_ref) s)
    (hstat : s'.status = .Running)
    (hcs : CalleeSaved s s')
    (hfr : S2Frame s.mem s'.mem [(esp s₀ + 208#64, 32), (esp s₀ + 240#64, 144), (esp s₀ - 144#64, 144)]) :
    ExpandFrameS2 96 s₀ s'.mem ∧ ExpandCommon 96 (s₀.setMem s'.mem) s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre_ref.rw_esp hc.frame
  have hf_s : ExpandFrameS2 96 s₀ s.mem := hf_ref.trans (S2Frame.of_frame hc.frame)
  have hf_s' : ExpandFrameS2 96 s₀ s'.mem := by
    refine hf_s.trans (hfr.mono fun a ha r hr => ?_)
    have hstk := ha (s₀.sp - 640#64, 640) (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold OutsideRegion esp at *; bv_omega)
  have h_eq_off (off : BitVec 64)
      (hoff : decide ((off.toNat + 8 ≤ 32) ∨ (400 ≤ off.toNat ∧ off.toNat + 8 ≤ 496)) = true) :
      s'.mem.read64 (esp s₀ + off) = s.mem.read64 (esp s₀ + off) := by
    have hcond := of_decide_eq_true hoff
    refine hfr.read64_eq (hrw_esp.sub (by bv_omega)) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions esp; bv_omega)
  rcases hc.saved with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hsaved' : ExpandSaved (s₀.setMem s'.mem) s'.mem :=
    { m400 := (h_eq_off 400#64 (by decide)).trans h0
      m408 := (h_eq_off 408#64 (by decide)).trans h1
      m416 := (h_eq_off 416#64 (by decide)).trans h2
      m424 := (h_eq_off 424#64 (by decide)).trans h3
      m432 := (h_eq_off 432#64 (by decide)).trans h4
      m440 := (h_eq_off 440#64 (by decide)).trans h5
      m448 := (h_eq_off 448#64 (by decide)).trans h6
      m456 := (h_eq_off 456#64 (by decide)).trans h7
      m464 := (h_eq_off 464#64 (by decide)).trans h8
      m472 := (h_eq_off 472#64 (by decide)).trans h9
      m480 := (h_eq_off 480#64 (by decide)).trans h10
      m488 := (h_eq_off 488#64 (by decide)).trans h11 }
  exact ⟨hf_s',
    ⟨hstat,
     hcs.sp_eq.trans hc.sp_eq,
     (CalleeSaved.x29 hcs).trans hc.x29_eq,
     (CalleeSaved.x27 hcs).trans hc.x27_eq,
     (CalleeSaved.x20 hcs).trans hc.x20_eq,
     (h_eq_off 8#64 (by decide)).trans hc.m8_eq,
     (h_eq_off 16#64 (by decide)).trans hc.m16_eq,
     hsaved',
     Frame.refl s'.mem _⟩⟩

/-! ## Loop Tail Segments and `finalize_fixed` Glue -/

private theorem readable_of_rw {m : Memory} {a : BitVec 64} {n : Nat} (h : m.RW a n) :
    m.Readable a n := by
  intro x hx
  obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (h x hx)
  exact ⟨by rw [hp]; rfl, hlf⟩

private theorem disj_esp_info46_14 {s₀ : State} {infoPtr : BitVec 64}
    (hout : ∀ a, InRegion infoPtr 46 a → OutsideRegion (s₀.sp - 640#64) 640 a) :
    DisjointRegions (esp s₀ + 64#64) 14 (infoPtr + 32#64) 14 := by
  have h_i0 := hout (infoPtr + 32#64) (by unfold InRegion; bv_omega)
  have h_in := hout (infoPtr + 45#64) (by unfold InRegion; bv_omega)
  unfold OutsideRegion at h_i0 h_in
  unfold DisjointRegions esp
  bv_omega

section PlacedPartBSat

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks} [hH : HkdfPlacedHooksExactSat C.F H]

theorem fin1_96_placed_runsTo_sat {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : ExpandPre96_46Base C.F prk info infoPtr s₀)
    (hf_ref : ExpandFrameS2 96 s₀ m_ref)
    (hx : StateX2Placed C.F prk info 96 (s₀.setMem m_ref) s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s fun s' =>
      ∃ m_ref', ExpandFrameS2 96 s₀ m_ref' ∧
        StateX2r expPlacedFakeB C.F prk info 96 (s₀.setMem m_ref') s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  rcases hpre_ref.fin_side_conditions hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hfin_pre : FinPre finPlacedFakeB C.F prk (info ++ [1#8]) s :=
    { pc_eq := by rw [finPlacedFakeB_off_0]; exact hx.pc_eq
      status := hx.common.status
      key_le := hb.pre.prk_le
      msg_lt := by simp [hb.pre.info_len_eq]
      hmac_st := by rw [hx.x1_eq, esp_setMem]; exact hx.hmac_240
      rw_out := by rw [hx.x0_eq]; exact hrw_x0
      rw_hm := by rw [hx.x1_eq]; exact hrw_x1
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sp
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; exact hd_x0_x1
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; exact hd_x0_sp
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; exact hd_x1_sp
      sp_aligned := by rw [hx.common.sp_eq, esp_setMem]; exact esp_aligned hb.pre.sp_aligned }
  refine (finalize_fixed_placed_runsTo_of_other_block_sat (C := C) (H := H)
    hcl hfin_pre).mono fun s' ⟨hpc', hrun', hcs, ht1, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'
  rw [hx.x0_eq, esp_setMem] at ht1
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq, esp_setMem] at hfr
  obtain ⟨hf_s', hc'⟩ := expandCommon96_reset_of_fin hb hf_ref hx.common hrun' hcs hfr
  exact ⟨s'.mem, hf_s', ⟨by rw [hpc']; simp only [arm64_norm], hc',
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans hx.x23_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq,
    ht1⟩⟩

theorem iter_b2_96_placed_runsTo_sat {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopB1_96Placed C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopB2_96Placed C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hlr := hx.lr_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrw_128 : s.mem.RW (esp s₀ + 128#64) 32 := hrw_esp.sub (by bv_omega)
  have hblk_len : (tPrev ++ info.take 32).length = 64 := by simp [ht_len, hpre.info_len_eq]
  refine s2_compress256_step_placed_sat_exact C H hrun hpc hx0 hx1 hx2 hlr
    hx.ist_128 hx.blk_64 hblk_len hrw_128 ?_
  generalize hist_def : shaStateBytes (C.F (hmacInnerInit C.F prk) (tPrev ++ info.take 32)) = ist'
  have hist'_len : ist'.length = 32 := by rw [← hist_def]; exact shaStateBytes_length _
  generalize hm1_def : s.mem.writeBytes (esp s₀ + 128#64) ist' = m₁
  have hA1 : AgreesOutside s.mem m₁ (esp s₀ + 128#64) 32 := by
    rw [← hm1_def]
    exact agreesOutside_writeBytes_le s.mem (esp s₀ + 128#64) ist' 32 (by rw [hist'_len])
  have hrw_wb : m₁.RW (esp s₀) 496 := rw_of_perm_eq hA1.2 hrw_esp
  have hm0_m1 : m₁.read64 (esp s₀) = infoPtr + 32#64 := by
    rw [hA1.read64_eq (by unfold DisjointRegions; bv_omega), hx.m0_eq]
  iterate 11 s2_step
  refine RunsTo.refl ?_
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  have hA2 : AgreesOutside m₁ ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8)
      (esp s₀ + 127#64) 1 := by
    refine agreesOutside_esp_write8 ?_ (by decide)
    exact agreesOutside_esp_write8 (AgreesOutside.rfl' _ _ _) (by decide)
  have hpos_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).read8
      (esp s₀ + 127#64) = 14#8 :=
    Memory.read8_write8_same _ _ _
  have hist_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).readBytes
      (esp s₀ + 128#64) 32 =
      shaStateBytes (C.F (hmacInnerInit C.F prk) (tPrev ++ info.take 32)) := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    rw [← hm1_def, hist_def]
    have h :=
      readBytes_writeBytes_same s.mem (esp s₀ + 128#64) ist' (by rw [hist'_len]; decide)
    rwa [hist'_len] at h
  have hcnt1_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).read64
      (esp s₀ + 160#64) = 2#64 := by
    refine (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    exact (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans hx.cnt1_160
  have host_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).readBytes
      (esp s₀ + 168#64) 32 =
      shaStateBytes (hmacOuterInit C.F prk) := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    exact (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans hx.ost_168
  have hcnt2_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).read64
      (esp s₀ + 200#64) = 1#64 := by
    refine (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    exact (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans hx.cnt2_200
  have hokm_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).readBytes
      (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd1 : DisjointRegions (esp s₀ + 128#64) 32 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 128#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      have hd2 : DisjointRegions (esp s₀ + 127#64) 1 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 127#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      exact (hA2.readBytes_eq hd2 (by omega)).trans
        ((hA1.readBytes_eq hd1 (by omega)).trans hx.okm_pre)
  refine ⟨by simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 127#64) (sz := 1) hc1
      (by simp only [arm64_norm, hrun])
      (by simp (config := { decide := true }) only [arm64_norm, hsp])
      (by simp (config := { decide := true }) only [arm64_norm, hx29])
      (by simp (config := { decide := true }) only [arm64_norm, hx27])
      (by simp (config := { decide := true }) only [arm64_norm, hx20])
      (by simp only [arm64_norm]; exact hA2) (by decide),
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hx19],
    by simp (config := { decide := true }) only [arm64_norm, hx22],
    by simp (config := { decide := true }) only [arm64_norm, hx23],
    by simp (config := { decide := true }) only [arm64_norm, hx26],
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hpos_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hist_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hcnt1_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact host_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hcnt2_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hokm_m2⟩

theorem iter_b3_96_placed_runsTo_sat {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hrd_info : s₀.mem.Readable infoPtr 46)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopB2_96Placed C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopB_96 expPlacedFakeB C.F prk info tPrev okmSoFar i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hlr := hx.lr_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx26 := hx.x26_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hsp_s : s.spAligned = true := by simpa [State.spAligned, hsp] using hesp
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 64#64) 14 := hrw_esp.sub (by bv_omega)
  have hrd_info14 : s.mem.Readable (infoPtr + 32#64) 14 :=
    readable_sub ((hx.common.frame.readable_iff infoPtr 46).mpr hrd_info)
      (fun a ha => by unfold InRegion at ha ⊢; bv_omega)
  have hdisj_info : 14 = 0 ∨ DisjointRegions (esp s₀ + 64#64) 14 (infoPtr + 32#64) 14 :=
    Or.inr (disj_esp_info46_14 hpre.out_info_stk)
  have hread_info46 : s.mem.readBytes infoPtr 46 = info := hpre.info_bytes_eq hx.common.frame
  have hdrop_len : (info.drop 32).length = 14 := by simp [hpre.info_len_eq]
  have hread_info14 : s.mem.readBytes (infoPtr + 32#64) 14 = info.drop 32 := by
    have h := readBytes_slice_of_readBytes_eq s.mem infoPtr info
      (by rw [hpre.info_len_eq]; exact hread_info46) 32 14 (by rw [hpre.info_len_eq])
    have htake : (info.drop 32).take 14 = info.drop 32 :=
      List.take_of_length_le (by rw [hdrop_len])
    exact h.trans htake
  have hx2_nat : (s.readReg64 .x2).toNat = 14 := by rw [hx2]; rfl
  refine s2_memcpy_step_placed_of_exact H hH.memcpy
    hrun hsp_s hpc hx0 hx1 hx2_nat hlr hread_info14 hrw_dst hrd_info14 hdisj_info fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₁ := s.mem.writeBytes (esp s₀ + 64#64) (info.drop 32)
  have hA1 : AgreesOutside s.mem m₁ (esp s₀ + 64#64) 14 :=
    agreesOutside_writeBytes_le s.mem (esp s₀ + 64#64) (info.drop 32) 14 (by rw [hdrop_len])
  have hrw_wb : m₁.RW (esp s₀) 496 := rw_of_perm_eq hA1.2 hrw_esp
  have hpos_m1 : m₁.read8 (esp s₀ + 127#64) = 14#8 := by
    rw [hA1.1 (esp s₀ + 127#64) (by simp only [OutsideRegion]; bv_omega), hx.pos_127]
  dsimp only [m₁] at hrw_wb hpos_m1
  have hi_eq : (BitVec.ofNat 64 i == 255#64) = false := by rcases hi with rfl | rfl <;> rfl
  have hi_ne : (BitVec.ofNat 64 i != 255#64) = true := by rcases hi with rfl | rfl <;> rfl
  have hi_cmp : (AddWithCarry64 (BitVec.ofNat 64 i) (bv% (2 ^ 64 - 256)) true).2.z = false := by
    rcases hi with rfl | rfl <;> rfl
  have hi_add1 : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 i) + 1#32) =
      BitVec.ofNat 64 (i + 1) := by
    rcases hi with rfl | rfl <;> rfl
  iterate 14 s2_step
  refine RunsTo.refl ?_
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  let c := BitVec.ofNat 8 (i + 1)
  have hA2 : AgreesOutside m₁
      (((m₁.write8 (esp s₀ + 240#64) c).write8 (esp s₀ + 78#64) c).write8 (esp s₀ + 127#64) 15#8)
      (esp s₀ + 64#64) 177 := by
    refine agreesOutside_esp_write8 ?_ (by decide)
    refine agreesOutside_esp_write8 ?_ (by decide)
    exact agreesOutside_esp_write8 (AgreesOutside.rfl' _ _ _) (by decide)
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 177) hc1
      (by rw [State.status_setMem]; simp only [arm64_norm, hrun])
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by simp only [arm64_norm]; exact hA2)
      (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx19],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ?_, ?_⟩
  · rw [mem_setMem]
    exact HmacStGen.of_memcpy14_counter ht_len hpre.info_len_eq
      hx.ist_128 hx.cnt1_160 hx.ost_168 hx.cnt2_200
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd1 : DisjointRegions (esp s₀ + 64#64) 14 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      have hd2 : DisjointRegions (esp s₀ + 64#64) 177 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      simp only [arm64_norm]
      exact (hA2.readBytes_eq hd2 (by omega)).trans
        ((hA1.readBytes_eq hd1 (by omega)).trans hx.okm_pre)

theorem iter_c_96_placed_runsTo_sat {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopB_96 expPlacedFakeB C.F prk info tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopC_96Placed C.F prk info tPrev okmSoFar i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  iterate 17 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 240#64) (sz := 144) hx.common
      hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl, hx19,
    by rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl,
    hx22, hx23, hx24,
    by rcases hrem with rfl | rfl <;> rfl,
    hx28, ?_, ?_⟩
  · simp only [mem_setMem]
    exact HmacStGen.of_copy_esp_64_240 hx.hmac_64
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd : DisjointRegions (esp s₀ + 240#64) 144 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 240#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 240#64 144 hd (by prove_agrees_esp)
        (by omega) hx.okm_pre

theorem iter_fin_96_placed_runsTo_sat {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {i rem dstOff : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : ExpandPre96_46Base C.F prk info infoPtr s₀)
    (hf_ref : ExpandFrameS2 96 s₀ m_ref)
    (ht_len : tPrev.length = 32)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopC_96Placed C.F prk info tPrev okmSoFar i rem dstOff (s₀.setMem m_ref) s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s fun s' =>
      ∃ m_ref', ExpandFrameS2 96 s₀ m_ref' ∧
        StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar 96 i rem dstOff
          (s₀.setMem m_ref') s' := by
  have hmin : min rem 32 = 32 := by rcases hrem with rfl | rfl <;> rfl
  have hpre_ref := hb.at_mem m_ref hf_ref
  rcases hpre_ref.fin_side_conditions hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) 96 := hpre_ref.rw_x2_frame hx.common.frame
  have hfin_pre : FinGenPre finPlacedFakeB C.F prk (tPrev ++ info.take 32)
      (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) s :=
    { pc_eq := by rw [finPlacedFakeB_off_0]; exact hx.pc_eq
      status := hx.common.status
      key_le := hb.pre.prk_le
      rem_lt := by simp [hb.pre.info_len_eq]
      hmac_st := by rw [hx.x1_eq, esp_setMem]; exact hx.hmac_240
      rw_out := by rw [hx.x0_eq]; exact hrw_x0
      rw_hm := by rw [hx.x1_eq]; exact hrw_x1
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sp
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; exact hd_x0_x1
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; exact hd_x0_sp
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; exact hd_x1_sp
      sp_aligned := by rw [hx.common.sp_eq, esp_setMem]; exact esp_aligned hb.pre.sp_aligned }
  refine (finalize_fixed_gen_placed_runsTo_of_other_block_sat (C := C) (H := H)
    hcl hfin_pre).mono fun s' ⟨hpc', hrun', hcs, ht, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'
  rw [hx.x0_eq, esp_setMem, List.append_assoc, ← List.append_assoc (info.take 32),
      List.take_append_drop, ← List.append_assoc] at ht
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq, esp_setMem] at hfr
  have hokm' : s'.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · refine (hfr.readBytes_eq (hrw_x2.sub (by bv_omega)) (fun r hr => ?_) (by omega)).trans
        hx.okm_pre
      have hd_stk : DisjointRegions (s₀.sp - 640#64) 640 (s₀.readReg64 .x2) dstOff :=
        hb.pre.disj_x2_stack.symm.sub_right (s₀.readReg64 .x2) ⟨by omega, by bv_omega⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact hd_stk.sub_left _ ⟨by dsimp; decide, by dsimp; unfold esp; bv_omega⟩
  obtain ⟨hf_s', hc'⟩ := expandCommon96_reset_of_fin hb hf_ref hx.common hrun' hcs hfr
  exact ⟨s'.mem, hf_s', ⟨by rw [hpc']; simp only [arm64_norm],
    hc',
    (CalleeSaved.x19 hcs).trans hx.x19_eq,
    (CalleeSaved.x21 hcs).trans (by rw [hmin]; exact hx.x21_eq),
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans (by rw [hmin]; exact hx.x23_eq),
    (CalleeSaved.x24 hcs).trans hx.x24_eq,
    (CalleeSaved.x26 hcs).trans (by rw [hmin]; exact hx.x26_eq),
    (CalleeSaved.x28 hcs).trans hx.x28_eq,
    ht, hokm'⟩⟩

theorem iter_d_continue_96_placed_runsTo_sat {prk info tPrev okmSoFar tNext : List (BitVec 8)}
    {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (htNext : tNext = hmacWith C.F prk (tPrev ++ info ++ [2#8]))
    (hx : StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar 96 1 64 32 s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoop expPlacedFakeB 96 tNext (okmSoFar ++ tNext) 2 32 64 s₀) := by
  have ht_208 : s.mem.readBytes (esp s₀ + 208#64) 32 = tNext := htNext ▸ hx.t_208
  have ht_len : tNext.length = 32 := by rw [htNext, length_hmacWith]
  clear htNext
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq
  have hx23 : s.readReg64 .x23 = 32#64 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 : s.readReg64 .x26 = 32#64 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrd_208 : s.mem.Readable (esp s₀ + 208#64) 32 :=
    readable_of_rw (hrw_esp.sub (by bv_omega))
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) 96 := hpre.rw_x2_frame hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2 + 32#64) 32 := hrw_x2.sub (by bv_omega)
  have hdisj_dst : 32 = 0 ∨ DisjointRegions (s₀.readReg64 .x2 + 32#64) 32 (esp s₀ + 208#64) 32 :=
    Or.inr ((hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + 32#64) ⟨by decide, by bv_omega⟩).sub_right
      (esp s₀ + 208#64) ⟨by decide, by unfold esp; bv_omega⟩)
  iterate 4 s2_step
  refine s2_memcpy_step_placed_of_exact H hH.memcpy
    hrun (by simpa [State.spAligned, arm64_norm, hsp] using hesp)
    rfl rfl rfl rfl rfl ht_208 hrw_dst hrd_208 hdisj_dst fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2 + 32#64) tNext
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + 32#64) 32 :=
    agreesOutside_writeBytes_le s.mem _ tNext 32 (by omega)
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    hpre.common_of_agreesOutside_x2 hx.common hrun hsp hx29 hx27 hx20 hA1 ⟨by decide, by decide⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := hpre.rw_esp hc1.frame
  dsimp only [m₁] at hm16_1 hrw1_esp
  iterate 6 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx24],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_⟩
  · simp only [mem_setMem]
    have ht_m1 : m₁.readBytes (esp s₀ + 208#64) 32 = tNext := by
      have hd : DisjointRegions (s₀.readReg64 .x2 + 32#64) 32 (esp s₀ + 208#64) 32 :=
        (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + 32#64) ⟨by decide, by bv_omega⟩).sub_right
          (esp s₀ + 208#64) ⟨by decide, by unfold esp; bv_omega⟩
      exact (hA1.readBytes_eq hd (by decide)).trans ht_208
    exact readBytes_32_esp_32_of_208 ht_m1
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
  · have hd2 : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) 64 :=
      (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64)
        ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2) ⟨by decide, by bv_omega⟩
    dsimp only [mem_setMem]
    refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd2 (by prove_agrees_esp) (by decide) ?_
    rw [show (64 : ℕ) = 32 + 32 from rfl, readBytes_add m₁ (s₀.readReg64 .x2) 32 32]
    have hleft : m₁.readBytes (s₀.readReg64 .x2) 32 = okmSoFar := by
      have hd1 : DisjointRegions (s₀.readReg64 .x2 + 32#64) 32 (s₀.readReg64 .x2) 32 := by
        unfold DisjointRegions; bv_omega
      exact (hA1.readBytes_eq hd1 (by decide)).trans hx.okm_pre
    have hright : m₁.readBytes (s₀.readReg64 .x2 + 32#64) 32 = tNext := by
      have h := readBytes_writeBytes_same s.mem (s₀.readReg64 .x2 + 32#64) tNext (by omega)
      rwa [ht_len] at h
    rw [hleft, hright]

theorem iter_d_done_96_placed_runsTo_sat {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hokm : okmSoFar ++ hmacWith C.F prk (tPrev ++ info ++ [3#8]) =
              hkdfExpand C.F prk info 96)
    (hx : StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar 96 2 32 64 s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateDone expPlacedFakeB C.F prk info 96 s₀) := by
  generalize htNext : hmacWith C.F prk (tPrev ++ info ++ [3#8]) = tNext
  have ht_208 : s.mem.readBytes (esp s₀ + 208#64) 32 = tNext := htNext ▸ hx.t_208
  have ht_len : tNext.length = 32 := by rw [← htNext, length_hmacWith]
  rw [htNext] at hokm
  clear htNext
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq
  have hx23 : s.readReg64 .x23 = 32#64 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 : s.readReg64 .x26 = 0#64 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrd_208 : s.mem.Readable (esp s₀ + 208#64) 32 :=
    readable_of_rw (hrw_esp.sub (by bv_omega))
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) 96 := hpre.rw_x2_frame hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2 + 64#64) 32 := hrw_x2.sub (by bv_omega)
  have hdisj_dst : 32 = 0 ∨ DisjointRegions (s₀.readReg64 .x2 + 64#64) 32 (esp s₀ + 208#64) 32 :=
    Or.inr ((hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + 64#64) ⟨by decide, by bv_omega⟩).sub_right
      (esp s₀ + 208#64) ⟨by decide, by unfold esp; bv_omega⟩)
  iterate 4 s2_step
  refine s2_memcpy_step_placed_of_exact H hH.memcpy
    hrun (by simpa [State.spAligned, arm64_norm, hsp] using hesp)
    rfl rfl rfl rfl rfl ht_208 hrw_dst hrd_208 hdisj_dst fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2 + 64#64) tNext
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + 64#64) 32 :=
    agreesOutside_writeBytes_le s.mem _ tNext 32 (by omega)
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    hpre.common_of_agreesOutside_x2 hx.common hrun hsp hx29 hx27 hx20 hA1 ⟨by decide, by decide⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := hpre.rw_esp hc1.frame
  dsimp only [m₁] at hm16_1 hrw1_esp
  iterate 6 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    ?_⟩
  have hd2 : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) 96 :=
    hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64) ⟨by decide, by unfold esp; bv_omega⟩
  dsimp only [mem_setMem]
  refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd2 (by prove_agrees_esp) (by decide) ?_
  rw [show (96 : ℕ) = 64 + 32 from rfl, readBytes_add m₁ (s₀.readReg64 .x2) 64 32]
  have hleft : m₁.readBytes (s₀.readReg64 .x2) 64 = okmSoFar := by
    have hd1 : DisjointRegions (s₀.readReg64 .x2 + 64#64) 32 (s₀.readReg64 .x2) 64 := by
      unfold DisjointRegions; bv_omega
    exact (hA1.readBytes_eq hd1 (by decide)).trans hx.okm_pre
  have hright : m₁.readBytes (s₀.readReg64 .x2 + 64#64) 32 = tNext := by
    have h := readBytes_writeBytes_same s.mem (s₀.readReg64 .x2 + 64#64) tNext (by omega)
    rwa [ht_len] at h
  rw [hleft, hright, hokm]

private theorem epilogue_96_raw_placed_runsTo_sat {prk info : List (BitVec 8)}
    {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hx : StateDone expPlacedFakeB C.F prk info 96 s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s (ExpandPost C.F prk info 96 s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  rcases hx.common.saved with
    ⟨m400, m408, m416, m424, m432, m440, m448, m456, m464, m472, m480, m488⟩
  iterate 8 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl, hrun, ⟨(esp_eq_add s₀).symm, ?_⟩, hx.okm_all, hx.common.frame⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem epilogue_96_placed_runsTo_sat {prk info : List (BitVec 8)}
    {infoPtr : BitVec 64} {s₀ s : State} {m_ref : Memory}
    (hb : ExpandPre96_46Base C.F prk info infoPtr s₀)
    (hf_ref : ExpandFrameS2 96 s₀ m_ref)
    (hx : StateDone expPlacedFakeB C.F prk info 96 (s₀.setMem m_ref) s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s fun sf =>
      sf.pc = s₀.readReg64 .lr ∧
      sf.status = .Running ∧
      CalleeSaved s₀ sf ∧
      sf.mem.readBytes (s₀.readReg64 .x2) 96 = hkdfExpand C.F prk info 96 ∧
      ExpandFrameS2 96 s₀ sf.mem := by
  refine (epilogue_96_raw_placed_runsTo_sat (C := C) (H := H) (hb.at_mem m_ref hf_ref) hx).mono
    fun sf ⟨hpc, hrun, hcs, hokm, hfr⟩ => ?_
  exact ⟨hpc, hrun, ⟨hcs.1, hcs.2⟩, hokm, hf_ref.trans (S2Frame.of_frame hfr)⟩

theorem iter_to_fin_96_placed_runsToE_sat {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {i rem dstOff : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl₀ : LibsignalCodeLoaded lsmpl s₀.mem)
    (hkf : s₀.mem.KeepsFrozen s.mem)
    (hb : ExpandPre96_46Base C.F prk info infoPtr s₀)
    (hf_ref : ExpandFrameS2 96 s₀ m_ref)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoop expPlacedFakeB 96 tPrev okmSoFar i rem dstOff (s₀.setMem m_ref) s) :
    RunsToE ((blkPC_53).rebase (blkPl_53).base H) s fun s' =>
      ∃ m_ref', ExpandFrameS2 96 s₀ m_ref' ∧
        StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar 96 i rem dstOff
          (s₀.setMem m_ref') s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  have hrd_ref : (s₀.setMem m_ref).mem.Readable infoPtr 46 :=
    fun a ha => let ⟨hr, hlf⟩ := hb.read_info a ha; hf_ref.2.2 a hr hlf
  have h16 : RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopC_96Placed C.F prk info tPrev okmSoFar i rem dstOff (s₀.setMem m_ref)) :=
    (iter_a1_96_placed_runsTo_sat (C := C) (H := H) hpre_ref hrem hdst hx).trans fun _ hs1 =>
    (iter_a2_96_placed_runsTo_sat (C := C) (H := H) hpre_ref ht_len hrem hdst hs1).trans fun _ hs2 =>
    (iter_b1_96_placed_runsTo_sat (C := C) (H := H) hpre_ref hrd_ref ht_len hdst hs2).trans fun _ hs3 =>
    (iter_b2_96_placed_runsTo_sat (C := C) (H := H) hpre_ref ht_len hdst hs3).trans fun _ hs4 =>
    (iter_b3_96_placed_runsTo_sat (C := C) (H := H) hpre_ref hrd_ref ht_len hi hdst hs4).trans fun _ hs5 =>
    iter_c_96_placed_runsTo_sat (C := C) (H := H) hpre_ref hrem hdst hs5
  exact RunsToE.trans_full (RunsTo.toE h16) fun s6 hs6 hkf6 _ =>
    RunsTo.toE (iter_fin_96_placed_runsTo_sat (C := C) (H := H)
      (hcl₀.of_keepsFrozen (Memory.KeepsFrozen.trans hkf hkf6)) hb hf_ref ht_len hrem hdst hs6)

/-- Full relocatable `RunsToE` contract for `expand_multi_info` (Block `53`) when `okmLen = 96` and
`info.length = 46` under `[HkdfPlacedHooksSat C.F H]`. -/
theorem expand_multi_info_96_46_placed_runsToE_sat {prk info : List (BitVec 8)}
    {infoPtr : BitVec 64} {s₀ : State}
    (hcl₀ : LibsignalCodeLoaded lsmpl s₀.mem)
    (hb : ExpandPre96_46Base C.F prk info infoPtr s₀) :
    RunsToE ((blkPC_53).rebase (blkPl_53).base H) s₀ fun sf =>
      sf.pc = s₀.readReg64 .lr ∧
      sf.status = .Running ∧
      CalleeSaved s₀ sf ∧
      sf.mem.readBytes (s₀.readReg64 .x2) 96 = hkdfExpand C.F prk info 96 ∧
      ExpandFrameS2 96 s₀ sf.mem := by
  have hs_id : s₀.setMem s₀.mem = s₀ := by cases s₀; rfl
  have hf₀ : ExpandFrameS2 96 s₀ s₀.mem := S2Frame.refl s₀.mem _
  have hpre₀ := hb.at_mem s₀.mem hf₀
  have h04 : RunsToE ((blkPC_53).rebase (blkPl_53).base H) s₀
      (StateX2Placed C.F prk info 96 (s₀.setMem s₀.mem)) := by
    conv => arg 2; rw [← hs_id]
    exact RunsTo.toE ((seg0_96_placed_runsTo_sat (C := C) (H := H) hpre₀).trans fun _ hs1 =>
      (seg1_96_placed_runsTo_sat (C := C) (H := H) hpre₀ hs1).trans fun _ hs2 =>
      (seg2a_96_placed_runsTo_sat (C := C) (H := H) hpre₀ hb.read_info hs2).trans fun _ hs3 =>
      seg2b_96_placed_runsTo_sat (C := C) (H := H) hpre₀ hs3)
  have h_after_fin1 := RunsToE.trans_full h04 fun s4 hs4 hkf4 _ =>
    RunsTo.toE (fin1_96_placed_runsTo_sat (C := C) (H := H) (hcl₀.of_keepsFrozen hkf4) hb hf₀ hs4)
  have h06 := h_after_fin1.trans fun s5 ⟨m1, hf1, hs5⟩ =>
    RunsTo.toE ((seg3_96_placed_runsTo_sat (C := C) (H := H) (hb.at_mem m1 hf1) hs5).mono
      fun s6 hs6 => Exists.intro m1 (And.intro hf1 hs6))
  have hfin2 := RunsToE.trans_full h06 fun s6 ⟨m1, hf1, hs6⟩ hkf6 _ =>
    iter_to_fin_96_placed_runsToE_sat (C := C) (H := H) hcl₀ hkf6 hb hf1
      (t1_length C.F prk info) (Or.inl rfl) (Or.inl rfl) (by decide) hs6
  have h08 := hfin2.trans fun s7 ⟨m2, hf2, hs7⟩ =>
    RunsTo.toE ((iter_d_continue_96_placed_runsTo_sat (C := C) (H := H) (tNext := t2 C.F prk info)
      (hb.at_mem m2 hf2) rfl hs7).mono fun s8 hs8 =>
      Exists.intro m2 (And.intro hf2 hs8))
  have hfin3 := RunsToE.trans_full h08 fun s8 ⟨m2, hf2, hs8⟩ hkf8 _ =>
    iter_to_fin_96_placed_runsToE_sat (C := C) (H := H) hcl₀ hkf8 hb hf2
      (t2_length C.F prk info) (Or.inr rfl) (Or.inr rfl) (by decide) hs8
  refine hfin3.trans fun s9 ⟨m3, hf3, hs9⟩ => ?_
  have hokm96 : (t1 C.F prk info ++ t2 C.F prk info) ++
      hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8]) =
      hkdfExpand C.F prk info 96 := by
    rw [show hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8]) = t3 C.F prk info from rfl,
        hkdfExpand_96_eq]
  exact RunsTo.toE ((iter_d_done_96_placed_runsTo_sat (C := C) (H := H) (hb.at_mem m3 hf3)
    hokm96 hs9).trans fun s10 hs10 =>
    epilogue_96_placed_runsTo_sat (C := C) (H := H) hb hf3 hs10)

end PlacedPartBSat

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLongPlacedSat
