/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat -- proof-setup: allow-public-import
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandBlock1
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandLoop
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegs

/-!
# `HookSat` Relocatable Verification of `expand_multi_info`

Establishes `ExpandMultiInfoPlacedOk` for `GenericHkdf<Hmac<Sha256>>::expand_multi_info`
under `[HkdfPlacedHooksSat C.F H]`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSat

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState hmacWith sha256With)
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement extract_withLsCodeLoaded
   lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_8_eq)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved ExpandMultiInfoPlacedOk
   Frame HmacSt RW RunsTo RunsTo.lsProg_svc TraceEq blkPC_53 blkPl_53 expPlacedFakeB
   expPlacedFakeB_off_0 expandMultiInfoSpec finPlacedFakeB hmacCoreAt isBlock_hmacCoreAt
   length_hmacWith ro_outside_rw_shared_lb)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (ExpandCommon ExpandFrame ExpandPost ExpandPre ExpandSaved StateDone
   StateLoop StateLoopCPlaced StateLoopFin StateX2Placed StateX2r
   esp esp_aligned fin_side_conditions hkdfExpand_64_eq hkdfExpand_80_eq
   t1 t1_length t2 t2_length t3 t3_length)
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsTo.toE RunsToE S2Frame)
open CryptoVerification.LibsignalTripleRatchet.FinalizeFixedProof (FinPre)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsSat
  (epilogue_raw_placed_runsTo_sat iter_a1_placed_runsTo_sat iter_a2_placed_runsTo_sat
   iter_b_placed_runsTo_sat iter_c_placed_runsTo_sat iter_d_continue_placed_runsTo_sat
   iter_d_done_placed_runsTo_sat seg0_placed_runsTo_sat seg1_placed_runsTo_sat
   seg2a_placed_runsTo_sat seg2b_placed_runsTo_sat seg3_placed_runsTo_sat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat
  (FinPostSat finalize_fixed_placed_runsTo_of_other_block_sat)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

/-! ## `S2Frame` and Ghost-State Reset Helpers -/

@[local simp]
private theorem esp_setMem (s₀ : State) (m : Memory) : esp (s₀.setMem m) = esp s₀ := rfl

abbrev ExpandFrameS2 (okmLen : ℕ) (s₀ : State) (m : Memory) : Prop :=
  S2Frame s₀.mem m [(s₀.readReg64 .x2, okmLen), (s₀.sp - 640#64, 640)]

private structure ExpandPreBase [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (okmLen : ℕ) (s₀ : State) : Prop where
  pre       : ExpandPre expPlacedFakeB F prk info infoPtr okmLen s₀
  read_info : s₀.mem.Readable infoPtr info.length

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

private theorem ExpandPreBase.at_mem [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hb : ExpandPreBase F prk info infoPtr okmLen s₀)
    (m : Memory) (hf : ExpandFrameS2 okmLen s₀ m) :
    ExpandPre expPlacedFakeB F prk info infoPtr okmLen (s₀.setMem m) := by
  have hout_pair {p : BitVec 64} {n : ℕ}
      (ho_x2 : ∀ a, InRegion p n a → OutsideRegion (s₀.readReg64 .x2) okmLen a)
      (ho_stk : ∀ a, InRegion p n a → OutsideRegion (s₀.sp - 640#64) 640 a) :
      ∀ a, InRegion p n a →
        ∀ r ∈ [(s₀.readReg64 .x2, okmLen), (s₀.sp - 640#64, 640)], OutsideRegion r.1 r.2 a := by
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
    · have ha : InRegion (s₀.readReg64 .x0) 0x90 (s₀.readReg64 .x0 + 0x3f#64) := by
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
      info_lt       := hb.pre.info_lt
      okm_len       := hb.pre.okm_len
      hmac_st       := hhmac_m
      info_ptr      := show m.read64 (s₀.readReg64 .x1) = infoPtr from
        (s2_read64_eq_of_readable hf
          (readable_sub hb.pre.read_x1 (fun a ha => by unfold InRegion at ha ⊢; bv_omega))
          (fun a ha => hout_x1 a (by unfold InRegion at ha ⊢; bv_omega))).trans hb.pre.info_ptr
      info_len      := show m.read64 (s₀.readReg64 .x1 + 8#64) = BitVec.ofNat 64 info.length from
        (s2_read64_eq_of_readable hf
          (readable_sub hb.pre.read_x1 (fun a ha => by unfold InRegion at ha ⊢; bv_omega))
          (fun a ha => hout_x1 a (by unfold InRegion at ha ⊢; bv_omega))).trans hb.pre.info_len
      info_bytes    := (s2_readBytes_eq_of_readable hf (by have := hb.pre.info_lt; omega)
        hb.read_info (hout_pair hb.pre.out_info_x2 hb.pre.out_info_stk)).trans hb.pre.info_bytes
      read_x0       := fun a ha => let ⟨hr, hlf⟩ := hb.pre.read_x0 a ha; hf.2.2 a hr hlf
      read_x1       := fun a ha => let ⟨hr, hlf⟩ := hb.pre.read_x1 a ha; hf.2.2 a hr hlf
      rw_x2         := hf.rw_of_rw (s₀.readReg64 .x2) okmLen hb.pre.rw_x2
      rw_stack      := hf.rw_of_rw (s₀.sp - 640#64) 640 hb.pre.rw_stack
      disj_x2_stack := hb.pre.disj_x2_stack
      disj_x0_stack := hb.pre.disj_x0_stack
      disj_x0_x2    := hb.pre.disj_x0_x2
      disj_x1_stack := hb.pre.disj_x1_stack
      disj_x1_x2    := hb.pre.disj_x1_x2
      out_info_stk  := hb.pre.out_info_stk
      out_info_x2   := hb.pre.out_info_x2
      sp_aligned    := hb.pre.sp_aligned }

private theorem expandCommon_reset_of_fin [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {prk info : List (BitVec 8)}
    {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s s' : State} {m_ref : Memory}
    (hb : ExpandPreBase F prk info infoPtr okmLen s₀)
    (hf_ref : ExpandFrameS2 okmLen s₀ m_ref)
    (hc : ExpandCommon okmLen (s₀.setMem m_ref) s)
    (hstat : s'.status = .Running)
    (hcs : CalleeSaved s s')
    (hfr : S2Frame s.mem s'.mem [(esp s₀ + 208#64, 32), (esp s₀ + 240#64, 0x90), (esp s₀ - 144#64, 144)]) :
    ExpandFrameS2 okmLen s₀ s'.mem ∧ ExpandCommon okmLen (s₀.setMem s'.mem) s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  have hrw_esp : s.mem.RW (esp s₀) 496 :=
    ExpandFrame.rw_esp (s₀ := s₀.setMem m_ref) hpre_ref hc.frame
  have hf_s : ExpandFrameS2 okmLen s₀ s.mem := hf_ref.trans (S2Frame.of_frame hc.frame)
  have hf_s' : ExpandFrameS2 okmLen s₀ s'.mem := by
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

/-! ## `finalize_fixed` Call Glue and Assembly -/

section PlacedSat

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksExactSat C.F H]

private theorem fin1_placed_runsTo_sat {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : ExpandPreBase C.F prk info infoPtr okmLen s₀)
    (hf_ref : ExpandFrameS2 okmLen s₀ m_ref)
    (hx : StateX2Placed C.F prk info okmLen (s₀.setMem m_ref) s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s fun s' =>
      ∃ m_ref', ExpandFrameS2 okmLen s₀ m_ref' ∧
        StateX2r expPlacedFakeB C.F prk info okmLen (s₀.setMem m_ref') s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  rcases fin_side_conditions (s₀ := s₀.setMem m_ref) hpre_ref hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hfin_pre : FinPre finPlacedFakeB C.F prk (info ++ [1#8]) s :=
    { pc_eq := by rw [CryptoVerification.LibsignalTripleRatchet.finPlacedFakeB_off_0]; exact hx.pc_eq
      status := hx.common.status
      key_le := hb.pre.prk_le
      msg_lt := by have := hb.pre.info_lt; simp; omega
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
  obtain ⟨hf_s', hc'⟩ := expandCommon_reset_of_fin hb hf_ref hx.common hrun' hcs hfr
  exact ⟨s'.mem, hf_s', ⟨by rw [hpc']; simp only [arm64_norm], hc',
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans hx.x23_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq,
    ht1⟩⟩

private theorem iter_fin_placed_runsTo_sat {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : ExpandPreBase C.F prk info infoPtr okmLen s₀)
    (hf_ref : ExpandFrameS2 okmLen s₀ m_ref)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopCPlaced C.F prk info tPrev okmSoFar okmLen i rem dstOff (s₀.setMem m_ref) s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s fun s' =>
      ∃ m_ref', ExpandFrameS2 okmLen s₀ m_ref' ∧
        StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar okmLen i rem dstOff
          (s₀.setMem m_ref') s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  rcases fin_side_conditions (s₀ := s₀.setMem m_ref) hpre_ref hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) okmLen :=
    ExpandFrame.rw_x2 (s₀ := s₀.setMem m_ref) hpre_ref hx.common.frame
  have hfin_pre : FinPre finPlacedFakeB C.F prk
      (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) s :=
    { pc_eq := by rw [CryptoVerification.LibsignalTripleRatchet.finPlacedFakeB_off_0]; exact hx.pc_eq
      status := hx.common.status
      key_le := hb.pre.prk_le
      msg_lt := by have := hb.pre.info_lt; simp [ht_len]; omega
      hmac_st := by rw [hx.x1_eq, esp_setMem]; exact hx.hmac_240
      rw_out := by rw [hx.x0_eq]; exact hrw_x0
      rw_hm := by rw [hx.x1_eq]; exact hrw_x1
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sp
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; exact hd_x0_x1
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; exact hd_x0_sp
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; exact hd_x1_sp
      sp_aligned := by rw [hx.common.sp_eq, esp_setMem]; exact esp_aligned hb.pre.sp_aligned }
  refine (finalize_fixed_placed_runsTo_of_other_block_sat (C := C) (H := H)
    hcl hfin_pre).mono fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'
  rw [hx.x0_eq, esp_setMem] at hout
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq, esp_setMem] at hfr
  have hokm' : s'.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hokm_len := hb.pre.okm_len
      refine (hfr.readBytes_eq (hrw_x2.sub (by bv_omega)) (fun r hr => ?_) (by omega)).trans hx.okm_pre
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · exact (hb.pre.disj_x2_stack.symm.sub_left (esp s₀ + 208#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      · exact (hb.pre.disj_x2_stack.symm.sub_left (esp s₀ + 240#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      · exact (hb.pre.disj_x2_stack.symm.sub_left (esp s₀ - 144#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
  obtain ⟨hf_s', hc'⟩ := expandCommon_reset_of_fin hb hf_ref hx.common hrun' hcs hfr
  exact ⟨s'.mem, hf_s', ⟨by rw [hpc']; simp only [arm64_norm], hc',
    (CalleeSaved.x19 hcs).trans hx.x19_eq,
    (CalleeSaved.x21 hcs).trans hx.x21_eq,
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans hx.x23_eq,
    (CalleeSaved.x24 hcs).trans hx.x24_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq,
    (CalleeSaved.x28 hcs).trans hx.x28_eq,
    hout, hokm'⟩⟩

private theorem iter_to_fin_placed_runsToE_sat {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl₀ : LibsignalCodeLoaded lsmpl s₀.mem)
    (hkf : s₀.mem.KeepsFrozen s.mem)
    (hb : ExpandPreBase C.F prk info infoPtr okmLen s₀)
    (hf_ref : ExpandFrameS2 okmLen s₀ m_ref)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 32 ∨ rem = 48 ∨ rem = 16)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoop expPlacedFakeB okmLen tPrev okmSoFar i rem dstOff (s₀.setMem m_ref) s) :
    RunsToE ((blkPC_53).rebase (blkPl_53).base H) s fun s' =>
      ∃ m_ref', ExpandFrameS2 okmLen s₀ m_ref' ∧
        StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar okmLen i rem dstOff
          (s₀.setMem m_ref') s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  have hrd_ref : (s₀.setMem m_ref).mem.Readable infoPtr info.length :=
    fun a ha => let ⟨hr, hlf⟩ := hb.read_info a ha; hf_ref.2.2 a hr hlf
  have h_pre : RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopCPlaced C.F prk info tPrev okmSoFar okmLen i rem dstOff (s₀.setMem m_ref)) :=
    (iter_a1_placed_runsTo_sat (C := C) (H := H) hpre_ref hrem hdst hx).trans fun s1 hs1 =>
      (iter_a2_placed_runsTo_sat (C := C) (H := H) hpre_ref ht_len hdst hs1).trans fun s2 hs2 =>
      (iter_b_placed_runsTo_sat (C := C) (H := H) hpre_ref hrd_ref ht_len hi hdst hs2).trans fun s3 hs3 =>
      iter_c_placed_runsTo_sat (C := C) (H := H) hpre_ref hrem hdst hs3
  exact RunsToE.trans_full (RunsTo.toE h_pre) fun sc hsc hkf_c _ =>
    RunsTo.toE (iter_fin_placed_runsTo_sat (C := C) (H := H)
      (hcl₀.of_keepsFrozen (Memory.KeepsFrozen.trans hkf hkf_c)) hb hf_ref ht_len hdst hsc)

private theorem epilogue_placed_runsTo_sat {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen : ℕ} {s₀ s : State} {m_ref : Memory}
    (hb : ExpandPreBase C.F prk info infoPtr okmLen s₀)
    (hf_ref : ExpandFrameS2 okmLen s₀ m_ref)
    (hx : StateDone expPlacedFakeB C.F prk info okmLen (s₀.setMem m_ref) s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s fun sf =>
      sf.pc = s₀.readReg64 .lr ∧
      sf.status = .Running ∧
      CalleeSaved s₀ sf ∧
      sf.mem.readBytes (s₀.readReg64 .x2) okmLen = hkdfExpand C.F prk info okmLen ∧
      ExpandFrameS2 okmLen s₀ sf.mem := by
  refine (epilogue_raw_placed_runsTo_sat (C := C) (H := H) (hb.at_mem m_ref hf_ref) hx).mono
    fun sf ⟨hpc, hrun, hcs, hokm, hfr⟩ => ?_
  exact ⟨hpc, hrun, ⟨hcs.1, hcs.2⟩, hokm, hf_ref.trans (S2Frame.of_frame hfr)⟩

private theorem expand_multi_info_placed_runsToE_sat {prk info : List (BitVec 8)}
    {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hcl₀ : LibsignalCodeLoaded lsmpl s₀.mem)
    (hb : ExpandPreBase C.F prk info infoPtr okmLen s₀) :
    RunsToE ((blkPC_53).rebase (blkPl_53).base H) s₀ fun sf =>
      sf.pc = s₀.readReg64 .lr ∧
      sf.status = .Running ∧
      CalleeSaved s₀ sf ∧
      sf.mem.readBytes (s₀.readReg64 .x2) okmLen = hkdfExpand C.F prk info okmLen ∧
      ExpandFrameS2 okmLen s₀ sf.mem := by
  have hs_id : s₀.setMem s₀.mem = s₀ := by cases s₀; rfl
  have hf₀ : ExpandFrameS2 okmLen s₀ s₀.mem := S2Frame.refl s₀.mem _
  have hpre₀ := hb.at_mem s₀.mem hf₀
  have h_to_fin1 : RunsToE ((blkPC_53).rebase (blkPl_53).base H) s₀
      (StateX2Placed C.F prk info okmLen (s₀.setMem s₀.mem)) := by
    conv => arg 2; rw [← hs_id]
    exact RunsTo.toE ((seg0_placed_runsTo_sat (C := C) (H := H) hpre₀).trans fun s1 hs1 =>
      (seg1_placed_runsTo_sat (C := C) (H := H) hpre₀ hs1).trans fun s2 hs2 =>
      (seg2a_placed_runsTo_sat (C := C) (H := H) hpre₀ hb.read_info hs2).trans fun s3 hs3 =>
      seg2b_placed_runsTo_sat (C := C) (H := H) hpre₀ hs3)
  have h_after_fin1 := RunsToE.trans_full h_to_fin1 fun s4 hs4 hkf4 _ =>
    RunsTo.toE (fin1_placed_runsTo_sat (C := C) (H := H) (hcl₀.of_keepsFrozen hkf4) hb hf₀ hs4)
  have h_loop := h_after_fin1.trans fun s5 ⟨m1, hf1, hs5⟩ =>
    RunsTo.toE ((seg3_placed_runsTo_sat (C := C) (H := H) (hb.at_mem m1 hf1) hs5).mono
      fun s6 hs6 => Exists.intro m1 (And.intro hf1 hs6))
  refine RunsToE.trans_full h_loop fun s6 ⟨m1, hf1, hs6⟩ hkf6 _ => ?_
  rcases hb.pre.okm_len with rfl | rfl
  · have hfin2 := iter_to_fin_placed_runsToE_sat (C := C) (H := H) hcl₀ hkf6 hb hf1
      (t1_length C.F prk info) (Or.inl rfl) (Or.inl rfl) (by decide) hs6
    refine hfin2.trans fun s7 ⟨m2, hf2, hs7⟩ => ?_
    have hokm64 : t1 C.F prk info ++ (hmacWith C.F prk (t1 C.F prk info ++ info ++ [2#8])).take 32 =
        hkdfExpand C.F prk info 64 := by
      rw [show hmacWith C.F prk (t1 C.F prk info ++ info ++ [2#8]) = t2 C.F prk info from rfl,
          List.take_of_length_le (by rw [t2_length]), hkdfExpand_64_eq]
    exact RunsTo.toE ((iter_d_done_placed_runsTo_sat (C := C) (H := H) (hb.at_mem m2 hf2)
      (Or.inl rfl) (Or.inl rfl) rfl hokm64 hs7).trans fun s8 hs8 =>
      epilogue_placed_runsTo_sat (C := C) (H := H) hb hf2 hs8)
  · have hfin2 := iter_to_fin_placed_runsToE_sat (C := C) (H := H) hcl₀ hkf6 hb hf1
      (t1_length C.F prk info) (Or.inl rfl) (Or.inr (Or.inl rfl)) (by decide) hs6
    have hloop3 := hfin2.trans fun s7 ⟨m2, hf2, hs7⟩ =>
      RunsTo.toE ((iter_d_continue_placed_runsTo_sat (C := C) (H := H) (tNext := t2 C.F prk info)
        (hb.at_mem m2 hf2) rfl (by decide) rfl hs7).mono fun s8 hs8 =>
        Exists.intro m2 (And.intro hf2 hs8))
    have hfin3 := RunsToE.trans_full hloop3 fun s8 ⟨m2, hf2, hs8⟩ hkf8 _ =>
      iter_to_fin_placed_runsToE_sat (C := C) (H := H) hcl₀ (Memory.KeepsFrozen.trans hkf6 hkf8) hb hf2
        (t2_length C.F prk info) (Or.inr rfl) (Or.inr (Or.inr rfl)) (by decide) hs8
    refine hfin3.trans fun s9 ⟨m3, hf3, hs9⟩ => ?_
    have hokm80 : (t1 C.F prk info ++ t2 C.F prk info) ++
        (hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8])).take 16 =
        hkdfExpand C.F prk info 80 := by
      rw [show hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8]) = t3 C.F prk info from rfl,
          hkdfExpand_80_eq]
    exact RunsTo.toE ((iter_d_done_placed_runsTo_sat (C := C) (H := H) (hb.at_mem m3 hf3)
      (Or.inr rfl) (Or.inr rfl) rfl hokm80 hs9).trans fun s10 hs10 =>
      epilogue_placed_runsTo_sat (C := C) (H := H) hb hf3 hs10)

end PlacedSat

/-! ## Separation-Logic Contract -/

theorem expand_multi_info_placed_ok_sat [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooksExactSat C.F H] :
    ExpandMultiInfoPlacedOk C H := by
  unfold ExpandMultiInfoPlacedOk
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre_cl hsp => ?_
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre_cl
  dsimp only [expandMultiInfoSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, hokm_len⟩, hsep⟩
  change s0.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ memRegion x.okmA x.okmLen ∗
      memRegion (s0.sp - 640#64) 640) ∗ R at hsep
  have hb_hm := isBlock_hmacCoreAt C.F x.hkdfA x.prk [] (by decide)
  have hb_hdr0 := IsBlock.pointsTo64 x.infoHdrA x.infoA
  have hb_hdr8 := IsBlock.pointsTo64 (x.infoHdrA + 8#64) (BitVec.ofNat 64 x.info.length)
  have hb_hdr : IsBlock ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length))
      x.infoHdrA 16
      (fun m => m.read64 x.infoHdrA = x.infoA ∧
        m.read64 (x.infoHdrA + 8#64) = BitVec.ofNat 64 x.info.length) :=
    hb_hdr0.sepConj hb_hdr8 rfl (by decide)
  have hro_info := IsBlockRO.pointsToBytesRO x.infoA x.info (by omega)
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (s0.sp - 640#64) 640
  let R_inv : SepProp :=
    hmacCoreAt C.F x.hkdfA x.prk [] ∗
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (x.infoA ↦ᵣ x.info) ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA x.okmLen ∗ (memRegion (s0.sp - 640#64) 640 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 640#64) 640 ∗ (memRegion x.okmA x.okmLen ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_hm_stk : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hm_okm : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion x.okmA x.okmLen ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_stk : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_okm : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (memRegion x.okmA x.okmLen ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
            (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion x.okmA x.okmLen ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
            (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hokm_pos : 0 < x.okmLen := by omega
  have h_exp_pre : ExpandPre expPlacedFakeB C.F x.prk x.info x.infoA x.okmLen s0 :=
    { pc_eq := by rw [expPlacedFakeB_off_0]; exact hpc
      status := hrun
      x3_eq := hx3
      prk_le := hprk_le
      info_lt := hinfo_lt
      okm_len := hokm_len
      hmac_st := by rw [hx0]; exact hb_hm.read hsep_hm_stk
      info_ptr := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).1
      info_len := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).2
      info_bytes := hro_info.read hsep_info_stk
      read_x0 := by rw [hx0]; exact Memory.RW.readable (fun a ha => hb_hm.permNoLazy_rw hsep_hm_stk ha)
      read_x1 := by rw [hx1]; exact Memory.RW.readable (fun a ha => hb_hdr.permNoLazy_rw hsep_hdr_stk ha)
      rw_x2 := by rw [hx2]; exact fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
      rw_stack := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
      disj_x2_stack := by rw [hx2]; exact hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk
      disj_x0_stack := by rw [hx0]; exact hb_hm.disjoint hb_stk (by decide) (by decide) hsep_hm_stk
      disj_x0_x2 := by rw [hx0, hx2]; exact hb_hm.disjoint hb_okm (by decide) hokm_pos hsep_hm_okm
      disj_x1_stack := by rw [hx1]; exact hb_hdr.disjoint hb_stk (by decide) (by decide) hsep_hdr_stk
      disj_x1_x2 := by rw [hx1, hx2]; exact hb_hdr.disjoint hb_okm (by decide) hokm_pos hsep_hdr_okm
      out_info_stk := ro_outside_rw_shared_lb hro_info hb_stk hsep_info_stk
      out_info_x2 := by rw [hx2]; exact ro_outside_rw_shared_lb hro_info hb_okm hsep_info_okm
      sp_aligned := by simpa [State.spAligned] using hsp }
  have hb_base : ExpandPreBase C.F x.prk x.info x.infoA x.okmLen s0 :=
    { pre := h_exp_pre
      read_info := fun a ha => ⟨hro_info.perm_r hsep_info_stk ha, hro_info.isLazyFree_false hsep_info_stk ha⟩ }
  refine (expand_multi_info_placed_runsToE_sat (C := C) (H := H) hcl hb_base).to_reaches_pc
    fun sf hpost hkf_sf _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [withLsCodeLoaded, expandMultiInfoSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExpandFrameS2 at hframe_sf
  rw [hx2] at hokm_sf hframe_sf
  have h_exp_len : (hkdfExpand C.F x.prk x.info x.okmLen).length = x.okmLen := by
    rcases hokm_len with h64 | h80
    · rw [h64, hkdfExpand_64_eq]
      simp [t1_length, t2_length]
    · rw [h80, hkdfExpand_80_eq]
      simp [t1_length, t2_length, t3_length]
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info x.okmLen) ∗
      (memRegion (s0.sp - 640#64) 640 ∗ R_inv) :=
    S2Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  change sf.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info x.okmLen) ∗
      memRegion (s0.sp - 640#64) 640) ∗ R
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

end LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSat
